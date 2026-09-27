import COF.SharedMemory.Algorithm
import COF.SharedMemory.Implementation
import Mathlib.Data.List.Nodup

/-!
# The single-shot client of an implementation

Corollary 7 rests on the remark that a COF universal construction "in particular implements COF
consensus": run its implementation of the consensus object with every process proposing once.
This file sets that up for any implementation `I` of a binary object (operations `Bool`,
responses `Bool`).

`singleShot I` is the *client*: an `Algorithm` of the consensus model in which every process,
at its first step, invokes the operation named by its input, then runs `I` until the operation
returns, and decides the response. After that, its steps are reads that change nothing.

`embed_step` shows that the client is `I`, step for step: each step of the client performs one
action of `I` (`actionOf`), from the configuration of `I` that the client configuration stands
for (`embed`). The invariants `ClientInv` and `HistoryInv` describe every reachable client
configuration and the history of `I` it has produced. `COF/Universal/Transfer.lean` uses them to
carry linearizability and COF over from `I` to the client.
-/

namespace COF.SharedMemory.Implementation
open Function

variable {P R V S : Type*} (I : Implementation P R V S Bool Bool)

/-! ## The client -/

/-- The local state of a client process: its state as a process of `I`, and its input. -/
abbrev ClientState (S : Type*) := ProcState S Bool × Bool

/-- The single-shot client of `I`, as an algorithm of the consensus model. -/
def singleShot : Algorithm P R V (ClientState S) where
  initialMemory := I.initialMemory
  initialState p b := (⟨I.initialState p, none, 0⟩, b)
  instruction p x :=
    match x.1.pending with
    | some o =>
      match I.instruction p x.1.state with
      | .read r next => .read r fun v => ⟨(x.1.after o (next v).1 (next v).2, x.2), (next v).2⟩
      | .write r v next => .write r v ⟨(x.1.after o next.1 next.2, x.2), next.2⟩
    | none =>
      .read (I.instruction p x.1.state).register fun _ =>
        ⟨if x.1.done = 0 then (⟨I.invoke p x.2 x.1.state, some x.2, 0⟩, x.2) else x, none⟩

/-- The action of `I` that a step of client process `p`, in local state `x`, performs: the
invocation of its operation, a step of that operation, or a step while idle. -/
def actionOf (p : P) (x : ClientState S) : Action P Bool :=
  match x.1.pending with
  | some _ => .step p
  | none => if x.1.done = 0 then .invoke p x.2 else .step p

/-- The configuration of `I` that a client configuration stands for. -/
def embed (c : Config P R V (ClientState S)) : ImplConfig P R V S Bool :=
  ⟨c.memory, fun p => (c.proc p).state.1⟩

/-- The actions of `I` that a finite run `ps` of the client from `c` performs. -/
noncomputable def actions (I : Implementation P R V S Bool Bool)
    (c : Config P R V (ClientState S)) : List P → List (Action P Bool)
  | [] => []
  | p :: ps => actionOf p (c.proc p).state :: actions I (I.singleShot.step c p) ps

/-- The actions of `I` that the client's infinite execution from `c` under `σ` performs. -/
noncomputable def infActions (c : Config P R V (ClientState S)) (σ : ℕ → P) :
    ℕ → Action P Bool :=
  fun m => actionOf (σ m) ((I.singleShot.execution c σ m).proc (σ m)).state

/-- The client process in local state `x` has invoked its operation. -/
def Invoked (x : ClientState S) : Prop := x.1.pending.isSome ∨ x.1.done ≠ 0

/-- The client invariant for the input vector `input`. Each process remembers its input and is in
one of three phases: it has not invoked yet; it is executing the operation its input names; or
its operation has returned, which is exactly when it has decided. -/
def ClientInv (input : P → Bool) (c : Config P R V (ClientState S)) : Prop :=
  ∀ p, (c.proc p).state.2 = input p ∧
    (((c.proc p).state.1.pending = none ∧ (c.proc p).state.1.done = 0 ∧
        (c.proc p).decision = none) ∨
      ((c.proc p).state.1.pending = some (input p) ∧ (c.proc p).state.1.done = 0 ∧
        (c.proc p).decision = none) ∨
      ((c.proc p).state.1.pending = none ∧ (c.proc p).state.1.done = 1 ∧
        (c.proc p).decision.isSome))

/-- The history produced so far: one instance per process that has invoked, of the operation its
input names, which has returned exactly when the process has decided, with its decision as the
response. -/
def HistoryInv (input : P → Bool) (c : Config P R V (ClientState S))
    (H : History P Bool Bool) : Prop :=
  (H.map OpRecord.proc).Nodup ∧
    (∀ a ∈ H, a.op = input a.proc ∧ a.returned.map Prod.fst = (c.proc a.proc).decision ∧
      Invoked (c.proc a.proc).state) ∧
    ∀ p, Invoked (c.proc p).state → ∃ a ∈ H, a.proc = p

variable {I}

/-! ## The client is the implementation, step for step -/

@[simp] theorem embed_memory (c : Config P R V (ClientState S)) : (embed c).memory = c.memory :=
  rfl

@[simp] theorem embed_proc (c : Config P R V (ClientState S)) (p : P) :
    (embed c).proc p = (c.proc p).state.1 := rfl

/-- The client starts where `I` does. -/
theorem embed_initial (input : P → Bool) : embed (I.singleShot.initial input) = I.initial := rfl

open scoped Classical in
theorem embed_update (c : Config P R V (ClientState S)) (m : R → V) (p : P)
    (l : Local (ClientState S)) :
    embed ⟨m, update c.proc p l⟩ = ⟨m, update (embed c).proc p l.state.1⟩ := by
  apply ImplConfig.ext
  · rfl
  · funext q
    by_cases hq : q = p
    · subst hq; simp [embed]
    · simp [embed, update_of_ne hq]

open scoped Classical in
/-- A step of a client process with a pending operation is a step of that operation in `I`. -/
theorem step_of_pending (c : Config P R V (ClientState S)) (p : P) {o : Bool}
    (h : (c.proc p).state.1.pending = some o) :
    I.singleShot.step c p =
      ⟨(I.stepResult (embed c) p o).1, update c.proc p
        ⟨((I.stepResult (embed c) p o).2.1, (c.proc p).state.2),
          (c.proc p).decision.or (I.stepResult (embed c) p o).2.2⟩⟩ := by
  simp only [Algorithm.step, singleShot, h, stepResult, embed_proc, embed_memory]
  cases I.instruction p (c.proc p).state.1.state <;> rfl

open scoped Classical in
/-- A client process that has not invoked yet invokes the operation its input names. -/
theorem step_of_fresh (c : Config P R V (ClientState S)) (p : P)
    (h : (c.proc p).state.1.pending = none) (h0 : (c.proc p).state.1.done = 0) :
    I.singleShot.step c p =
      ⟨c.memory, update c.proc p
        ⟨(⟨I.invoke p (c.proc p).state.2 (c.proc p).state.1.state,
            some (c.proc p).state.2, 0⟩, (c.proc p).state.2), (c.proc p).decision⟩⟩ := by
  simp only [Algorithm.step, singleShot, h, h0, ite_true, Option.or_none]

/-- A client process whose operation has returned is idle: its steps change nothing. -/
theorem step_of_returned (c : Config P R V (ClientState S)) (p : P)
    (h : (c.proc p).state.1.pending = none) (h0 : (c.proc p).state.1.done ≠ 0) :
    I.singleShot.step c p = c := by
  classical
  simp only [Algorithm.step, singleShot, h, h0, ite_false, Option.or_none]
  apply Config.ext
  · rfl
  · funext q
    by_cases hq : q = p
    · subst hq
      simp
    · simp [update_of_ne hq]

/-- **The simulation.** Each step of the client performs one action of `I`, from the
corresponding configuration. -/
theorem embed_step (c : Config P R V (ClientState S)) (p : P) :
    embed (I.singleShot.step c p) = I.act (embed c) (actionOf p (c.proc p).state) := by
  cases hp : (c.proc p).state.1.pending with
  | some o =>
    rw [step_of_pending c p hp, embed_update]
    simp [actionOf, act, hp]
  | none =>
    by_cases h0 : (c.proc p).state.1.done = 0
    · rw [step_of_fresh c p hp h0, embed_update]
      simp [actionOf, act, hp, h0]
    · rw [step_of_returned c p hp h0]
      simp [actionOf, act, hp, h0]

/-- The client's infinite executions are executions of `I`. -/
theorem embed_execution (c : Config P R V (ClientState S)) (σ : ℕ → P) (k : ℕ) :
    embed (I.singleShot.execution c σ k) = I.execution (embed c) (I.infActions c σ) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Algorithm.execution_succ, execution_succ, embed_step, ih]
    rfl

/-- In particular, from an initial configuration of the client. -/
theorem execution_infActions (input : P → Bool) (σ : ℕ → P) (k : ℕ) :
    I.execution I.initial (I.infActions (I.singleShot.initial input) σ) k =
      embed (I.singleShot.execution (I.singleShot.initial input) σ k) := by
  rw [embed_execution, embed_initial]

/-- The events that client steps contribute to the history of `I`. -/
theorem event_of_pending (c : Config P R V (ClientState S)) (p : P) {o : Bool}
    (h : (c.proc p).state.1.pending = some o) :
    I.event (embed c) (actionOf p (c.proc p).state) =
      (I.stepResult (embed c) p o).2.2.map (.res p) := by
  simp [actionOf, event, h]

theorem event_of_fresh (c : Config P R V (ClientState S)) (p : P)
    (h : (c.proc p).state.1.pending = none) (h0 : (c.proc p).state.1.done = 0) :
    I.event (embed c) (actionOf p (c.proc p).state) = some (.inv p (c.proc p).state.2) := by
  simp [actionOf, event, h, h0]

theorem event_of_returned (c : Config P R V (ClientState S)) (p : P)
    (h : (c.proc p).state.1.pending = none) (h0 : (c.proc p).state.1.done ≠ 0) :
    I.event (embed c) (actionOf p (c.proc p).state) = none := by
  simp [actionOf, event, h, h0]

/-! ## The invariants -/

theorem clientInv_initial (input : P → Bool) : ClientInv input (I.singleShot.initial input) := by
  intro p
  simp [Algorithm.initial, singleShot]

theorem clientInv_step {input : P → Bool} {c : Config P R V (ClientState S)}
    (h : ClientInv input c) (q : P) : ClientInv input (I.singleShot.step c q) := by
  intro p
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨hin, hph⟩ := h p
    rcases hph with ⟨hp, h0, hd⟩ | ⟨hp, h0, hd⟩ | ⟨hp, h1, hd⟩
    · rw [step_of_fresh c p hp h0]
      simp [hin, hd]
    · obtain ⟨s, hs⟩ := I.stepResult_after (embed c) p (input p)
      rw [step_of_pending c p hp]
      simp only [update_self, hs, embed_proc]
      cases (I.stepResult (embed c) p (input p)).2.2 <;>
        simp [ProcState.after, hin, h0, hd]
    · rw [step_of_returned c p hp (by omega)]
      exact h p
  · rw [Algorithm.step_local_other _ _ hpq]
    exact h p

theorem clientInv_run {input : P → Bool} :
    ∀ (ps : List P) {c : Config P R V (ClientState S)}, ClientInv input c →
      ClientInv input (I.singleShot.run c ps)
  | [], _, h => h
  | q :: qs, _, h => clientInv_run qs (clientInv_step h q)

theorem clientInv_execution {input : P → Bool} {c : Config P R V (ClientState S)}
    (h : ClientInv input c) (σ : ℕ → P) :
    ∀ k, ClientInv input (I.singleShot.execution c σ k)
  | 0 => h
  | k + 1 => clientInv_step (clientInv_execution h σ k) (σ k)

variable (I) in
/-- In particular, the invariant holds along every execution from an initial configuration. -/
theorem clientInv_initial_execution (input : P → Bool) (σ : ℕ → P) (k : ℕ) :
    ClientInv input (I.singleShot.execution (I.singleShot.initial input) σ k) :=
  clientInv_execution (clientInv_initial input) σ k

/-- The history invariant survives a step of the client, together with the event it records. -/
theorem historyInv_step {input : P → Bool}
    {c : Config P R V (ClientState S)} {H : History P Bool Bool}
    (hc : ClientInv input c) (hH : HistoryInv input c H) (q : P) (t : ℕ) :
    HistoryInv input (I.singleShot.step c q)
      (H.record t (I.event (embed c) (actionOf q (c.proc q).state))) := by
  classical
  obtain ⟨hnd, hrec, hex⟩ := hH
  obtain ⟨hin, hph⟩ := hc q
  rcases hph with ⟨hp, h0, hd⟩ | ⟨hp, h0, hd⟩ | ⟨hp, h1, hd⟩
  · -- `q` invokes: a new instance, and nobody else changes.
    rw [event_of_fresh c q hp h0, step_of_fresh c q hp h0, hin]
    have hnot : ∀ a ∈ H, a.proc ≠ q := by
      intro a ha hpa
      have hinv := (hrec a ha).2.2
      rw [hpa] at hinv
      simp [Invoked, hp, h0] at hinv
    refine ⟨?_, ?_, ?_⟩
    · simpa [History.record, List.nodup_append] using ⟨hnd, hnot⟩
    · intro a ha
      simp only [History.record, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · obtain ⟨hao, har, hinv⟩ := hrec a ha
        have hq := hnot a ha
        exact ⟨hao, by simpa [update_of_ne hq] using har, by simpa [update_of_ne hq] using hinv⟩
      · exact ⟨rfl, by simp [hd], by simp [Invoked]⟩
    · intro p hpi
      simp only [History.record, List.mem_append, List.mem_singleton]
      by_cases hpq : p = q
      · subst hpq
        exact ⟨_, Or.inr rfl, rfl⟩
      · obtain ⟨a, ha, hpa⟩ := hex p (by simpa [update_of_ne hpq] using hpi)
        exact ⟨a, Or.inl ha, hpa⟩
  · -- `q` takes a step of its operation, which may return.
    rw [event_of_pending c q hp, step_of_pending c q hp]
    obtain ⟨s, hs⟩ := I.stepResult_after (embed c) q (input q)
    rw [embed_proc] at hs
    cases hr : (I.stepResult (embed c) q (input q)).2.2 with
    | none =>
      rw [hr] at hs
      simp only [Option.map_none, History.record]
      refine ⟨hnd, ?_, ?_⟩
      · intro a ha
        obtain ⟨hao, har, hinv⟩ := hrec a ha
        by_cases hpq : a.proc = q
        · rw [hpq] at har ⊢
          exact ⟨hpq ▸ hao, by simpa [hr, hd] using har, by simp [hs, ProcState.after, Invoked]⟩
        · exact ⟨hao, by simpa [update_of_ne hpq] using har,
            by simpa [update_of_ne hpq] using hinv⟩
      · intro p hpi
        by_cases hpq : p = q
        · subst hpq
          exact hex p (by simp [Invoked, hp])
        · exact hex p (by simpa [update_of_ne hpq] using hpi)
    | some r =>
      rw [hr] at hs
      simp only [Option.map_some, History.record]
      refine ⟨?_, ?_, ?_⟩
      · -- Closing an instance does not change the process it belongs to.
        simpa [List.map_map, comp_def, apply_ite OpRecord.proc] using hnd
      · intro a' ha'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        obtain ⟨hao, har, hinv⟩ := hrec a ha
        by_cases hpq : a.proc = q
        · have hnone : a.returned = none := by rw [hpq] at har; simpa [hd] using har
          rw [ite_eq_left ⟨hpq, by simp [hnone]⟩]
          simp only [hpq]
          exact ⟨hpq ▸ hao, by simp [hd], by simp [hs, ProcState.after, Invoked]⟩
        · rw [ite_eq_right fun h => hpq h.1]
          exact ⟨hao, by simpa [update_of_ne hpq] using har,
            by simpa [update_of_ne hpq] using hinv⟩
      · intro p hpi
        have hpi' : Invoked (c.proc p).state := by
          by_cases hpq : p = q
          · subst hpq
            simp [Invoked, hp]
          · simpa [update_of_ne hpq] using hpi
        obtain ⟨a, ha, hpa⟩ := hex p hpi'
        refine ⟨_, List.mem_map_of_mem ha, ?_⟩
        split <;> simp [hpa]
  · -- `q` has returned: nothing happens.
    rw [event_of_returned c q hp (by omega), step_of_returned c q hp (by omega)]
    exact ⟨hnd, hrec, hex⟩

/-- The history invariant holds along any finite run, for the history the run records. -/
theorem historyInv_run {input : P → Bool} :
    ∀ (ps : List P) (c : Config P R V (ClientState S)) (H : History P Bool Bool)
      (t : ℕ), ClientInv input c → HistoryInv input c H →
      HistoryInv input (I.singleShot.run c ps)
        (I.recordRun t (embed c) H (actions I c ps))
  | [], _, _, _, _, hH => hH
  | q :: qs, c, H, t, hc, hH => by
    simp only [Algorithm.run_cons, actions, recordRun]
    rw [← embed_step]
    exact historyInv_run qs _ _ _ (clientInv_step hc q) (historyInv_step hc hH q t)

/-- Once invoked, a client process stays invoked. -/
theorem invoked_step {input : P → Bool} {c : Config P R V (ClientState S)}
    (hc : ClientInv input c) {p : P} (h : Invoked (c.proc p).state) (q : P) :
    Invoked ((I.singleShot.step c q).proc p).state := by
  by_cases hpq : p = q
  · subst hpq
    rcases (hc p).2 with ⟨hp, h0, -⟩ | ⟨hp, -, -⟩ | ⟨hp, h1, -⟩
    · simp [Invoked, hp, h0] at h
    · obtain ⟨s, hs⟩ := I.stepResult_after (embed c) p (input p)
      rw [step_of_pending c p hp]
      simp only [update_self, hs]
      cases (I.stepResult (embed c) p (input p)).2.2 <;> simp [ProcState.after, Invoked]
    · rw [step_of_returned c p hp (by omega)]
      exact h
  · rwa [Algorithm.step_local_other _ _ hpq]

/-- An invoked client process that has not decided is executing the operation its input names. -/
theorem pending_of_invoked {input : P → Bool} {c : Config P R V (ClientState S)}
    (hc : ClientInv input c) {p : P} (h : Invoked (c.proc p).state)
    (hd : (c.proc p).decision = none) : (c.proc p).state.1.pending = some (input p) := by
  rcases (hc p).2 with ⟨hp, h0, -⟩ | ⟨hp, -, -⟩ | ⟨-, -, hs⟩
  · simp [Invoked, hp, h0] at h
  · exact hp
  · simp [hd] at hs

end COF.SharedMemory.Implementation
