import COF.Universal
import COF.SharedMemory.Implementation
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find

/-! The paper's Corollary `cor:no_cof_univ`, stated with the full notions.

A COF universal construction (`COFUniversal`) gives, for every sequential object, a linearizable
and conflict-obstruction-free implementation in the multi-shot model of
`SharedMemory/Implementation.lean`: arbitrary objects, repeated invocations, histories with
real-time order. The reduction runs such an implementation under a single-shot client, in which
each process invokes the operation named by its input once, at its first step. That
client is an algorithm of the consensus model (`singleShot`). Linearizability and COF of the
implementation give it the single-shot fragments `Linearizes` and `ObjectCOF`
(`binaryUniversal_of_cofUniversal`), and at the consensus object that contradicts
`no_cof_consensus`. -/
namespace COF

/-- A conflict-obstruction-free universal construction (paper, Section 4): for every sequential
object, a linearizable and conflict-obstruction-free implementation from read/write registers.
Register, value and local-state types may depend on the object. Asking for an implementation of
each object, rather than one uniform algorithm, makes this weaker and its impossibility
stronger. -/
def COFUniversal (P : Type*) [DecidableEq P] : Prop :=
  ∀ (Q O Resp : Type) (obj : Object Q O Resp),
    ∃ (R V S : Type) (_ : DecidableEq R) (I : SharedMemory.Implementation P R V S O Resp),
      I.Linearizable obj ∧ I.ConflictObstructionFree obj.Conflict

/-- A legal sequential history of the proposals of `L`'s processes is exactly what `responses`
computes. This connects the linearizations of `Linearizable` to the fragment `Linearizes`. -/
theorem Object.responses_of_legal {P : Type*} (obj : Object Q Bool Bool) (input : P → Bool) :
    ∀ (L : List (P × Bool)) (q : Q), obj.Legal q (L.map fun y => (input y.1, y.2)) →
      obj.responses input q (L.map Prod.fst) = L
  | [], _, _ => rfl
  | (i, r) :: L, q, h => by
    obtain ⟨hr, hL⟩ := h
    simp only [List.map_cons, Object.responses]
    rw [Object.responses_of_legal obj input L _ hL, hr]

namespace SharedMemory.Implementation
open Function

variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable {C : Type*} [DecidableEq C] (I : Implementation P R V S Bool Bool) (e : C → P)

/-- The local state of a client process: its state in the implementation, and its input. -/
abbrev ClientState (S : Type*) := ProcState S Bool × Bool

/-- The single-shot client of `I` on the processes `e i`, as an algorithm of the consensus
model. At its first step a process invokes the operation named by its input. It then
follows the implementation, and decides the response. Once it has returned, it is idle, and its
steps are reads that change nothing. Nobody else is ever invoked. -/
def singleShot : Algorithm (C) R V (ClientState S) where
  initialMemory := I.initialMemory
  initialState i b := (⟨I.initialState (e i), none, 0⟩, b)
  instruction i x :=
    match x.1.pending with
    | some o =>
      match I.instruction (e i) x.1.state with
      | .read r next => .read r fun v => ⟨(x.1.after o (next v).1 (next v).2, x.2), (next v).2⟩
      | .write r v next => .write r v ⟨(x.1.after o next.1 next.2, x.2), next.2⟩
    | none =>
      .read (I.instruction (e i) x.1.state).register fun _ =>
        ⟨if x.1.done = 0 then (⟨I.invoke (e i) x.2 x.1.state, some x.2, 0⟩, x.2) else x, none⟩

/-- The action of the implementation that a step of client process `i`, in local state `x`,
performs: its invocation, a step of its operation, or a step while idle. -/
def actionOf (i : C) (x : ClientState S) : Action P Bool :=
  match x.1.pending with
  | some _ => .step (e i)
  | none => if x.1.done = 0 then .invoke (e i) x.2 else .step (e i)

/-- The configuration of the implementation that a configuration of the client stands for.
Processes outside the client are idle in their initial state. -/
noncomputable def embed (c : Config (C) R V (ClientState S)) : ImplConfig P R V S Bool where
  memory := c.memory
  proc p :=
    match partialInv e p with
    | some i => (c.proc i).state.1
    | none => ⟨I.initialState p, none, 0⟩

/-- The actions of the implementation that a finite run of the client from `c` performs. -/
def actions (I : Implementation P R V S Bool Bool) (e : C → P)
    (c : Config (C) R V (ClientState S)) : List (C) → List (Action P Bool)
  | [] => []
  | i :: is => actionOf e i (c.proc i).state :: actions I e ((I.singleShot e).step c i) is

/-- The actions of the implementation that the client's infinite execution from `c` under
`schedule` performs. -/
def infActions (c : Config (C) R V (ClientState S)) (schedule : ℕ → C) :
    ℕ → Action P Bool :=
  fun m => actionOf e (schedule m)
    (((I.singleShot e).execution c schedule m).proc (schedule m)).state

/-- Client process `i`, in local state `x`, has invoked its operation. -/
def Invoked (x : ClientState S) : Prop := x.1.pending.isSome ∨ x.1.done ≠ 0

/-- The client's invariant for the input vector `input`. Each process remembers its input and is
in one of three phases: not yet invoked; executing the operation its input names; or returned,
which is exactly when it has decided. -/
def ClientInv (input : C → Bool) (c : Config (C) R V (ClientState S)) : Prop :=
  ∀ i, (c.proc i).state.2 = input i ∧
    (((c.proc i).state.1.pending = none ∧ (c.proc i).state.1.done = 0 ∧
        (c.proc i).decision = none) ∨
      ((c.proc i).state.1.pending = some (input i) ∧ (c.proc i).state.1.done = 0 ∧
        (c.proc i).decision = none) ∨
      ((c.proc i).state.1.pending = none ∧ (c.proc i).state.1.done = 1 ∧
        (c.proc i).decision.isSome))

/-- The history of the client so far: one instance for each process that has invoked, proposing
its input, which has returned exactly when the process has decided, and with its decision. -/
def HistoryInv (input : C → Bool) (c : Config (C) R V (ClientState S))
    (H : History P Bool Bool) : Prop :=
  (H.map OpRecord.proc).Nodup ∧
    (∀ a ∈ H, ∃ i, a.proc = e i ∧ a.op = input i ∧
      a.returned.map Prod.fst = (c.proc i).decision ∧ Invoked (c.proc i).state) ∧
    ∀ i, Invoked (c.proc i).state → ∃ a ∈ H, a.proc = e i

variable {I e}

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- The client and the implementation share the memory. -/
@[simp] theorem embed_memory (c : Config (C) R V (ClientState S)) :
    (I.embed e c).memory = c.memory := rfl

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- Client process `i` is process `e i` of the implementation. -/
theorem embed_proc (he : Injective e) (c : Config (C) R V (ClientState S)) (i : C) :
    (I.embed e c).proc (e i) = (c.proc i).state.1 := by
  simp [embed, partialInv_left he]

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- The client starts where the implementation does. -/
theorem embed_initial (he : Injective e) (input : C → Bool) :
    I.embed e ((I.singleShot e).initial input) = I.initial := by
  apply ImplConfig.ext
  · rfl
  · funext p
    simp only [embed]
    cases h : partialInv e p with
    | none => rfl
    | some i =>
      obtain rfl := (he.isPartialInv i p).mp h
      rfl

omit [DecidableEq R] in
/-- Updating one client process updates the corresponding process of the implementation. -/
theorem embed_update (he : Injective e) (c : Config (C) R V (ClientState S)) (m : R → V)
    (i : C) (l : Local (ClientState S)) :
    I.embed e ⟨m, update c.proc i l⟩ = ⟨m, update (I.embed e c).proc (e i) l.state.1⟩ := by
  apply ImplConfig.ext
  · rfl
  · funext p
    cases h : partialInv e p with
    | none =>
      have hp : p ≠ e i := by
        rintro rfl
        rw [partialInv_left he] at h
        cases h
      simp [embed, h, update_of_ne hp]
    | some j =>
      obtain rfl := (he.isPartialInv j p).mp h
      by_cases hji : j = i
      · subst hji
        simp [embed_proc he]
      · simp [embed_proc he, update_of_ne hji, update_of_ne (he.ne hji)]

omit [DecidableEq P] in
/-- A step of a client process with a pending operation is a step of that operation in the
implementation. -/
theorem step_of_pending (he : Injective e) (c : Config (C) R V (ClientState S)) (i : C)
    {o : Bool} (h : (c.proc i).state.1.pending = some o) :
    (I.singleShot e).step c i =
      ⟨(I.stepResult (I.embed e c) (e i) o).1, update c.proc i
        ⟨((I.stepResult (I.embed e c) (e i) o).2.1, (c.proc i).state.2),
          (c.proc i).decision.or (I.stepResult (I.embed e c) (e i) o).2.2⟩⟩ := by
  simp only [Algorithm.step, singleShot, h, stepResult, embed_proc he, embed_memory]
  cases I.instruction (e i) (c.proc i).state.1.state <;> rfl

omit [DecidableEq P] in
/-- A client process that has not invoked yet invokes its operation, the one its input names. -/
theorem step_of_fresh (c : Config (C) R V (ClientState S)) (i : C)
    (h : (c.proc i).state.1.pending = none) (h0 : (c.proc i).state.1.done = 0) :
    (I.singleShot e).step c i =
      ⟨c.memory, update c.proc i
        ⟨(⟨I.invoke (e i) (c.proc i).state.2 (c.proc i).state.1.state,
            some (c.proc i).state.2, 0⟩, (c.proc i).state.2), (c.proc i).decision⟩⟩ := by
  simp only [Algorithm.step, singleShot, h, h0, ite_true, Option.or_none]

omit [DecidableEq P] in
/-- A client process that has returned is idle: its steps change nothing. -/
theorem step_of_returned (c : Config (C) R V (ClientState S)) (i : C)
    (h : (c.proc i).state.1.pending = none) (h0 : (c.proc i).state.1.done ≠ 0) :
    (I.singleShot e).step c i = c := by
  simp only [Algorithm.step, singleShot, h, h0, ite_false, Option.or_none]
  apply Config.ext
  · rfl
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [update_of_ne hj]

/-- **The simulation.** Each step of the client is one action of the implementation, taken from
the corresponding configuration. -/
theorem embed_step (he : Injective e) (c : Config (C) R V (ClientState S)) (i : C) :
    I.embed e ((I.singleShot e).step c i) =
      I.act (I.embed e c) (actionOf e i (c.proc i).state) := by
  cases hp : (c.proc i).state.1.pending with
  | some o =>
    rw [step_of_pending he c i hp, embed_update he]
    simp [actionOf, act, hp, embed_proc he]
  | none =>
    by_cases h0 : (c.proc i).state.1.done = 0
    · rw [step_of_fresh c i hp h0, embed_update he]
      simp [actionOf, act, hp, h0, embed_proc he]
    · rw [step_of_returned c i hp h0]
      simp [actionOf, act, hp, h0, embed_proc he]

omit [DecidableEq P] [DecidableEq C] in
/-- The events the client's steps contribute to the history: a step of a pending operation
contributes its response, if any. -/
theorem event_of_pending (he : Injective e) (c : Config (C) R V (ClientState S)) (i : C)
    {o : Bool} (h : (c.proc i).state.1.pending = some o) :
    I.event (I.embed e c) (actionOf e i (c.proc i).state) =
      (I.stepResult (I.embed e c) (e i) o).2.2.map (.res (e i)) := by
  simp [actionOf, event, h, embed_proc he]

omit [DecidableEq P] [DecidableEq C] in
/-- A process that has not invoked yet contributes its invocation. -/
theorem event_of_fresh (he : Injective e) (c : Config (C) R V (ClientState S)) (i : C)
    (h : (c.proc i).state.1.pending = none) (h0 : (c.proc i).state.1.done = 0) :
    I.event (I.embed e c) (actionOf e i (c.proc i).state) =
      some (.inv (e i) (c.proc i).state.2) := by
  simp [actionOf, event, h, h0, embed_proc he]

omit [DecidableEq P] [DecidableEq C] in
/-- A process that has returned contributes nothing. -/
theorem event_of_returned (he : Injective e) (c : Config (C) R V (ClientState S))
    (i : C) (h : (c.proc i).state.1.pending = none) (h0 : (c.proc i).state.1.done ≠ 0) :
    I.event (I.embed e c) (actionOf e i (c.proc i).state) = none := by
  simp [actionOf, event, h, h0, embed_proc he]

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- Initially, every client process remembers its input and has not invoked yet. -/
theorem clientInv_initial (input : C → Bool) :
    ClientInv input ((I.singleShot e).initial input) := by
  intro i
  simp [Algorithm.initial, singleShot]

omit [DecidableEq P] in
/-- The invariant survives any step of the client. -/
theorem clientInv_step (he : Injective e) {input : C → Bool}
    {c : Config (C) R V (ClientState S)} (h : ClientInv input c) (j : C) :
    ClientInv input ((I.singleShot e).step c j) := by
  intro i
  by_cases hij : i = j
  · subst hij
    obtain ⟨hin, hph⟩ := h i
    rcases hph with ⟨hp, h0, hd⟩ | ⟨hp, h0, hd⟩ | ⟨hp, h1, hd⟩
    · rw [step_of_fresh c i hp h0]
      simp [hin, hd]
    · obtain ⟨s, hs⟩ := I.stepResult_after (I.embed e c) (e i) (input i)
      rw [step_of_pending he c i hp]
      simp only [update_self, hs, embed_proc he]
      cases (I.stepResult (I.embed e c) (e i) (input i)).2.2 <;>
        simp [ProcState.after, hin, h0, hd]
    · rw [step_of_returned c i hp (by omega)]
      exact h i
  · rw [Algorithm.step_local_other _ _ hij]
    exact h i

omit [DecidableEq P] in
/-- The invariant holds along every finite run. -/
theorem clientInv_run (he : Injective e) {input : C → Bool} :
    ∀ (ps : List (C)) {c : Config (C) R V (ClientState S)}, ClientInv input c →
      ClientInv input ((I.singleShot e).run c ps)
  | [], _, h => h
  | j :: js, _, h => clientInv_run he js (clientInv_step he h j)

/-- The history invariant survives any step of the client, together with the event it
contributes. -/
theorem historyInv_step (he : Injective e) {input : C → Bool}
    {c : Config (C) R V (ClientState S)} {H : History P Bool Bool}
    (hc : ClientInv input c) (hH : HistoryInv e input c H) (j : C) (t : ℕ) :
    HistoryInv e input ((I.singleShot e).step c j)
      (H.record t (I.event (I.embed e c) (actionOf e j (c.proc j).state))) := by
  obtain ⟨hnd, hrec, hex⟩ := hH
  obtain ⟨hin, hph⟩ := hc j
  rcases hph with ⟨hp, h0, hd⟩ | ⟨hp, h0, hd⟩ | ⟨hp, h1, hd⟩
  · -- `j` invokes: a new instance, and nobody else changes.
    rw [event_of_fresh he c j hp h0, step_of_fresh c j hp h0, hin]
    have hnot : ∀ a ∈ H, a.proc ≠ e j := by
      intro a ha hpa
      obtain ⟨i, hai, -, -, hinv⟩ := hrec a ha
      obtain rfl : i = j := he (hai.symm.trans hpa)
      simp [Invoked, hp, h0] at hinv
    refine ⟨?_, ?_, ?_⟩
    · simp only [History.record, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, ?_⟩
      simp only [List.mem_singleton]
      rintro _ hx _ rfl
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact hnot a ha
    · intro a ha
      simp only [History.record, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · obtain ⟨i, hai, hao, har, hinv⟩ := hrec a ha
        have hij : i ≠ j := fun hij => hnot a ha (hij ▸ hai)
        exact ⟨i, hai, hao, by simpa [update_of_ne hij] using har,
          by simpa [update_of_ne hij] using hinv⟩
      · exact ⟨j, rfl, rfl, by simp [hd], by simp [Invoked]⟩
    · intro i hi
      simp only [History.record, List.mem_append, List.mem_singleton]
      by_cases hij : i = j
      · subst hij
        exact ⟨_, Or.inr rfl, rfl⟩
      · obtain ⟨a, ha, hpa⟩ := hex i (by simpa [update_of_ne hij] using hi)
        exact ⟨a, Or.inl ha, hpa⟩
  · -- `j` takes a step of its operation, which may return.
    rw [event_of_pending he c j hp, step_of_pending he c j hp]
    obtain ⟨s, hs⟩ := I.stepResult_after (I.embed e c) (e j) (input j)
    rw [embed_proc he] at hs
    cases hr : (I.stepResult (I.embed e c) (e j) (input j)).2.2 with
    | none =>
      rw [hr] at hs
      simp only [Option.map_none, History.record]
      refine ⟨hnd, ?_, ?_⟩
      · intro a ha
        obtain ⟨i, hai, hao, har, hinv⟩ := hrec a ha
        by_cases hij : i = j
        · subst hij
          exact ⟨i, hai, hao, by simpa [hr, hd] using har, by simp [hs, ProcState.after, Invoked]⟩
        · exact ⟨i, hai, hao, by simpa [update_of_ne hij] using har,
            by simpa [update_of_ne hij] using hinv⟩
      · intro i hi
        by_cases hij : i = j
        · subst hij
          exact hex i (by simp [Invoked, hp])
        · exact hex i (by simpa [update_of_ne hij] using hi)
    | some r =>
      rw [hr] at hs
      simp only [Option.map_some, History.record]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.map_map]
        convert hnd using 1
        apply List.map_congr_left
        intro a _
        simp only [comp_apply]
        split <;> rfl
      · intro a' ha'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        obtain ⟨i, hai, hao, har, hinv⟩ := hrec a ha
        by_cases hij : i = j
        · subst hij
          have hnone : a.returned = none := by simpa [hd] using har
          rw [ite_eq_left ⟨hai, by simp [hnone]⟩]
          exact ⟨i, hai, hao, by simp [hd], by simp [hs, ProcState.after, Invoked]⟩
        · have hne : a.proc ≠ e j := by rw [hai]; exact he.ne hij
          rw [ite_eq_right fun h => hne h.1]
          exact ⟨i, hai, hao, by simpa [update_of_ne hij] using har,
            by simpa [update_of_ne hij] using hinv⟩
      · intro i hi
        have hi' : Invoked (c.proc i).state := by
          by_cases hij : i = j
          · subst hij
            simp [Invoked, hp]
          · simpa [update_of_ne hij] using hi
        obtain ⟨a, ha, hpa⟩ := hex i hi'
        refine ⟨_, List.mem_map_of_mem ha, ?_⟩
        split <;> simp [hpa]
  · -- `j` has returned: nothing happens.
    rw [event_of_returned he c j hp (by omega), step_of_returned c j hp (by omega)]
    exact ⟨hnd, hrec, hex⟩

/-- The invariant holds along any finite run, for the history the run records. -/
theorem historyInv_run (he : Injective e) {input : C → Bool} :
    ∀ (ps : List (C)) (c : Config (C) R V (ClientState S)) (H : History P Bool Bool)
      (t : ℕ), ClientInv input c → HistoryInv e input c H →
      HistoryInv e input ((I.singleShot e).run c ps)
        (I.recordRun t (I.embed e c) H (actions I e c ps))
  | [], _, _, _, _, hH => hH
  | j :: js, c, H, t, hc, hH => by
    simp only [Algorithm.run_cons, actions, recordRun]
    rw [← embed_step he]
    exact historyInv_run he js _ _ _ (clientInv_step he hc j) (historyInv_step he hc hH j t)

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- Reading the client processes off a linearization of the client's history, the operations
are the processes' inputs. -/
theorem map_filterMap_partialInv (he : Injective e) (input : C → Bool)
    {S : List (OpRecord P Bool Bool × Bool)}
    (hS : ∀ x ∈ S, ∃ i, x.1.proc = e i ∧ x.1.op = input i) :
    (S.filterMap fun x => (partialInv e x.1.proc).map (·, x.2)).map
        (fun y => (input y.1, y.2)) = S.map fun x => (x.1.op, x.2) := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    obtain ⟨i, hi, ho⟩ := hS x List.mem_cons_self
    simp [hi, ho, partialInv_left he, ih fun y hy => hS y (List.mem_cons_of_mem _ hy)]

/-- **Linearizability yields the single-shot fragment.** A linearization of the client's history
orders the proposals of some of the processes, including every one that has returned, and its
responses are the decisions. -/
theorem linearizes_singleShot (he : Injective e) {obj : Object Q Bool Bool}
    (h : I.Linearizable obj) : (I.singleShot e).Linearizes obj := by
  intro input c hr
  obtain ⟨ps, -, rfl⟩ := hr
  have hinit : ClientInv input ((I.singleShot e).initial input) := clientInv_initial input
  have hc := clientInv_run (I := I) he ps hinit
  have hH := historyInv_run (I := I) he ps ((I.singleShot e).initial input) [] 0
    hinit ⟨List.nodup_nil, by simp, fun i hi => by
      simp [Invoked, Algorithm.initial, singleShot] at hi⟩
  rw [embed_initial he] at hH
  obtain ⟨hHnd, hrec, hex⟩ := hH
  obtain ⟨S, hnd, hsub, hcomp, hlegal, -⟩ := h (actions I e ((I.singleShot e).initial input) ps)
  have hS : ∀ x ∈ S, ∃ i, x.1.proc = e i ∧ x.1.op = input i := fun x hx => by
    obtain ⟨i, hi, ho, -, -⟩ := hrec x.1 (hsub x hx)
    exact ⟨i, hi, ho⟩
  refine ⟨(S.filterMap fun x => (partialInv e x.1.proc).map (·, x.2)).map Prod.fst, ?_, ?_⟩
  · -- Distinct linearized instances belong to distinct processes.
    have hprocs : (S.map fun x => x.1.proc).Nodup := by
      have := hnd.map_on (f := OpRecord.proc) fun a ha b hb hab => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact List.inj_on_of_nodup_map hHnd (hsub x hx) (hsub y hy) hab
      simpa [List.map_map, comp_def] using this
    have := hprocs.filterMap (f := partialInv e) fun a a' b ha ha' => by
      rw [Option.mem_def, he.isPartialInv] at ha ha'
      exact ha.symm.trans ha'
    simpa [List.map_filterMap, List.filterMap_map, Option.map_map, comp_def] using this
  · intro i v hv
    rw [Object.responses_of_legal obj input _ _
      (by rwa [map_filterMap_partialInv he input hS])]
    -- A decided process has returned, so its instance is linearized, with its decision.
    have hinv :
        Invoked (((I.singleShot e).run ((I.singleShot e).initial input) ps).proc i).state := by
      rcases (hc i).2 with ⟨-, -, hd⟩ | ⟨-, -, hd⟩ | ⟨-, h1, -⟩
      · rw [hd] at hv
        cases hv
      · rw [hd] at hv
        cases hv
      · simp [Invoked, h1]
    obtain ⟨a, ha, hpa⟩ := hex i hinv
    obtain ⟨i', hai', -, har, -⟩ := hrec a ha
    obtain rfl : i' = i := he (hai'.symm.trans hpa)
    rw [hv] at har
    obtain ⟨⟨v', t⟩, hret, rfl⟩ := Option.map_eq_some_iff.mp har
    exact List.mem_filterMap.mpr ⟨(a, v'), hcomp a ha v' t hret, by simp [hpa, partialInv_left he]⟩

/-- The client's infinite executions are executions of the implementation. -/
theorem embed_execution (he : Injective e) (c : Config (C) R V (ClientState S))
    (schedule : ℕ → C) (k : ℕ) :
    I.embed e ((I.singleShot e).execution c schedule k) =
      I.execution (I.embed e c) (I.infActions e c schedule) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change I.embed e ((I.singleShot e).step _ (schedule k)) = I.act (I.execution _ _ k) _
    rw [embed_step he, ih]
    rfl

/-- From the initial configuration, in particular, the client's execution is the
implementation's execution of `infActions`. -/
theorem execution_infActions (he : Injective e) (input : C → Bool) (schedule : ℕ → C)
    (k : ℕ) :
    I.execution I.initial (I.infActions e ((I.singleShot e).initial input) schedule) k =
      I.embed e ((I.singleShot e).execution ((I.singleShot e).initial input) schedule k) := by
  rw [embed_execution he, embed_initial he]

omit [DecidableEq P] in
/-- The invariant holds along every infinite execution. -/
theorem clientInv_execution (he : Injective e) {input : C → Bool}
    {c : Config (C) R V (ClientState S)} (h : ClientInv input c) (schedule : ℕ → C) :
    ∀ k, ClientInv input ((I.singleShot e).execution c schedule k)
  | 0 => h
  | k + 1 => clientInv_step he (clientInv_execution he h schedule k) (schedule k)

omit [DecidableEq P] in
/-- Once invoked, a client process stays invoked. -/
theorem invoked_step (he : Injective e) {input : C → Bool}
    {c : Config (C) R V (ClientState S)} (hc : ClientInv input c) {i : C}
    (h : Invoked (c.proc i).state) (j : C) :
    Invoked (((I.singleShot e).step c j).proc i).state := by
  by_cases hij : i = j
  · subst hij
    rcases (hc i).2 with ⟨hp, h0, -⟩ | ⟨hp, -, -⟩ | ⟨hp, h1, -⟩
    · simp [Invoked, hp, h0] at h
    · obtain ⟨s, hs⟩ := I.stepResult_after (I.embed e c) (e i) (input i)
      rw [step_of_pending he c i hp]
      simp only [update_self, hs]
      cases (I.stepResult (I.embed e c) (e i) (input i)).2.2 <;> simp [ProcState.after, Invoked]
    · rw [step_of_returned c i hp (by omega)]
      exact h
  · rwa [Algorithm.step_local_other _ _ hij]

omit [DecidableEq P] [DecidableEq R] [DecidableEq C] in
/-- An invoked client process that has not decided is executing its operation. -/
theorem pending_of_invoked {input : C → Bool} {c : Config (C) R V (ClientState S)}
    (hc : ClientInv input c) {i : C} (h : Invoked (c.proc i).state)
    (hd : (c.proc i).decision = none) : (c.proc i).state.1.pending = some (input i) := by
  rcases (hc i).2 with ⟨hp, h0, -⟩ | ⟨hp, -, -⟩ | ⟨-, -, hs⟩
  · simp [Invoked, hp, h0] at h
  · exact hp
  · simp [hd] at hs

/-- In the trace, a step belongs to the scheduled client process's pending proposal, if any. -/
theorem trace_step_infActions (he : Injective e) (input : C → Bool) (schedule : ℕ → C)
    (k : ℕ) :
    (I.trace (I.infActions e ((I.singleShot e).initial input) schedule)).step k =
      (((I.singleShot e).execution ((I.singleShot e).initial input) schedule k).proc
        (schedule k)).state.1.pending.map fun o => (e (schedule k),
          (((I.singleShot e).execution ((I.singleShot e).initial input) schedule k).proc
            (schedule k)).state.1.done, o) := by
  simp only [trace]
  rw [execution_infActions he]
  cases hp : (((I.singleShot e).execution ((I.singleShot e).initial input) schedule k).proc
      (schedule k)).state.1.pending with
  | some o => simp [infActions, actionOf, hp, embed_proc he]
  | none =>
    by_cases h0 : (((I.singleShot e).execution ((I.singleShot e).initial input) schedule k).proc
        (schedule k)).state.1.done = 0 <;>
      simp [infActions, actionOf, hp, h0, embed_proc he]

/-- The first time a client process is scheduled, it invokes its proposal. -/
theorem trace_invoked_infActions (he : Injective e) (input : C → Bool)
    (schedule : ℕ → C) {p : C} {t : ℕ} (ht : schedule t = p)
    (hfirst : ∀ m < t, schedule m ≠ p) :
    (I.trace (I.infActions e ((I.singleShot e).initial input) schedule)).invoked
      (e p, 0, input p) := by
  have hfresh := (I.singleShot e).execution_proc_of_unscheduled
    ((I.singleShot e).initial input) schedule hfirst
  refine ⟨t, ?_, ?_, ?_⟩
  · simp only [infActions]
    rw [ht, hfresh]
    simp [actionOf, Algorithm.initial, singleShot]
  · rw [execution_infActions he, embed_proc he, hfresh]
    rfl
  · rw [execution_infActions he, embed_proc he, hfresh]
    rfl

omit [DecidableEq P] in
/-- After its first scheduling, a client process stays invoked. -/
theorem invoked_after (he : Injective e) (input : C → Bool) (schedule : ℕ → C)
    {p : C} {t : ℕ} (ht : schedule t = p) (hfirst : ∀ m < t, schedule m ≠ p) :
    ∀ m, t < m → Invoked
      (((I.singleShot e).execution ((I.singleShot e).initial input) schedule m).proc p).state := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hfresh := (I.singleShot e).execution_proc_of_unscheduled
      ((I.singleShot e).initial input) schedule hfirst
    change Invoked (((I.singleShot e).step ((I.singleShot e).execution
      ((I.singleShot e).initial input) schedule t) (schedule t)).proc p).state
    rw [ht, step_of_fresh _ p (by rw [hfresh]; simp [Algorithm.initial, singleShot])
      (by rw [hfresh]; simp [Algorithm.initial, singleShot])]
    simp [Invoked]
  | succ m _ ih =>
    exact invoked_step he
      (clientInv_execution he (clientInv_initial (I := I) (e := e) input) schedule m) ih
      (schedule m)

/-- A client process scheduled infinitely often is correct: it keeps taking steps while it has
not decided, and is idle for good once it has. -/
theorem trace_correct_infActions (he : Injective e) (input : C → Bool)
    (schedule : ℕ → C) {p : C} {t : ℕ} (ht : schedule t = p)
    (hfirst : ∀ m < t, schedule m ≠ p) (hinf : ∀ N, ∃ k ≥ N, schedule k = p) :
    (I.trace (I.infActions e ((I.singleShot e).initial input) schedule)).correct
      (e p, 0, input p) := by
  have hinv := clientInv_execution (I := I) he (clientInv_initial (I := I) (e := e) input) schedule
  by_cases hdec : ∃ m, (((I.singleShot e).execution ((I.singleShot e).initial input) schedule
      m).proc p).decision.isSome
  · right
    obtain ⟨m, hm⟩ := hdec
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
    refine ⟨m, fun k hk => ?_⟩
    have hvk := (I.singleShot e).execution_decision hk hv
    rw [execution_infActions he, embed_proc he]
    rcases (hinv k p).2 with ⟨-, -, hd⟩ | ⟨-, -, hd⟩ | ⟨hp, -, -⟩
    · exact absurd (hvk.symm.trans hd) (by simp)
    · exact absurd (hvk.symm.trans hd) (by simp)
    · exact hp
  · left
    push Not at hdec
    intro N
    obtain ⟨k, hk, hkp⟩ := hinf (N + t + 1)
    have hpend := pending_of_invoked (hinv k)
      (invoked_after he input schedule ht hfirst k (by omega)) (by simpa using hdec k)
    refine ⟨k, by omega, ?_, ?_⟩
    · simp [infActions, hkp, actionOf, hpend]
    · rw [execution_infActions he, embed_proc he, hpend]
      rfl

/-- If eventually only processes whose proposals do not conflict with `p`'s take steps, then
`p`'s proposal is eventually conflict-free in the trace. -/
theorem trace_conflictFree_infActions (he : Injective e) (input : C → Bool)
    (schedule : ℕ → C) {obj : Object Q Bool Bool} {p : C} {N : ℕ}
    (hN : ∀ k ≥ N, schedule k ≠ p → ¬ obj.Conflict (input p) (input (schedule k))) :
    ∀ k ≥ N, ∀ j, (I.trace (I.infActions e ((I.singleShot e).initial input) schedule)).step k =
      some j → j ≠ (e p, 0, input p) → ¬ obj.Conflict (input p) j.2.2 := by
  intro k hk j hstep hne
  rw [trace_step_infActions he] at hstep
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hstep
  rcases (clientInv_execution (I := I) he (clientInv_initial (I := I) (e := e) input) schedule k
      (schedule k)).2 with ⟨hp, -, -⟩ | ⟨hp, h0, -⟩ | ⟨hp, -, -⟩
  · simp [hp] at ho
  · rw [hp] at ho
    obtain rfl := Option.some.inj ho
    refine hN k hk fun hq => hne ?_
    rw [h0, hq]
  · simp [hp] at ho

/-- **COF yields the single-shot fragment.** In the execution of the implementation that the
client stands for, a process's proposal is invoked when the process is first scheduled. If the
process is scheduled infinitely often and eventually only processes with non-conflicting
proposals step, the proposal is eventually conflict-free, so COF forces it to return. -/
theorem objectCOF_singleShot (he : Injective e) {obj : Object Q Bool Bool}
    (h : I.ConflictObstructionFree obj.Conflict) : (I.singleShot e).ObjectCOF obj := by
  classical
  intro input c hr schedule p hinf hfree
  obtain ⟨ps, -, rfl⟩ := hr
  obtain ⟨N, hN⟩ := hfree
  -- Run the client from its initial configuration: first `ps`, then `schedule`.
  have hsk : ∀ k, Algorithm.prepend ps schedule (ps.length + k) = schedule k :=
    Algorithm.prepend_add ps schedule
  have hsched : ∃ t, Algorithm.prepend ps schedule t = p := by
    obtain ⟨k, -, hk⟩ := hinf 0
    exact ⟨ps.length + k, by rw [hsk, hk]⟩
  have hinf' : ∀ M, ∃ k ≥ M, Algorithm.prepend ps schedule k = p := by
    intro M
    obtain ⟨k, hk, hkp⟩ := hinf M
    exact ⟨ps.length + k, by omega, by rw [hsk, hkp]⟩
  have hN' : ∀ k ≥ ps.length + N, Algorithm.prepend ps schedule k ≠ p →
      ¬ obj.Conflict (input p) (input (Algorithm.prepend ps schedule k)) := by
    intro k hk hkp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show ps.length ≤ k by omega)
    rw [hsk] at hkp ⊢
    exact hN m (by omega) hkp
  have hfirst : ∀ m < Nat.find hsched, Algorithm.prepend ps schedule m ≠ p :=
    fun m hm => Nat.find_min hsched hm
  obtain ⟨t, ht⟩ := h (I.trace (I.infActions e ((I.singleShot e).initial input)
      (Algorithm.prepend ps schedule))) ⟨_, rfl⟩ (e p, 0, input p)
    (trace_invoked_infActions he input _ (Nat.find_spec hsched) hfirst)
    (trace_correct_infActions he input _ (Nat.find_spec hsched) hfirst hinf')
    (Or.inr ⟨ps.length + N, trace_conflictFree_infActions he input _ hN'⟩)
  -- The proposal returned, so the process has decided.
  change 0 < ((I.execution I.initial _ t).proc (e p)).done at ht
  rw [execution_infActions he, embed_proc he] at ht
  rcases (clientInv_execution (I := I) he (clientInv_initial (I := I) (e := e) input)
      (Algorithm.prepend ps schedule) t p).2 with ⟨-, h0, -⟩ | ⟨-, h0, -⟩ | ⟨-, -, hd⟩
  · rw [h0] at ht
    exact absurd ht (lt_irrefl 0)
  · rw [h0] at ht
    exact absurd ht (lt_irrefl 0)
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
    refine ⟨t - ps.length, v, ?_⟩
    rw [← Algorithm.execution_prepend]
    exact (I.singleShot e).execution_decision (by omega) hv

/-- No linearizable, conflict-obstruction-free implementation of binary consensus exists for
three or more processes, in the full multi-shot model. Its single-shot client would be a COF
consensus algorithm, which `no_cof_consensus` rules out. -/
theorem no_linearizable_cof_consensus (I : Implementation P R V S Bool Bool) (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) :
    ¬ (I.Linearizable consensusObject ∧ I.ConflictObstructionFree consensusObject.Conflict) := by
  rintro ⟨hlin, hcof⟩
  exact (I.singleShot id).no_cof_consensus p₀ p₁ p₂ h₀₁ h₂₀ h₂₁
    ⟨(I.singleShot id).safe_of_consensus_linearizes (linearizes_singleShot injective_id hlin),
      (I.singleShot id).termination_of_consensus_objectCOF
        (objectCOF_singleShot injective_id hcof)⟩

end SharedMemory.Implementation

open SharedMemory Function

/-- **The single-shot fragment is a consequence of the full notion.** A COF universal
construction yields `BinaryUniversal`, for the same processes: run each binary object's
implementation under the single-shot client. -/
theorem binaryUniversal_of_cofUniversal {P : Type} [DecidableEq P] (h : COFUniversal P) :
    BinaryUniversal P := by
  intro Q obj
  obtain ⟨R, V, S, inst, I, hlin, hcof⟩ := h Q Bool Bool obj
  let _ : DecidableEq R := inst
  exact ⟨R, V, Implementation.ClientState S, inst, I.singleShot id,
    Implementation.linearizes_singleShot injective_id hlin,
    Implementation.objectCOF_singleShot injective_id hcof⟩

/-- **Paper Corollary `cor:no_cof_univ`**: no conflict-obstruction-free universal construction
exists in the read/write model with three or more processes. Its implementation of binary
consensus would be linearizable and conflict-obstruction-free. -/
theorem no_cofUniversal {P : Type*} [DecidableEq P] (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) : ¬ COFUniversal P := by
  intro h
  obtain ⟨R, V, S, inst, I, hlin, hcof⟩ := h (Option Bool) Bool Bool consensusObject
  let _ : DecidableEq R := inst
  exact I.no_linearizable_cof_consensus p₀ p₁ p₂ h₀₁ h₂₀ h₂₁ ⟨hlin, hcof⟩

/-- Numeric formulation, for a system of `n ≥ 3` processes. -/
theorem no_cofUniversal_fin {n : ℕ} (hn : 3 ≤ n) : ¬ COFUniversal (Fin n) :=
  no_cofUniversal ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))

end COF
