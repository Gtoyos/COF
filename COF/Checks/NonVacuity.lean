import COF.Paper

/-!
# The hypotheses of the impossibility results are satisfiable

An impossibility theorem is empty if its hypotheses cannot hold at all. This file shows that each
hypothesis is satisfiable on its own terms:

* **COF consensus with one process** (`cofConsensus_satisfiable`). Validity, Agreement and COF
  termination hold together for the trivial algorithm `decideOwnInput`, which really decides
  (`decideOwnInput_decides`). Theorem 6 needs its three processes.
* **A COF universal construction with one process** (`cofUniversal_unit`). The process runs the
  sequential specification itself, so every object has a linearizable, wait-free implementation.
  Corollary 7 needs its three processes.
* **A linearizable, COF implementation with three processes** (`eager_linearizable_cof`), of the
  object with one state. So linearizability and COF remain satisfiable when several processes
  interleave: Corollary 7 rules out COF universal constructions only because every object,
  consensus included, must be implemented.

Both implementations answer every operation at its first step. They are linearizable and
wait-free by two sufficient conditions, proved first for any implementation
(`isLinearization_returnedOps`, `waitFree_of_steps_return`).
-/

namespace COF.Checks
open SharedMemory SharedMemory.Implementation

/-! ## Two sufficient conditions, for any implementation -/

section Sufficient
variable {P R V S O Resp : Type*}

/-- The returned instances of a history, in order, each with its response. -/
def returnedOps (H : History P O Resp) : List (OpRecord P O Resp × Resp) :=
  H.filterMap fun a => a.returned.map fun x => (a, x.1)

/-- The returned instances of a history, in order, form a sublist of it. -/
theorem returnedOps_sublist (H : History P O Resp) :
    ((returnedOps H).map Prod.fst).Sublist H := by
  induction H with
  | nil => simp [returnedOps]
  | cons a H ih =>
    cases h : a.returned with
    | none => simpa [returnedOps, h] using ih.cons a
    | some x => simpa [returnedOps, h] using ih.cons_cons a

/-- **A sufficient condition for linearizability.** If the instances of a history are listed in
increasing order of invocation, and each returns after it was invoked, then its returned
instances, in that order and with their responses, linearize it as soon as they are legal. -/
theorem isLinearization_returnedOps {Q : Type*} {obj : Object Q O Resp} {H : History P O Resp}
    (horder : H.Pairwise fun a b => a.invokedAt < b.invokedAt)
    (hret : ∀ a ∈ H, ∀ r t, a.returned = some (r, t) → a.invokedAt < t)
    (hlegal : obj.Legal obj.initial ((returnedOps H).map fun x => (x.1.op, x.2))) :
    IsLinearization obj H (returnedOps H) where
  nodup := by
    have hnd : H.Nodup := horder.imp fun h hab => by subst hab; omega
    exact hnd.sublist (returnedOps_sublist H)
  subset x hx := by
    obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hax
    exact ha
  complete a ha r t hr := List.mem_filterMap.mpr ⟨a, ha, by simp [hr]⟩
  legal := hlegal
  realTime x y hxy r t hy := by
    -- `x` comes before `y` in the history, so it was invoked before `y`, which returned later.
    have hsub := (hxy.map Prod.fst).trans (returnedOps_sublist H)
    have hlt := List.rel_of_pairwise_cons (horder.sublist hsub) (List.mem_singleton_self _)
    have := hret y.1 (hsub.subset (by simp)) r t hy
    omega

/-- An action of another process leaves `p` unchanged. -/
theorem act_proc_other (I : Implementation P R V S O Resp) {c : ImplConfig P R V S O}
    {a : Action P O} {p : P} (hi : ∀ o, a ≠ .invoke p o) (hs : a ≠ .step p) :
    (I.act c a).proc p = c.proc p := by
  cases a with
  | invoke q o =>
    have hq : p ≠ q := fun h => hi o (by rw [h])
    cases h : (c.proc q).pending <;> simp [act, h, Function.update, hq]
  | step q =>
    have hq : p ≠ q := fun h => hs (by rw [h])
    cases h : (c.proc q).pending <;> simp [act, h, Function.update, hq]

/-- An action leaves a busy process `p` busy, unless it is a step of `p` that returns; then one
more operation of `p` has returned. -/
theorem act_busy (I : Implementation P R V S O Resp) {c : ImplConfig P R V S O} {p : P} {o : O}
    (h : (c.proc p).pending = some o) (a : Action P O) :
    (c.proc p).done < ((I.act c a).proc p).done ∨
      (((I.act c a).proc p).pending.isSome ∧ ((I.act c a).proc p).done = (c.proc p).done) := by
  by_cases hs : a = .step p
  · -- A step of the operation: it returns, or it stays pending.
    subst hs
    obtain ⟨s, hs⟩ := I.stepResult_after c p o
    simp only [act, h, Function.update_self, hs]
    cases (I.stepResult c p o).2.2 <;> simp [ProcState.after]
  · -- Invoking a busy process does nothing, and an action of another process leaves `p` alone.
    right
    by_cases hi : ∃ o', a = .invoke p o'
    · obtain ⟨o', rfl⟩ := hi
      simp [act, h]
    · push Not at hi
      simp [act_proc_other I hi hs, h]

/-- An operation invoked on `p` at time `t`, when `k` operations of `p` have returned, stays
pending until it returns: at every later time, more than `k` operations of `p` have returned, or
`p` is still busy with `k` returned. -/
theorem pending_until_returned (I : Implementation P R V S O Resp) (α : ℕ → Action P O)
    {p : P} {t k : ℕ} {o : O} (hat : α t = .invoke p o)
    (hpt : ((I.execution I.initial α t).proc p).pending = none)
    (hdt : ((I.execution I.initial α t).proc p).done = k) :
    ∀ m, t < m → k < ((I.execution I.initial α m).proc p).done ∨
      (((I.execution I.initial α m).proc p).pending.isSome ∧
        ((I.execution I.initial α m).proc p).done = k) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    rw [execution_succ, hat]
    simp [act, hpt, hdt]
  | succ m _ ih =>
    rw [execution_succ]
    rcases ih with hk | ⟨hb, rfl⟩
    · exact Or.inl (lt_of_lt_of_le hk (I.done_le_act _ _ _))
    · obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      exact act_busy I ho' (α m)

/-- **A sufficient condition for wait freedom.** If, in every execution, a step of a pending
operation returns it, the implementation is wait-free. A correct process either takes another
step, which returns its operation, or is eventually idle, which it is only once its operation has
returned. -/
theorem waitFree_of_steps_return (I : Implementation P R V S O Resp)
    (h : ∀ α m p o, ((I.execution I.initial α m).proc p).pending = some o →
      ((I.act (I.execution I.initial α m) (.step p)).proc p).done =
        ((I.execution I.initial α m).proc p).done + 1) :
    I.WaitFree := by
  rintro _ ⟨α, rfl⟩ ⟨p, k, o⟩ ⟨t, hat, hpt, hdt⟩ hcorr
  have key := pending_until_returned I α hat hpt hdt
  rcases hcorr with hsteps | ⟨N, hidle⟩
  · -- `p` steps at some time `m > t`; unless the operation has returned by then, it returns now.
    obtain ⟨m, hm, hstep, -⟩ := hsteps (t + 1)
    rcases key m (by omega) with hk | ⟨hb, hd⟩
    · exact ⟨m, hk⟩
    · obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      refine ⟨m + 1, ?_⟩
      rw [execution_succ, hstep, h α m p o' ho', hd]
      omega
  · -- `p` is eventually idle, so it is not still busy with the operation.
    rcases key (max N (t + 1)) (by omega) with hk | ⟨hb, -⟩
    · exact ⟨_, hk⟩
    · simp [hidle _ (Nat.le_max_left _ _)] at hb

end Sufficient

/-! ## COF consensus with one process -/

/-- `decideOwnInput` on a single process is a COF consensus algorithm. -/
theorem cofConsensus_satisfiable : ∃ a : Algorithm Unit Unit Unit Bool, a.COFConsensus :=
  ⟨Algorithm.decideOwnInput Unit, Algorithm.decideOwnInput_cofConsensus⟩

/-- The witness takes decisions: validity and agreement do not hold merely because nothing is
ever decided. -/
theorem decideOwnInput_decides :
    (((Algorithm.decideOwnInput Unit).run
      ((Algorithm.decideOwnInput Unit).initial (fun _ => true)) [()]).proc ()).decision =
      some true := by
  simp [Algorithm.initial, Algorithm.step, Algorithm.decideOwnInput]

/-! ## A COF universal construction with one process -/

section OneProcess

variable {Q O Resp : Type} (obj : Object Q O Resp)

/-- A step of the one-process construction: apply the pending operation, if any, and return
its sequential response. -/
def seqRespond (s : Q × Option O) : (Q × Option O) × Option Resp :=
  match s.2 with
  | some o => (((obj.transition o s.1).2, none), some (obj.transition o s.1).1)
  | none => (s, none)

/-- The one-process universal construction. The local state holds the object's state and the
pending operation; each step writes a dummy register and answers. -/
def seqImpl : Implementation Unit Unit Unit (Q × Option O) O Resp where
  initialMemory _ := ()
  initialState _ := (obj.initial, none)
  invoke _ o s := (s.1, some o)
  instruction _ s := .write () () (seqRespond obj s)

/-- `L` is a legal sequential history from `q`, ending in state `q'`. -/
def Replays (obj : Object Q O Resp) : Q → List (O × Resp) → Q → Prop
  | q, [], q' => q = q'
  | q, (o, r) :: L, q' => (obj.transition o q).1 = r ∧ Replays obj (obj.transition o q).2 L q'

variable {obj} in
/-- A replayed history is legal. -/
theorem Replays.legal : ∀ {q : Q} {L : List (O × Resp)} {q' : Q},
    Replays obj q L q' → obj.Legal q L
  | _, [], _, _ => trivial
  | _, (_, _) :: _, _, ⟨hr, h⟩ => ⟨hr, Replays.legal h⟩

variable {obj} in
/-- Replaying one more operation from the final state extends the history. -/
theorem Replays.snoc : ∀ {q : Q} {L : List (O × Resp)} {q' : Q}, Replays obj q L q' →
    ∀ o, Replays obj q (L ++ [(o, (obj.transition o q').1)]) (obj.transition o q').2
  | _, [], _, h, _ => by
    subst h
    exact ⟨rfl, rfl⟩
  | _, (_, _) :: _, _, ⟨hr, h⟩, o => ⟨hr, Replays.snoc h o⟩

/-- The operations of a history that have returned, with their responses, in order. -/
def completedOps (H : History Unit O Resp) : List (O × Resp) :=
  (returnedOps H).map fun x => (x.1.op, x.2)

/-- The invariant of the one-process construction at time `t`. The automaton knows the pending
operation; every record lies in the past; each record returned before the next was invoked; all
records but a last, pending one have returned; and the returned operations replay to the
automaton's state. -/
def SeqInv (c : ImplConfig Unit Unit Unit (Q × Option O) O) (H : History Unit O Resp)
    (t : ℕ) : Prop :=
  (c.proc ()).state.2 = (c.proc ()).pending ∧
    (∀ a ∈ H, a.invokedAt < t ∧ ∀ r t', a.returned = some (r, t') → a.invokedAt < t' ∧ t' < t) ∧
    H.Pairwise (fun a b => ∃ r t', a.returned = some (r, t') ∧ t' < b.invokedAt) ∧
    ((c.proc ()).pending = none → ∀ a ∈ H, a.returned.isSome) ∧
    (∀ o, (c.proc ()).pending = some o →
      ∃ H' tp, H = H' ++ [⟨(), o, tp, none⟩] ∧ ∀ a ∈ H', a.returned.isSome) ∧
    Replays obj obj.initial (completedOps H) (c.proc ()).state.1

/-- Invoking the idle process records the operation in its local state. -/
theorem seqImpl_invoke_idle (c : ImplConfig Unit Unit Unit (Q × Option O) O) (o : O)
    (hp : (c.proc ()).pending = none) :
    (seqImpl obj).act c (.invoke () o) =
        ⟨c.memory, fun _ => ⟨((c.proc ()).state.1, some o), some o, (c.proc ()).done⟩⟩ ∧
      (seqImpl obj).event c (.invoke () o) = some (.inv () o) := by
  refine ⟨?_, by simp [event, hp]⟩
  simp only [act, hp]
  congr 1
  funext u
  cases u
  simp [seqImpl]

/-- A step of the busy process applies its operation and returns the sequential response. -/
theorem seqImpl_step_busy (c : ImplConfig Unit Unit Unit (Q × Option O) O) {o : O}
    (hp : (c.proc ()).pending = some o) (hs : (c.proc ()).state.2 = some o) :
    (seqImpl obj).act c (.step ()) =
        ⟨fun _ => (), fun _ => ⟨((obj.transition o (c.proc ()).state.1).2, none), none,
          (c.proc ()).done + 1⟩⟩ ∧
      (seqImpl obj).event c (.step ()) =
        some (.res () (obj.transition o (c.proc ()).state.1).1) := by
  refine ⟨?_, by simp [event, hp, stepResult, seqImpl, seqRespond, hs]⟩
  simp only [act, hp]
  congr 1
  funext u
  cases u
  simp [stepResult, seqImpl, seqRespond, hs, ProcState.after]

/-- The invariant holds initially, with an empty history. -/
theorem seqInv_initial : SeqInv obj (seqImpl obj).initial [] 0 := by
  refine ⟨rfl, by simp, List.Pairwise.nil, fun _ => by simp, fun o h => ?_, rfl⟩
  simp [initial] at h

/-- The invariant survives every action, with the event it records. -/
theorem seqInv_act {c : ImplConfig Unit Unit Unit (Q × Option O) O} {H : History Unit O Resp}
    {t : ℕ} (h : SeqInv obj c H t) (a : Action Unit O) :
    SeqInv obj ((seqImpl obj).act c a) (H.record t ((seqImpl obj).event c a)) (t + 1) := by
  obtain ⟨hst, htime, hpw, hidle, hbusy, hrep⟩ := h
  have hlater : ∀ a ∈ H, a.invokedAt < t + 1 ∧
      ∀ r t', a.returned = some (r, t') → a.invokedAt < t' ∧ t' < t + 1 := fun a ha =>
    ⟨by have := (htime a ha).1; omega, fun r t' hr => by
      have := (htime a ha).2 r t' hr; omega⟩
  -- Actions that change nothing: invoking a busy process, or `.step` of an idle one.
  have hsame : ∀ a', (seqImpl obj).act c a' = c → (seqImpl obj).event c a' = none →
      SeqInv obj ((seqImpl obj).act c a') (H.record t ((seqImpl obj).event c a')) (t + 1) := by
    intro a' hc he
    rw [hc, he]
    exact ⟨hst, hlater, hpw, hidle, hbusy, hrep⟩
  cases a with
  | invoke u o =>
    cases hp : (c.proc ()).pending with
    | some o' => exact hsame _ (by simp [act, hp]) (by simp [event, hp])
    | none =>
      obtain ⟨hc, he⟩ := seqImpl_invoke_idle obj c o hp
      rw [hc, he]
      simp only [History.record]
      have hret := hidle hp
      refine ⟨rfl, ?_, ?_, fun h => by simp at h, fun o' h => ?_, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hlater a ha
        · simp
      · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        obtain ⟨⟨r, t'⟩, hrt⟩ := Option.isSome_iff_exists.mp (hret a ha)
        exact ⟨r, t', hrt, ((htime a ha).2 r t' hrt).2⟩
      · obtain rfl : o' = o := by simpa using h.symm
        exact ⟨H, t, rfl, hret⟩
      · simpa [completedOps, returnedOps, List.filterMap_append] using hrep
  | step u =>
    cases hp : (c.proc ()).pending with
    | none => exact hsame _ (by simp [act, hp]) (by simp [event, hp])
    | some o =>
      have hs : (c.proc ()).state.2 = some o := hst.trans hp
      obtain ⟨hc, he⟩ := seqImpl_step_busy obj c hp hs
      rw [hc, he]
      obtain ⟨H', tp, rfl, hret⟩ := hbusy o hp
      -- The response closes the pending record: every earlier record has already returned.
      have hmap : History.record (H' ++ [(⟨(), o, tp, none⟩ : OpRecord Unit O Resp)]) t
          (some (.res () (obj.transition o (c.proc ()).state.1).1)) =
          H' ++ [⟨(), o, tp, some ((obj.transition o (c.proc ()).state.1).1, t)⟩] := by
        simp only [History.record, List.map_append]
        congr 1
        conv_rhs => rw [← List.map_id H']
        apply List.map_congr_left
        intro a ha
        have := hret a ha
        simp_all [Option.isSome_iff_ne_none]
      rw [hmap]
      have htp : tp < t := (htime _ (List.mem_append_right _ (List.mem_singleton_self _))).1
      obtain ⟨hpw', -, hcross⟩ := List.pairwise_append.mp hpw
      refine ⟨rfl, ?_, ?_, fun _ a ha => ?_, fun o' h => by simp at h, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hlater a (List.mem_append_left _ ha)
        · refine ⟨show tp < t + 1 by omega, fun r t' h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨htp, by omega⟩
      · refine List.pairwise_append.mpr ⟨hpw', List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact hcross a ha ⟨(), o, tp, none⟩ (List.mem_singleton_self _)
      · simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hret a ha
        · rfl
      · have hrep' : Replays obj obj.initial (completedOps H') (c.proc ()).state.1 := by
          simpa [completedOps, returnedOps, List.filterMap_append] using hrep
        simpa [completedOps, returnedOps, List.filterMap_append] using hrep'.snoc o

/-- The invariant holds along every finite execution, for the history it records. -/
theorem seqInv_recordRun : ∀ (acts : List (Action Unit O))
    (c : ImplConfig Unit Unit Unit (Q × Option O) O) (H : History Unit O Resp) (t : ℕ),
    SeqInv obj c H t →
      SeqInv obj ((seqImpl obj).run c acts) ((seqImpl obj).recordRun t c H acts) (t + acts.length)
  | [], _, _, _, h => h
  | a :: as, c, H, t, h => by
    have := seqInv_recordRun as _ _ _ (seqInv_act obj h a)
    simpa [Implementation.run, recordRun, Nat.add_assoc, Nat.add_comm 1] using this

/-- The one-process construction is linearizable: its history is sequential, and the
linearization is the list of returned operations in order. -/
theorem seqImpl_linearizable : (seqImpl obj).Linearizable obj := by
  intro acts
  obtain ⟨-, htime, hpw, -, -, hrep⟩ := seqInv_recordRun obj acts _ [] 0 (seqInv_initial obj)
  refine ⟨_, isLinearization_returnedOps ?_ (fun a ha r t hr => ((htime a ha).2 r t hr).1)
    hrep.legal⟩
  -- Each record returned before the next was invoked, so they are in order of invocation.
  exact hpw.imp_of_mem fun ha _ ⟨r, t', hr, hlt⟩ => by
    have := ((htime _ ha).2 r t' hr).1
    omega

/-- Every action preserves the fact that the automaton knows the pending operation. -/
theorem seqImpl_act_state_pending (c : ImplConfig Unit Unit Unit (Q × Option O) O)
    (h : (c.proc ()).state.2 = (c.proc ()).pending) (a : Action Unit O) :
    (((seqImpl obj).act c a).proc ()).state.2 = (((seqImpl obj).act c a).proc ()).pending := by
  rcases a with ⟨⟨⟩, o⟩ | ⟨⟨⟩⟩ <;> cases hp : (c.proc ()).pending
  · rw [(seqImpl_invoke_idle obj c o hp).1]
  · simpa [act, hp] using h
  · simpa [act, hp] using h
  · rw [(seqImpl_step_busy obj c hp (h.trans hp)).1]

/-- Along any execution, the automaton knows the pending operation. -/
theorem seqImpl_state_pending (α : ℕ → Action Unit O) : ∀ m,
    (((seqImpl obj).execution (seqImpl obj).initial α m).proc ()).state.2 =
      (((seqImpl obj).execution (seqImpl obj).initial α m).proc ()).pending
  | 0 => rfl
  | m + 1 => seqImpl_act_state_pending obj _ (seqImpl_state_pending α m) (α m)

/-- The one-process construction is wait-free: a pending operation returns at the next step of
the process. -/
theorem seqImpl_waitFree : (seqImpl obj).WaitFree :=
  waitFree_of_steps_return _ fun α m u _ ho => by
    cases u
    rw [(seqImpl_step_busy obj _ ho ((seqImpl_state_pending obj α m).trans ho)).1]

/-- **A COF universal construction exists for one process**: the process runs the sequential
specification itself. -/
theorem cofUniversal_unit : COFUniversal.{0, 0, 0, 0} Unit := fun _ _ _ obj =>
  ⟨Unit, Unit, _, seqImpl obj, seqImpl_linearizable obj, waitFree_imp_cof (seqImpl_waitFree obj)⟩

end OneProcess

/-! ## A linearizable, COF implementation with three processes -/

section ThreeProcesses

/-- The object with one state, one operation and one response. -/
def unitObj : Object Unit Unit Unit := ⟨(), fun _ _ => ((), ())⟩

/-- Every process answers at its first step. -/
def eager : Implementation (Fin 3) Unit Unit Unit Unit Unit where
  initialMemory _ := ()
  initialState _ := ()
  invoke _ _ s := s
  instruction _ _ := .write () () ((), some ())

/-! ### Linearizability -/

/-- Invariant of recorded histories at time `t`: records in strictly increasing invocation
order, all in the past, each returned after it was invoked. -/
def HInv (H : History (Fin 3) Unit Unit) (t : ℕ) : Prop :=
  H.Pairwise (fun a b => a.invokedAt < b.invokedAt) ∧
  ∀ a ∈ H, a.invokedAt < t ∧ ∀ r t', a.returned = some (r, t') → a.invokedAt < t' ∧ t' < t

theorem hinv_record {H : History (Fin 3) Unit Unit} {t : ℕ} (h : HInv H t)
    (e : Option (Event (Fin 3) Unit Unit)) : HInv (H.record t e) (t + 1) := by
  obtain ⟨hpw, htime⟩ := h
  have hlater : ∀ a ∈ H, a.invokedAt < t + 1 ∧
      ∀ r t', a.returned = some (r, t') → a.invokedAt < t' ∧ t' < t + 1 := fun a ha =>
    ⟨by have := (htime a ha).1; omega, fun r t' hr => by have := (htime a ha).2 r t' hr; omega⟩
  rcases e with _ | ⟨p, o⟩ | ⟨p, r⟩
  · exact ⟨hpw, hlater⟩
  · refine ⟨List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [List.mem_singleton.mp hb]
      exact (htime a ha).1
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hlater a ha
      · rw [List.mem_singleton.mp ha]; simp
  · simp only [History.record]
    refine ⟨?_, ?_⟩
    · refine List.pairwise_map.mpr (hpw.imp fun {a b} hab => ?_)
      split <;> split <;> simpa using hab
    · intro a' ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      split
      · refine ⟨by have := (htime a ha).1; simp; omega, fun r' t' h => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨(htime a ha).1, by omega⟩
      · exact hlater a ha

theorem hinv_recordRun : ∀ (acts : List (Action (Fin 3) Unit))
    (c : ImplConfig (Fin 3) Unit Unit Unit Unit) (H : History (Fin 3) Unit Unit) (t : ℕ), HInv H t →
    HInv (eager.recordRun t c H acts) (t + acts.length)
  | [], _, _, _, h => h
  | a :: as, c, H, t, h => by
    have := hinv_recordRun as (eager.act c a) _ (t + 1) (hinv_record h (eager.event c a))
    simpa [recordRun, Nat.add_assoc, Nat.add_comm 1] using this

theorem legal_unit : ∀ L : List (Unit × Unit), unitObj.Legal () L
  | [] => trivial
  | _ :: L => ⟨rfl, legal_unit L⟩

theorem eager_linearizable : eager.Linearizable unitObj := by
  intro acts
  obtain ⟨hpw, htime⟩ := hinv_recordRun acts eager.initial [] 0 ⟨List.Pairwise.nil, by simp⟩
  exact ⟨_, isLinearization_returnedOps hpw (fun a ha r t hr => ((htime a ha).2 r t hr).1)
    (legal_unit _)⟩

/-! ### Conflict-obstruction freedom (indeed wait freedom) -/

/-- A step of a busy process returns its operation. -/
theorem step_done (c : ImplConfig (Fin 3) Unit Unit Unit Unit) (p : Fin 3) {o : Unit}
    (h : (c.proc p).pending = some o) :
    ((eager.act c (.step p)).proc p).done = (c.proc p).done + 1 := by
  simp only [act, h]
  simp [stepResult, eager, ProcState.after, Function.update]

theorem eager_waitFree : eager.WaitFree :=
  waitFree_of_steps_return eager fun _ _ p _ ho => step_done _ p ho

/-- **Non-vacuity with three processes**: linearizable and COF, for the one-state object. -/
theorem eager_linearizable_cof :
    eager.Linearizable unitObj ∧ eager.ConflictObstructionFree unitObj.Conflict :=
  ⟨eager_linearizable, waitFree_imp_cof eager_waitFree⟩

/-- The one-state object has no conflicts, so COF is exactly wait freedom here (paper §3). -/
theorem unitObj_no_conflict (a b : Unit) : ¬ unitObj.Conflict a b := by
  rintro ⟨s, h⟩; exact h ⟨rfl, rfl, rfl⟩

end ThreeProcesses

end COF.Checks
