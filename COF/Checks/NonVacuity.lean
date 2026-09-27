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
-/

namespace COF.Checks
open SharedMemory SharedMemory.Implementation

/-- The returned instances of a history, in order, form a sublist of it. -/
theorem filterMap_returned_sublist {P O Resp : Type*} (H : History P O Resp) :
    ((H.filterMap fun a => a.returned.map fun x => (a, x.1)).map Prod.fst).Sublist H := by
  induction H with
  | nil => simp
  | cons a H ih =>
    cases h : a.returned with
    | none => simpa [h] using ih.cons a
    | some x => simpa [h] using ih.cons_cons a

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
  simp [Algorithm.initial]
  rfl

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
  H.filterMap fun a => a.returned.map fun x => (a.op, x.1)

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
      (seqImpl obj (Resp := Resp)).event c (.invoke () o) = some (.inv () o) := by
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
theorem seqInv_initial : SeqInv obj (seqImpl obj (Resp := Resp)).initial [] 0 := by
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
  -- Actions that change nothing: invoking a busy process, or scheduling an idle one.
  have hsame : ∀ a', (seqImpl obj).act c a' = c → (seqImpl obj (Resp := Resp)).event c a' = none →
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
      · simpa [completedOps, List.filterMap_append] using hrep
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
        obtain ⟨r, t', h1, h2⟩ := hcross a ha ⟨(), o, tp, none⟩ (List.mem_singleton_self _)
        exact ⟨r, t', h1, h2⟩
      · simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hret a ha
        · rfl
      · have hrep' : Replays obj obj.initial (completedOps H') (c.proc ()).state.1 := by
          simpa [completedOps, List.filterMap_append] using hrep
        simpa [completedOps, List.filterMap_append] using hrep'.snoc o

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
  obtain ⟨-, htime, hpw, -, -, hrep⟩ :=
    seqInv_recordRun obj acts _ [] 0 (seqInv_initial obj (Resp := Resp))
  refine ⟨((seqImpl obj).history acts).filterMap fun a => a.returned.map fun x => (a, x.1),
    ?_, ?_, ?_, ?_, ?_⟩
  · have hnd : ((seqImpl obj).history acts).Nodup :=
      hpw.imp_of_mem fun {a b} ha _ ⟨r, t', hr, hlt⟩ hab => by
        subst hab
        have := ((htime a ha).2 r t' hr).1
        omega
    exact hnd.sublist (filterMap_returned_sublist _)
  · intro x hx
    obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hax
    exact ha
  · intro a ha r t hr
    exact List.mem_filterMap.mpr ⟨a, ha, by simp [hr]⟩
  · have : (((seqImpl obj).history acts).filterMap fun a => a.returned.map fun x => (a, x.1)).map
        (fun x => (x.1.op, x.2)) = completedOps ((seqImpl obj).history acts) := by
      simp [completedOps, List.map_filterMap, Option.map_map, Function.comp_def]
    rw [this]
    exact hrep.legal
  · intro x y hxy r t hy
    have hsub := (hxy.map Prod.fst).trans (filterMap_returned_sublist _)
    have hmem : ∀ z ∈ [x.1, y.1], z ∈ (seqImpl obj).history acts := fun z hz => hsub.subset hz
    obtain ⟨r', t', hx', hlt⟩ := List.rel_of_pairwise_cons (hpw.sublist hsub)
      (List.mem_singleton_self _)
    have h1 := ((htime x.1 (hmem _ (by simp))).2 r' t' hx').1
    have h2 := ((htime y.1 (hmem _ (by simp))).2 r t hy).1
    omega

/-- Along any execution, the automaton knows the pending operation. -/
theorem seqImpl_state_pending (α : ℕ → Action Unit O) : ∀ m,
    (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc ()).state.2 =
      (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc ()).pending
  | 0 => rfl
  | m + 1 => by
    have ih := seqImpl_state_pending α m
    change ((((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).state.2 =
      (((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).pending)
    cases α m with
    | invoke u o =>
      cases u
      cases hp : (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc
          ()).pending with
      | none =>
        rw [(seqImpl_invoke_idle obj _ o hp).1]
      | some _ => simpa [act, hp] using ih
    | step u =>
      cases u
      cases hp : (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc
          ()).pending with
      | none => simpa [act, hp] using ih
      | some o => rw [(seqImpl_step_busy obj _ hp (ih.trans hp)).1]

/-- After an invocation at time `t`, the operation stays pending until the process's next step,
which returns it. -/
theorem seqImpl_after_invoke (α : ℕ → Action Unit O) {t k : ℕ} {o : O}
    (hat : α t = .invoke () o)
    (hpt : (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α t).proc ()).pending =
      none)
    (hdt : (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α t).proc ()).done = k) :
    ∀ m, t < m →
      k < (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc ()).done ∨
      ((((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc ()).pending.isSome ∧
        (((seqImpl obj (Resp := Resp)).execution (seqImpl obj).initial α m).proc ()).done = k) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    change k < (((seqImpl obj).act (Implementation.execution _ _ α t) (α t)).proc ()).done ∨
      ((((seqImpl obj).act (Implementation.execution _ _ α t) (α t)).proc ()).pending.isSome ∧
        (((seqImpl obj).act (Implementation.execution _ _ α t) (α t)).proc ()).done = k)
    rw [hat, (seqImpl_invoke_idle obj _ o hpt).1]
    exact Or.inr ⟨rfl, hdt⟩
  | succ m _ ih =>
    change k < (((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).done ∨
      ((((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).pending.isSome ∧
        (((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).done = k)
    rcases ih with hk | ⟨hb, hd⟩
    · exact Or.inl (lt_of_lt_of_le hk ((seqImpl obj).done_le_act _ _ _))
    · obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      cases α m with
      | invoke u _ =>
        cases u
        simp only [act, ho']
        exact Or.inr ⟨rfl, hd⟩
      | step u =>
        cases u
        rw [(seqImpl_step_busy obj _ ho' ((seqImpl_state_pending obj α m).trans ho')).1]
        exact Or.inl (by simp [hd])

/-- The one-process construction is conflict-obstruction-free — indeed wait-free: a pending
operation of a correct process returns at its next step. -/
theorem seqImpl_cof (conflict : O → O → Prop) :
    (seqImpl obj (Resp := Resp)).ConflictObstructionFree conflict := by
  rintro _ ⟨α, rfl⟩ ⟨u, k, o⟩ ⟨t, hat, hpt, hdt⟩ hcorr -
  cases u
  have key := seqImpl_after_invoke obj α hat hpt hdt
  rcases hcorr with hsteps | ⟨N, hidle⟩
  · obtain ⟨m, hm, hstep, hbusy⟩ := hsteps (t + 1)
    rcases key m (by omega) with hk | ⟨hb, hd⟩
    · exact ⟨m, hk⟩
    · refine ⟨m + 1, ?_⟩
      change k < (((seqImpl obj).act (Implementation.execution _ _ α m) (α m)).proc ()).done
      obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      rw [hstep, (seqImpl_step_busy obj _ ho' ((seqImpl_state_pending obj α m).trans ho')).1]
      simp [hd]
  · rcases key (max N (t + 1)) (by omega) with hk | ⟨hb, -⟩
    · exact ⟨_, hk⟩
    · simp [hidle _ (Nat.le_max_left _ _)] at hb

/-- **A COF universal construction exists for one process**: the process runs the sequential
specification itself. -/
theorem cofUniversal_unit : COFUniversal.{0, 0, 0, 0} Unit := fun _ _ _ obj =>
  ⟨Unit, Unit, _, seqImpl obj, seqImpl_linearizable obj, seqImpl_cof obj _⟩

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
  · classical
    simp only [History.record]
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
  refine ⟨(eager.history acts).filterMap fun a => a.returned.map fun x => (a, x.1),
    ?_, ?_, ?_, legal_unit _, ?_⟩
  · have hnd : (eager.history acts).Nodup := hpw.imp fun {a b} h hab => by subst hab; omega
    exact hnd.sublist (filterMap_returned_sublist _)
  · intro x hx
    obtain ⟨a, ha, hax⟩ := List.mem_filterMap.mp hx
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hax
    exact ha
  · intro a ha r t hr
    exact List.mem_filterMap.mpr ⟨a, ha, by simp [hr]⟩
  · intro x y hxy r t hy
    have hsub := (hxy.map Prod.fst).trans (filterMap_returned_sublist _)
    have hlt := List.rel_of_pairwise_cons (hpw.sublist hsub) (List.mem_singleton_self _)
    have := ((htime y.1 (hsub.subset (by simp))).2 r t hy).1
    omega

/-! ### Conflict-obstruction freedom (indeed wait freedom) -/

theorem act_other {c : ImplConfig (Fin 3) Unit Unit Unit Unit} {a : Action (Fin 3) Unit}
    {p : Fin 3} (hp : ∀ o, a ≠ .invoke p o) (hs : a ≠ .step p) :
    (eager.act c a).proc p = c.proc p := by
  classical
  cases a with
  | invoke q o =>
    have hq : p ≠ q := fun h => hp o (by rw [h])
    cases h : (c.proc q).pending <;> simp [act, h, Function.update, hq]
  | step q =>
    have hq : p ≠ q := fun h => hs (by rw [h])
    cases h : (c.proc q).pending <;> simp [act, h, Function.update, hq]

/-- A step of a busy process returns its operation. -/
theorem step_done (c : ImplConfig (Fin 3) Unit Unit Unit Unit) (p : Fin 3) {o : Unit}
    (h : (c.proc p).pending = some o) :
    ((eager.act c (.step p)).proc p).done = (c.proc p).done + 1 := by
  simp only [act, h]
  simp [stepResult, eager, ProcState.after, Function.update]

/-- After `p` is invoked at `t` with `k` returned operations, it stays pending with `k`
returned operations until its operation returns. -/
theorem after_invoke (α : ℕ → Action (Fin 3) Unit) {p : Fin 3} {t k : ℕ} {o : Unit}
    (hat : α t = .invoke p o)
    (hpt : ((eager.execution eager.initial α t).proc p).pending = none)
    (hdt : ((eager.execution eager.initial α t).proc p).done = k) :
    ∀ m, t < m → k < ((eager.execution eager.initial α m).proc p).done ∨
      (((eager.execution eager.initial α m).proc p).pending.isSome ∧
        ((eager.execution eager.initial α m).proc p).done = k) := by
  classical
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    right
    change ((eager.act _ (α t)).proc p).pending.isSome ∧ ((eager.act _ (α t)).proc p).done = k
    rw [hat]
    simp [act, hpt, hdt]
  | succ m _ ih =>
    change k < ((eager.act _ (α m)).proc p).done ∨
      (((eager.act _ (α m)).proc p).pending.isSome ∧ ((eager.act _ (α m)).proc p).done = k)
    rcases ih with hk | ⟨hb, hd⟩
    · exact Or.inl (lt_of_lt_of_le hk (eager.done_le_act _ _ _))
    · obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      by_cases hs : α m = .step p
      · left
        rw [hs, step_done _ _ ho', hd]
        omega
      · by_cases hi : ∃ o, α m = .invoke p o
        · obtain ⟨o, ho⟩ := hi
          right
          rw [ho]
          simp only [act, ho']
          exact ⟨by simp, hd⟩
        · push Not at hi
          right
          rw [act_other hi hs]
          exact ⟨hb, hd⟩

theorem eager_waitFree : eager.WaitFree := by
  rintro _ ⟨α, rfl⟩ ⟨p, k, o⟩ ⟨t, hat, hpt, hdt⟩ hcorr
  dsimp only [trace, StepsAt] at hat hpt hdt hcorr ⊢
  have key := after_invoke α hat hpt hdt
  rcases hcorr with hsteps | ⟨N, hidle⟩
  · obtain ⟨m, hm, hstep, hbusy⟩ := hsteps (t + 1)
    rcases key m (by omega) with hk | ⟨hb, hd⟩
    · exact ⟨m, hk⟩
    · refine ⟨m + 1, ?_⟩
      change k < ((eager.act _ (α m)).proc p).done
      obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hb
      rw [hstep, step_done _ _ ho']
      omega
  · rcases key (max N (t + 1)) (by omega) with hk | ⟨hb, -⟩
    · exact ⟨_, hk⟩
    · simp [hidle _ (Nat.le_max_left _ _)] at hb

/-- **Non-vacuity with three processes**: linearizable and COF, for the one-state object. -/
theorem eager_linearizable_cof :
    eager.Linearizable unitObj ∧ eager.ConflictObstructionFree unitObj.Conflict :=
  ⟨eager_linearizable, waitFree_imp_cof eager_waitFree⟩

/-- The one-state object has no conflicts, so COF is exactly wait freedom here (paper §3). -/
theorem unitObj_no_conflict (a b : Unit) : ¬ unitObj.Conflict a b := by
  rintro ⟨s, h⟩; exact h ⟨rfl, rfl, rfl⟩

end ThreeProcesses

end COF.Checks
