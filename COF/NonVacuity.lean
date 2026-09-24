import COF

/-! Non-vacuity checks for the impossibility result.

These make precise two claims that the impossibility theorem would be empty
without:

1. `consensus_satisfiable` — `Safe ∧ COFTermination` is satisfiable, so
   `no_cof_consensus` is not vacuously true because its hypotheses contradict
   each other. The witness is a one-process system in which the process decides
   its own input.

2. `alt_not_homogeneous` — the COF liveness hypothesis genuinely exempts some
   schedules, so `COFTermination` is strictly weaker than wait-free termination
   and the impossibility is not a restatement of FLP.

See `MODEL.md`. -/

namespace COF.NonVacuity
open COF COF.SharedMemory

/-- One process, one register, trivial values, local state = own proposal, decided at the
first step. This is the trivial algorithm `Algorithm.decideOwnInput` (`COF/Tightness.lean`),
which is proved safe and COF-terminating for every system of at most one process. -/
abbrev solo : Algorithm Unit Unit Unit Bool := Algorithm.decideOwnInput Unit

/-- **The hypotheses of the impossibility theorem are jointly satisfiable.** -/
theorem consensus_satisfiable : ∃ a : Algorithm Unit Unit Unit Bool, a.Consensus :=
  ⟨solo, Algorithm.decideOwnInput_consensus⟩

/-- Sanity check that decisions really are reachable in this witness, i.e. `Safe`
is not satisfied merely because nothing ever decides. -/
theorem solo_decides :
    ((solo.run (solo.initial (fun _ => true)) [()]).proc ()).decision = some true :=
  rfl


/-- Two processes with opposite proposals. -/
def two : Bool → Bool := id

/-- The alternating schedule. -/
def alt : ℕ → Bool := fun k => k % 2 == 0

/-- The alternating schedule is *not* eventually homogeneous, hence
`COFTermination` imposes no requirement whatsoever on it, while wait-free
termination would. -/
theorem alt_not_homogeneous : ¬ ∃ N v, ∀ k ≥ N, two (alt k) = v := by
  rintro ⟨N, v, h⟩
  have h1 := h (2 * N) (by omega)
  have h2 := h (2 * N + 1) (by omega)
  have m1 : (2 * N) % 2 = 0 := by omega
  have m2 : (2 * N + 1) % 2 = 1 := by omega
  rw [show alt (2 * N) = true by simp [alt, m1]] at h1
  rw [show alt (2 * N + 1) = false by simp [alt, m2]] at h2
  cases v <;> simp [two] at h1 h2

/-- Restated: for every algorithm, `COFTermination` says nothing about the
alternating schedule, so it cannot entail termination under all schedules. -/
theorem cofTermination_silent_on_alt
    {R V S : Type} [DecidableEq R] (a : Algorithm Bool R V S)
    (_ : a.COFTermination) :
    ¬ ∃ N v, ∀ k ≥ N, two (alt k) = v := alt_not_homogeneous

/-! ### The full universal-construction notions are satisfiable

With a single process, a COF universal construction exists: the process keeps the object's state
itself and answers each operation at its first step. So `COFUniversal` is not refuted by its
definitions alone, and `no_cofUniversal` really needs its three processes. -/

section OneProcess
open SharedMemory.Implementation

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

/-- The returned instances of a history, in order, form a sublist of it. -/
theorem filterMap_returned_sublist (H : History Unit O Resp) :
    ((H.filterMap fun a => a.returned.map fun x => (a, x.1)).map Prod.fst).Sublist H := by
  induction H with
  | nil => simp
  | cons a H ih =>
    cases h : a.returned with
    | none => simpa [h] using ih.cons a
    | some x => simpa [h] using ih.cons_cons a

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

/-- **The full universal-construction notions are satisfiable.** With one process, a COF
universal construction exists: the process runs the sequential specification itself. -/
theorem cofUniversal_unit : COFUniversal Unit := fun _ _ _ obj =>
  ⟨Unit, Unit, _, inferInstance, seqImpl obj, seqImpl_linearizable obj, seqImpl_cof obj _⟩

end OneProcess

end COF.NonVacuity
