import COF.Termination
import COF.SharedMemory.Commutation

/-! The bivalent-successor lemma for two active processes sharing an input. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

theorem reachable_step {input : P → Bool} {c : Config P R V S}
    (hr : a.Reachable input c) (p : P) : a.Reachable input (a.step c p) :=
  a.reachable_run hr [p]

omit [DecidableEq P] [DecidableEq R] in
theorem Indist.restrict {active other : Set P} {c d : Config P R V S}
    (h : Indist active c d) (hs : other ⊆ active) : Indist other c d :=
  ⟨h.1, fun p hp => h.2 p (hs hp)⟩

/-- Two different processes cannot have oppositely valent immediate successors. -/
theorem successor_valencies_eq (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q : P} {v w : Bool}
    (hr : a.Reachable input c) (hp : p ∈ active) (hq : q ∈ active) (hne : p ≠ q)
    (hv : a.Valent active (a.step c p) v) (hw : a.Valent active (a.step c q) w) : v = w := by
  have hvq := a.valent_mono hv (Reach.single a _ hq)
  have hwp := a.valent_mono hw (Reach.single a _ hp)
  rcases a.commutation_or_erasure c hne with he | he | he
  · exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) hp
      ⟨congrArg Config.memory he, fun r _ => congrArg (fun c => c.proc r) he⟩ hvq hwp
  · exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) hq
      (he.restrict (by simpa using hne.symm)) hvq hw
  · exact (a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr q) p) hp
      (he.restrict (by simpa using hne)) hwp hv).symm

/-- If every active successor has the same valency, so does its predecessor. -/
theorem valent_of_successors {active : Set P} (hne : active.Nonempty)
    {c : Config P R V S} {v : Bool}
    (h : ∀ p ∈ active, a.Valent active (a.step c p) v) : a.Valent active c v := by
  rintro ⟨d, ⟨ps, hps, rfl⟩, hd⟩
  cases ps with
  | nil =>
    obtain ⟨p, hp⟩ := hne
    exact h p hp ⟨a.step c p, Reach.refl a _ _, a.decided_run hd [p]⟩
  | cons p ps =>
    exact h p (hps p (by simp)) ⟨a.run (a.step c p) ps,
      ⟨ps, fun q hq => hps q (by simp [hq]), rfl⟩, hd⟩

/-- Paper Lemma `bivalent_to_bivalent`. No fairness of the choice is assumed. -/
theorem bivalent_successor (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} {p q : P} (hne : p ≠ q)
    (hr : a.Reachable input c) (hb : a.Bivalent {p, q} c) :
    a.Bivalent {p, q} (a.step c p) ∨ a.Bivalent {p, q} (a.step c q) := by
  by_contra hn
  have hu : a.Univalent {p, q} (a.step c p) ∧ a.Univalent {p, q} (a.step c q) := by
    simpa only [not_or, Bivalent, not_not] using hn
  have eqv := fun v w => a.successor_valencies_eq ht (active := {p, q})
    (v := v) (w := w) hr (by simp) (by simp) hne
  rcases hu with ⟨hp | hp, hq | hq⟩
  · apply hb; left
    apply a.valent_of_successors ⟨p, by simp⟩
    intro r hmem
    rcases (show r = p ∨ r = q by simpa using hmem) with rfl | rfl <;> assumption
  · cases eqv false true hp hq
  · cases eqv true false hp hq
  · apply hb; right
    apply a.valent_of_successors ⟨p, by simp⟩
    intro r hmem
    rcases (show r = p ∨ r = q by simpa using hmem) with rfl | rfl <;> assumption

end COF.SharedMemory.Algorithm
