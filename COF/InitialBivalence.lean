import COF.Bivalence

/-! A reachable bivalent configuration, obtained by moving a step of the excluded
process across a solo execution. The third process supplies the observer needed
for the indistinguishability argument. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- The square of steps in the proof of Lemma `init_tobivalent`. -/
theorem square_valency (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q r : P} {v w : Bool}
    (hr : a.Reachable input c) (hq : q ∈ active) (hobs : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hv : a.Valent active (a.step c p) v)
    (hw : a.Valent active (a.step c q) w)
    (hwp : a.Valent active (a.step (a.step c q) p) w) : v = w := by
  have hvq := a.valent_mono hv (Reach.single a _ hq)
  rcases a.commutation_or_erasure c hpq with he | he | he
  · exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) hobs
      ⟨congrArg Config.memory he, fun r _ => congrArg (fun c => c.proc r) he⟩ hvq hwp
  · exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) hobs
      (he.restrict (by simpa using hrp)) hvq hw
  · exact (a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr q) p) hobs
      (he.restrict (by simpa using hrq)) hwp hv).symm

/-- If all reachable configurations were univalent, an excluded process's step
could not change valency. -/
theorem external_step_preserves_valency (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {p q r : P} (hq : q ∈ active) (hobs : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {c : Config P R V S} {v : Bool} (hr : a.Reachable input c)
    (hv : a.Valent active c v) : a.Valent active (a.step c p) v := by
  have noflip : ¬ a.Valent active (a.step c p) (!v) := by
    intro hflip
    obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hr q
    have hreach : a.Reach active c (a.run c ps) :=
      ⟨ps, fun t ht => (hps t ht) ▸ hq, rfl⟩
    have hvb := a.valent_decision hv hreach ⟨q, hb⟩
    subst b
    have propagate : ∀ (xs : List P), (∀ t ∈ xs, t = q) →
        ∀ (d : Config P R V S), a.Reachable input d → a.Valent active d v →
        a.Valent active (a.step d p) (!v) →
        a.Valent active (a.step (a.run d xs) p) (!v) := by
      intro xs hxs
      induction xs with
      | nil => intro d _ _ hh; exact hh
      | cons t xs ih =>
        have htq := hxs t (by simp)
        subst t
        intro d hd hdv hdflip
        have hnext := a.valent_mono hdv (Reach.single a _ hq)
        have hn : ¬ a.Valent active (a.step (a.step d q) p) v := by
          intro hn
          have he := a.square_valency ht hd hq hobs hpq hrp hrq hdflip hnext hn
          cases v <;> cases he
        have hnflip : a.Valent active (a.step (a.step d q) p) (!v) := by
          have hu := hall _ (a.reachable_step (a.reachable_step hd q) p)
          cases v <;> simp_all only [Univalent, Bool.not_true, Bool.not_false, false_or,
            or_false]
        exact ih (fun t ht => hxs t (by simp [ht])) (a.step d q)
          (a.reachable_step hd q) hnext hnflip
    have hfinal := propagate ps hps c hr hv hflip
    have hb' := a.step_decision (a.run c ps) p q v hb
    exact hfinal ⟨a.step (a.run c ps) p, Reach.refl a _ _, by simpa using
      (show (a.step (a.run c ps) p).Decided v from ⟨q, hb'⟩)⟩
  have hu := hall _ (a.reachable_step hr p)
  cases v <;> simp_all only [Univalent, Bool.not_true, Bool.not_false, false_or, or_false]

/-- Paper Lemma `init_tobivalent`, generalized to any process type containing three
distinct processes. Processes other than these three need never be scheduled. -/
theorem reachable_bivalent (hs : a.Safe) (ht : a.COFTermination)
    (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) :
    let input : P → Bool := fun p => if p = p₀ then false else true
    ∃ c, a.Reachable input c ∧ a.Bivalent {p₁, p₂} c := by
  classical
  dsimp only
  let input : P → Bool := fun p => if p = p₀ then false else true
  change ∃ c, a.Reachable input c ∧ a.Bivalent {p₁, p₂} c
  by_contra hn
  have hall : ∀ c, a.Reachable input c → a.Univalent {p₁, p₂} c := by
    intro c hc
    by_contra hu
    exact hn ⟨c, hc, hu⟩
  have hi : a.Reachable input (a.initial input) := Reach.refl a _ _
  have hiv : a.Valent {p₁, p₂} (a.initial input) true := by
    apply a.initial_valent hs
    intro p hp
    rcases (show p = p₁ ∨ p = p₂ by simpa using hp) with rfl | rfl
    · simp [input, h₀₁.symm]
    · simp [input, h₂₀]
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hi p₀
  have hiv0 : a.Valent {p₀} (a.initial input) false := by
    apply a.initial_valent hs
    simp [input]
  have hb0 := a.valent_decision hiv0
    ⟨ps, by simpa using hps, rfl⟩ (show (a.run (a.initial input) ps).Decided b from ⟨p₀, hb⟩)
  subst b
  have preserve : ∀ (xs : List P), (∀ p ∈ xs, p = p₀) →
      ∀ c, a.Reachable input c → a.Valent {p₁, p₂} c true →
      a.Valent {p₁, p₂} (a.run c xs) true := by
    intro xs hxs
    induction xs with
    | nil => intro c _ hv; exact hv
    | cons p xs ih =>
      have hp := hxs p (by simp)
      subst p
      intro c hc hv
      exact ih (fun p hp => hxs p (by simp [hp])) _ (a.reachable_step hc p₀)
        (a.external_step_preserves_valency ht (q := p₁) (r := p₂)
          (by simp) (by simp) h₀₁ h₂₀ h₂₁ hall hc hv)
  exact preserve ps hps _ hi hiv
    ⟨a.run (a.initial input) ps, Reach.refl a _ _, p₀, hb⟩

end COF.SharedMemory.Algorithm
