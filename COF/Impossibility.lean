import COF.InitialBivalence

/-! The main impossibility theorem. The infinite bivalent execution may starve one
of its two active processes; at least one is infinitely scheduled, which suffices
for the contradiction with COF termination. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

omit [DecidableEq P] in
/-- An infinite sequence taking only two values takes at least one infinitely often. -/
theorem two_process_infinite (schedule : ℕ → P) (p q : P)
    (hs : ∀ n, schedule n = p ∨ schedule n = q) :
    (∀ N, ∃ k ≥ N, schedule k = p) ∨ (∀ N, ∃ k ≥ N, schedule k = q) := by
  by_cases hp : ∀ N, ∃ k ≥ N, schedule k = p
  · exact Or.inl hp
  · right
    push Not at hp
    obtain ⟨N, hN⟩ := hp
    intro M
    refine ⟨max N M, le_max_right _ _, ?_⟩
    exact (hs _).resolve_left (hN _ (le_max_left _ _))

/-- A reachable bivalent state is incompatible with COF termination when its two
active processes have the same input. -/
theorem no_bivalent (hs : a.Safe) (ht : a.COFTermination) {input : P → Bool}
    {p q : P} (hne : p ≠ q) (hin : input p = input q)
    {c : Config P R V S} (hr : a.Reachable input c) (hb : a.Bivalent {p, q} c) : False := by
  classical
  let K := {d : Config P R V S // a.Reachable input d ∧ a.Bivalent {p, q} d}
  have successor : ∀ d : K, ∃ t : P, (t = p ∨ t = q) ∧ a.Bivalent {p, q} (a.step d.val t) := by
    intro d
    rcases a.bivalent_successor ht hne d.property.1 d.property.2 with h | h
    · exact ⟨p, Or.inl rfl, h⟩
    · exact ⟨q, Or.inr rfl, h⟩
  choose pick hpick hbiv using successor
  let next : K → K := fun d => ⟨a.step d.val (pick d),
    a.reachable_step d.property.1 _, hbiv d⟩
  let states : ℕ → K := Nat.rec ⟨c, hr, hb⟩ (fun _ d => next d)
  let schedule : ℕ → P := fun n => pick (states n)
  have hexe : ∀ n, a.execution c schedule n = (states n).val := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change a.step (a.execution c schedule n) (schedule n) = a.step (states n).val (schedule n)
      rw [ih]
  have hhom : ∃ N v, ∀ k ≥ N, input (schedule k) = v := by
    refine ⟨0, input q, ?_⟩
    intro k _
    rcases hpick (states k) with h | h
    · exact (congrArg input h).trans hin
    · exact congrArg input h
  have hsome : ∃ t, ∀ N, ∃ k ≥ N, schedule k = t := by
    rcases two_process_infinite schedule p q (fun n => hpick (states n)) with h | h
    · exact ⟨p, h⟩
    · exact ⟨q, h⟩
  obtain ⟨t, htinf⟩ := hsome
  obtain ⟨n, v, hd⟩ := ht input c hr schedule hhom t htinf
  rw [hexe] at hd
  exact a.bivalent_not_decided hs (states n).property.1 (states n).property.2 v ⟨t, hd⟩

/-- Paper Theorem `no_quasi_cons`: three distinct processes suffice, irrespective
of how many other processes there are or whether they ever take steps. -/
theorem no_cof_consensus (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) : ¬ a.Consensus := by
  rintro ⟨hs, ht⟩
  obtain ⟨c, hr, hb⟩ := a.reachable_bivalent hs ht p₀ p₁ p₂ h₀₁ h₂₀ h₂₁
  exact a.no_bivalent hs ht h₂₁.symm
    (by simp [h₀₁.symm, h₂₀]) hr hb

/-- Numeric formulation for an arbitrary finite system of at least three processes. -/
theorem no_cof_consensus_fin {n : ℕ} (hn : 3 ≤ n) (a : Algorithm (Fin n) R V S) :
    ¬ a.Consensus := by
  exact a.no_cof_consensus ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by intro h; have := congrArg Fin.val h; simp at this)

end COF.SharedMemory.Algorithm
