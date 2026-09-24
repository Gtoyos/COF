import COF.InitialBivalence

/-! The main impossibility theorem. The infinite bivalent execution may starve one
of its two active processes; at least one is infinitely scheduled, which suffices
for the contradiction with COF termination. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- An infinite sequence taking only two values takes at least one infinitely often.

The bivalent schedule need not run both active processes infinitely often — it may starve
one of them. Only one infinitely scheduled process is needed for the contradiction, and
this supplies it. -/
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

/-- A reachable bivalent configuration is incompatible with COF termination, provided its
two active processes proposed the same value.

Iterating `bivalent_successor` from `c` builds an infinite execution through bivalent
configurations. Its schedule only ever runs `p` or `q`, who proposed the same value, so
it is homogeneous from the start and COF termination applies to it in full. At least one
of the two is scheduled infinitely often, so that process must decide — but no
configuration along the execution has anyone decided, since all of them are bivalent. -/
theorem no_bivalent (hs : a.Safe) (ht : a.COFTermination) {input : P → Bool}
    {p q : P} (hne : p ≠ q) (hin : input p = input q)
    {c : Config P R V S} (hr : a.Reachable input c) (hb : a.Bivalent {p, q} c) : False := by
  classical
  -- Reachable bivalent configurations, each of which has a bivalent successor.
  let K := {d : Config P R V S // a.Reachable input d ∧ a.Bivalent {p, q} d}
  have successor : ∀ d : K, ∃ t : P, (t = p ∨ t = q) ∧ a.Bivalent {p, q} (a.step d.val t) := by
    intro d
    rcases a.bivalent_successor ht hne d.property.1 d.property.2 with h | h
    · exact ⟨p, Or.inl rfl, h⟩
    · exact ⟨q, Or.inr rfl, h⟩
  -- Choosing one such successor everywhere turns that into an infinite execution.
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
  -- Only `p` and `q` ever step, and they proposed the same value.
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
  -- Liveness hands us a decision inside a bivalent configuration.
  obtain ⟨t, htinf⟩ := hsome
  obtain ⟨n, v, hd⟩ := ht input c hr schedule hhom t htinf
  rw [hexe] at hd
  exact a.bivalent_not_decided hs (states n).property.1 (states n).property.2 v ⟨t, hd⟩

/-- Paper Theorem `no_quasi_cons`: no deterministic asynchronous read/write algorithm
satisfies both consensus safety and COF termination. Three distinct process identifiers
suffice, irrespective of how many other processes there are or whether they ever take
steps.

`reachable_bivalent` produces a bivalent configuration for the input vector where only
`p₀` proposes `false`; `p₁` and `p₂` both propose `true`, which is the shared input
`no_bivalent` needs. -/
theorem no_cof_consensus (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) : ¬ a.Consensus := by
  rintro ⟨hs, ht⟩
  obtain ⟨c, hr, hb⟩ := a.reachable_bivalent hs ht p₀ p₁ p₂ h₀₁ h₂₀ h₂₁
  exact a.no_bivalent hs ht h₂₁.symm
    (by simp [h₀₁.symm, h₂₀]) hr hb

/-- Numeric formulation for an arbitrary finite system of at least three processes. -/
theorem no_cof_consensus_fin {n : ℕ} (hn : 3 ≤ n) (a : Algorithm (Fin n) R V S) :
    ¬ a.Consensus :=
  a.no_cof_consensus ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    (Fin.ne_of_val_ne (by simp))

end COF.SharedMemory.Algorithm
