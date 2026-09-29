import COF.Consensus.InitialBivalence
import COF.Consensus.BivalentSuccessor

/-!
# Theorem 6: no COF consensus for three or more processes

> **Theorem 6.** No algorithm implements conflict-obstruction-free consensus in the read-write
> shared memory model of three or more processes.

The paper's proof: start from the bivalent configuration of Lemma 4 and extend it forever with
Lemma 5, by steps of `p₁` and `p₂` only. At least one of them takes infinitely many steps and is
correct. Nobody ever decides, since all configurations are bivalent. But `p₁` and `p₂` proposed the
same value, so COF termination requires the correct one to decide.
-/

namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- A sequence taking only two values takes at least one of them infinitely often. -/
theorem infinitely_often_of_two (σ : ℕ → P) (p q : P) (hs : ∀ n, σ n = p ∨ σ n = q) :
    (∀ N, ∃ k ≥ N, σ k = p) ∨ (∀ N, ∃ k ≥ N, σ k = q) := by
  by_cases hp : ∀ N, ∃ k ≥ N, σ k = p
  · exact Or.inl hp
  · right
    push Not at hp
    obtain ⟨N, hN⟩ := hp
    intro M
    refine ⟨max N M, le_max_right _ _, ?_⟩
    exact (hs _).resolve_left (hN _ (le_max_left _ _))

/-- No reachable configuration is bivalent for two processes that proposed the same value.

Iterating Lemma 5 gives an infinite execution through bivalent configurations, in which only
`p₁` and `p₂` take steps. Nobody has decided in a bivalent configuration (`bivalent_not_decided`,
by Agreement), so every entry of the execution is a step. `p₁` and `p₂` proposed the same value,
so COF termination forbids either of them to take infinitely many steps. But one of them does. -/
theorem not_bivalent (hag : a.Agreement) (ht : a.COFTermination) {input : P → Bool}
    {p₁ p₂ : P} (h₁₂ : p₁ ≠ p₂) (hin : input p₁ = input p₂)
    {c : Config P R V S} (hr : a.Reachable input c) : ¬ a.Bivalent {p₁, p₂} c := by
  intro hb
  -- The reachable configurations that are bivalent for `{p₁,p₂}`. Each has a bivalent successor.
  let K := {d : Config P R V S // a.Reachable input d ∧ a.Bivalent {p₁, p₂} d}
  have successor : ∀ d : K, ∃ t : P, (t = p₁ ∨ t = p₂) ∧ a.Bivalent {p₁, p₂} (a.step d.val t) := by
    intro d
    rcases a.bivalent_successor ht h₁₂ d.property.1 d.property.2 with h | h
    · exact ⟨p₁, Or.inl rfl, h⟩
    · exact ⟨p₂, Or.inr rfl, h⟩
  -- Choosing a successor at every configuration defines an infinite execution from `c`.
  choose pick hpick hbiv using successor
  let next : K → K := fun d => ⟨a.step d.val (pick d), a.reachable_step d.property.1 _, hbiv d⟩
  let states : ℕ → K := Nat.rec ⟨c, hr, hb⟩ (fun _ d => next d)
  let σ : ℕ → P := fun n => pick (states n)
  have hexec : ∀ n, a.execution c σ n = (states n).val := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [execution_succ, ih]
  -- Only `p₁` and `p₂` take steps, and they proposed the same value.
  have hhom : ∃ N v, ∀ k ≥ N, input (σ k) = v := by
    refine ⟨0, input p₂, fun k _ => ?_⟩
    rcases hpick (states k) with h | h
    · exact (congrArg input h).trans hin
    · exact congrArg input h
  -- Nobody decides, so every entry is a step.
  have hadm : a.Admissible c σ := by
    intro n
    rw [hexec]
    cases hd : ((states n).val.proc (σ n)).decision with
    | none => rfl
    | some v =>
      exact (a.bivalent_not_decided hag (states n).property.1 (states n).property.2 v
        ⟨σ n, hd⟩).elim
  -- One of them takes infinitely many steps.
  rcases infinitely_often_of_two σ p₁ p₂ (fun n => hpick (states n)) with h | h
  · exact ht.from_reachable hr hadm hhom p₁ h
  · exact ht.from_reachable hr hadm hhom p₂ h

/-- **Theorem 6**: no algorithm satisfies Validity, Agreement and COF termination, as soon as
there are three distinct processes. Nothing is assumed about the other processes, if any: they
need never take a step. -/
theorem no_cof_consensus (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
    ¬ a.COFConsensus := by
  rintro ⟨hval, hag, ht⟩
  obtain ⟨c, hr, hb⟩ := a.reachable_bivalent hval ht p₀ p₁ p₂ h₀₁ h₀₂ h₁₂
  exact a.not_bivalent hag ht h₁₂
    ((zeroAt_of_ne h₀₁.symm).trans (zeroAt_of_ne h₀₂.symm).symm) hr hb

/-- **Theorem 6** for `n ≥ 3` processes `0, …, n - 1`. -/
theorem no_cof_consensus_fin {n : ℕ} (hn : 3 ≤ n) (a : Algorithm (Fin n) R V S) :
    ¬ a.COFConsensus :=
  a.no_cof_consensus ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))

end COF.SharedMemory.Algorithm
