import COF.Progress

/-!
# The example of Figure 1

> Consider the execution in Figure 1, where three processes access a shared counter. The object
> supports two types of operations: `read()`, which returns the current value of the counter, and
> `inc()`, which increments the counter by one. […] Reading a counter conflicts with
> incrementing it, but two increment operations — and likewise two read operations — commute
> with each other. After some steps of `p₁`, `p₁` crashes while `p₂` and `p₃` continue
> concurrently. In Figure 1, no operation is eventually step-contention free. As a consequence,
> OF would not guarantee that the operations of the two correct processes complete. On the
> contrary, COF would ensure progress because `o₂` and `o₃` are in fact eventually
> conflict-step-contention free.

This file checks each of these claims against Definitions 1 and 2: the execution in which the
increments never complete satisfies obstruction freedom and violates conflict-obstruction freedom.
-/

namespace COF.Checks.Figure1

/-- The operations of the counter. -/
inductive CounterOp | read | inc

/-- The shared counter: `read` returns the value; `inc` increments it and acknowledges with `0`. -/
def counter : Object ℕ CounterOp ℕ where
  initial := 0
  transition
    | .read, q => (q, q)
    | .inc, q => (0, q + 1)

/-- "Reading a counter conflicts with incrementing it". -/
theorem read_inc_conflict : counter.Conflict .read .inc :=
  ⟨0, by simp [Object.CommuteAt, counter]⟩

/-- "Two increment operations … commute with each other". -/
theorem inc_inc_commute : ¬ counter.Conflict .inc .inc := by
  rintro ⟨s, h⟩
  exact h (by simp [Object.CommuteAt, counter])

/-- "… and likewise two read operations". -/
theorem read_read_commute : ¬ counter.Conflict .read .read := by
  rintro ⟨s, h⟩
  exact h (by simp [Object.CommuteAt, counter])

/-- The execution of Figure 1, as a trace. Instance `0` is `p₁`'s `read`, instances `1` and `2`
are the `inc`s of `p₂` and `p₃`. `p₁` takes steps for a while and crashes; then `p₂` and `p₃`
alternate forever. No instance completes. -/
def execution : Trace (Fin 3) CounterOp where
  operation i := if i = 0 then .read else .inc
  invoked _ := True
  correct i := i ≠ 0
  completed _ := False
  step k := if k < 13 then some 0 else if k % 2 = 0 then some 1 else some 2

theorem step_late (k : ℕ) (hk : 13 ≤ k) :
    execution.step k = some 1 ∨ execution.step k = some 2 := by
  simp only [execution, show ¬ k < 13 by omega, ite_false]
  split <;> simp

/-- "No operation is eventually step-contention free." -/
theorem not_eventuallySolo (i : Fin 3) : ¬ execution.EventuallySolo i := by
  rintro (h | ⟨N, hN⟩)
  · exact h
  · have h1 := hN (2 * (N + 13)) (by omega) 1
      (by simp [execution, show ¬ 2 * (N + 13) < 13 by omega])
    have h2 := hN (2 * (N + 13) + 1) (by omega) 2
      (by simp [execution, show ¬ 2 * (N + 13) + 1 < 13 by omega, Nat.add_mod])
    exact absurd (h1.trans h2.symm) (by decide)

/-- "`o₂` and `o₃` are in fact eventually conflict-step-contention free." -/
theorem inc_eventuallyConflictFree (i : Fin 3) (hi : i ≠ 0) :
    execution.EventuallyConflictFree counter.Conflict i := by
  refine Or.inr ⟨13, fun k hk j hj _ => ?_⟩
  have hop : ∀ x : Fin 3, x ≠ 0 → execution.operation x = .inc := fun x hx => by
    simp [execution, hx]
  rcases step_late k hk with h | h <;> rw [h] at hj <;> cases hj <;>
    rw [hop i hi, hop _ (by decide)] <;> exact inc_inc_commute

/-- The crashed reader is owed nothing. -/
theorem reader_faulty : ¬ execution.correct 0 := by simp [execution]

/-- "OF would not guarantee that the operations of the two correct processes complete." -/
theorem obstructionFree_allows : ObstructionFree (· = execution) := by
  rintro t rfl i - - hs
  exact absurd hs (not_eventuallySolo i)

/-- "COF would ensure progress." -/
theorem cof_forbids : ¬ ConflictObstructionFree (· = execution) counter.Conflict := fun h =>
  h execution rfl 1 trivial (show (1 : Fin 3) ≠ 0 by decide)
    (inc_eventuallyConflictFree 1 (by decide))

end COF.Checks.Figure1
