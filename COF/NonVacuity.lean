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

end COF.NonVacuity
