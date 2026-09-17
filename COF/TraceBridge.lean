import COF.Universal
import COF.Progress

/-! Relate the trace-level COF definition from Section 3 to the concrete consensus
model. Completed processes do not contribute further operation-instance steps. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- The trace of a single-shot execution with all proposals invoked initially.

A process's instance is its own proposal; it is `correct` when it takes infinitely many
steps or has already returned, and a step counts as a step *of the instance* only while
that instance is still pending — after deciding, the process's steps are idle. -/
def trace (input : P → Bool) (c : Config P R V S) (schedule : ℕ → P) : Trace P Bool where
  operation := input
  invoked := fun _ => True
  completed := fun p => ∃ n v, ((a.execution c schedule n).proc p).decision = some v
  correct := fun p => (∀ N, ∃ k ≥ N, schedule k = p) ∨
    ∃ n v, ((a.execution c schedule n).proc p).decision = some v
  step := fun n =>
    if ((a.execution c schedule n).proc (schedule n)).decision = none
    then some (schedule n) else none

/-- The class of concrete, single-shot shared-memory traces. -/
def ValidTrace (t : Trace P Bool) : Prop :=
  ∃ input c, a.Reachable input c ∧ ∃ schedule, t = a.trace input c schedule

/-- Full trace-level COF implies the necessary liveness fragment used in the
universal-construction reduction. In particular, completed invocations are never
silently counted as pending conflicting operations. -/
theorem objectCOF_of_trace_cof {Q : Type*} (obj : Object Q Bool Bool)
    (h : ConflictObstructionFree a.ValidTrace obj.Conflict) : a.ObjectCOF obj := by
  intro input c hr schedule p hinf hfree
  apply h (a.trace input c schedule) ⟨input, c, hr, schedule, rfl⟩ p trivial (Or.inl hinf)
  right
  obtain ⟨N, hN⟩ := hfree
  refine ⟨N, ?_⟩
  intro k hk q hstep hqp
  have hq : schedule k = q := by
    dsimp [trace] at hstep
    split at hstep
    · exact Option.some.inj hstep
    · cases hstep
  change ¬ obj.Conflict (input p) (input q)
  rw [← hq]
  exact hN k hk (hq ▸ hqp)

/-- The consensus instance of the original trace-level progress condition is
incompatible with single-shot linearizability for three or more processes. -/
theorem no_linearizable_cof (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) :
    ¬ (a.Linearizes consensusObject ∧
      ConflictObstructionFree a.ValidTrace consensusObject.Conflict) := by
  rintro ⟨hs, ht⟩
  exact a.no_cof_consensus p₀ p₁ p₂ h₀₁ h₂₀ h₂₁
    ⟨a.safe_of_consensus_linearizes hs,
      a.termination_of_consensus_objectCOF (a.objectCOF_of_trace_cof consensusObject ht)⟩

end COF.SharedMemory.Algorithm
