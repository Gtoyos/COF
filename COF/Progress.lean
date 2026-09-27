import COF.Objects

/-!
# Progress conditions (paper §2 and §3)

The progress conditions are stated for an abstract `Trace`: an infinite execution seen as a
sequence of steps of operation instances, together with which instances were invoked and
completed and which were invoked by correct processes. An implementation is then given by the set
of traces of its infinite executions (`SharedMemory.Implementation.ValidTrace`), and each progress
condition quantifies over that set.

> **Definition 1.** An operation instance `Φ = (x,o,p)` is eventually conflict-step-contention
> free in an execution `α` if either `Φ` completes in `α`, or there exists a suffix of `α` in which
> no other operation `Φ' = (x,o',q)` takes steps such that `o ≍ o'`.
>
> **Definition 2.** An implementation is conflict-obstruction-free if, for every infinite
> execution `α` and every operation instance `Φ` invoked by a correct process such that `Φ` is
> eventually conflict-step-contention free in `α`, `Φ` completes in `α`.

The paper's operation instances carry an object `x`; a trace describes one object, so `x` is
implicit. Lemmas 1 and 2 of §3 are `cof_iff_obstructionFree_of_full` and
`cof_iff_waitFree_of_empty`.
-/

namespace COF

/-- An infinite execution, seen through its operation instances. `Instance` identifies operation
instances; repeated invocations of the same operation are distinct instances. -/
structure Trace (Instance Operation : Type*) where
  /-- The operation that each instance invokes. -/
  operation : Instance → Operation
  /-- The instance was invoked. -/
  invoked : Instance → Prop
  /-- The process that invoked the instance is correct: it takes infinitely many steps, or
  eventually has no pending operation. -/
  correct : Instance → Prop
  /-- The instance completed: it returned a response. -/
  completed : Instance → Prop
  /-- The instance that takes step `k`, if any. A step of a process with no pending operation
  (`none`) is a step of no instance, so it is contention for nobody. -/
  step : ℕ → Option Instance

namespace Trace
variable {I O : Type*}

/-- **Definition 1.** `i` completes, or from some point on no other instance whose operation
conflicts with `i`'s takes a step. -/
def EventuallyConflictFree (t : Trace I O) (conflict : O → O → Prop) (i : I) : Prop :=
  t.completed i ∨ ∃ N, ∀ k ≥ N, ∀ j, t.step k = some j → j ≠ i →
    ¬ conflict (t.operation i) (t.operation j)

/-- "Eventually step-contention free": `i` completes, or from some point on only `i` takes
steps ("`Φ` runs solo"). -/
def EventuallySolo (t : Trace I O) (i : I) : Prop :=
  t.completed i ∨ ∃ N, ∀ k ≥ N, ∀ j, t.step k = some j → j = i

/-- Running solo is conflict-free, for any conflict relation. -/
theorem eventuallyConflictFree_of_solo (t : Trace I O) (conflict : O → O → Prop)
    {i : I} (h : t.EventuallySolo i) : t.EventuallyConflictFree conflict i := by
  rcases h with h | ⟨N, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨N, fun k hk j hj hji => (hji (h k hk j hj)).elim⟩

/-- When every pair of operations conflicts, being conflict-free is being solo. -/
theorem eventuallyConflictFree_iff_solo (t : Trace I O)
    {conflict : O → O → Prop} (hfull : ∀ a b, conflict a b) (i : I) :
    t.EventuallyConflictFree conflict i ↔ t.EventuallySolo i := by
  constructor
  · rintro (h | ⟨N, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨N, ?_⟩
      intro k hk j hj
      by_contra hne
      exact h k hk j hj hne (hfull _ _)
  · exact t.eventuallyConflictFree_of_solo conflict

/-- When no two operations conflict, every instance is conflict-free. -/
theorem eventuallyConflictFree_of_empty (t : Trace I O)
    {conflict : O → O → Prop} (hempty : ∀ a b, ¬ conflict a b) (i : I) :
    t.EventuallyConflictFree conflict i :=
  Or.inr ⟨0, fun _ _ _ _ _ => hempty _ _⟩

end Trace

variable {I O : Type*}

/-- **Definition 2.** Conflict-obstruction freedom of the executions `valid`: every invoked
instance of a correct process that is eventually conflict-free completes. -/
def ConflictObstructionFree (valid : Trace I O → Prop) (conflict : O → O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i →
    t.EventuallyConflictFree conflict i → t.completed i

/-- Obstruction freedom: "any operation instance `Φ` invoked by a correct process completes in
`α` whenever `Φ` is eventually step-contention-free in `α`". -/
def ObstructionFree (valid : Trace I O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i → t.EventuallySolo i → t.completed i

/-- Wait freedom: "each operation instance invoked by a correct process completes in a finite
number of its own steps". In an infinite execution, completing is completing after finitely many
steps. -/
def WaitFree (valid : Trace I O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i → t.completed i

/-- Wait freedom implies COF. -/
theorem waitFree_imp_cof {valid : Trace I O → Prop} {conflict : O → O → Prop}
    (h : WaitFree valid) : ConflictObstructionFree valid conflict := by
  intro t ht i hi hc _
  exact h t ht i hi hc

/-- COF implies obstruction freedom. -/
theorem cof_imp_obstructionFree {valid : Trace I O → Prop} {conflict : O → O → Prop}
    (h : ConflictObstructionFree valid conflict) : ObstructionFree valid := by
  intro t ht i hi hc hs
  exact h t ht i hi hc (t.eventuallyConflictFree_of_solo conflict hs)

/-- **Lemma 1.** If every pair of operations conflicts, COF is obstruction freedom. -/
theorem cof_iff_obstructionFree_of_full {valid : Trace I O → Prop}
    {conflict : O → O → Prop} (hfull : ∀ a b, conflict a b) :
    ConflictObstructionFree valid conflict ↔ ObstructionFree valid := by
  refine ⟨cof_imp_obstructionFree, ?_⟩
  intro h t ht i hi hc hf
  exact h t ht i hi hc ((t.eventuallyConflictFree_iff_solo hfull i).mp hf)

/-- **Lemma 2.** If no two operations conflict, COF is wait freedom. -/
theorem cof_iff_waitFree_of_empty {valid : Trace I O → Prop}
    {conflict : O → O → Prop} (hempty : ∀ a b, ¬ conflict a b) :
    ConflictObstructionFree valid conflict ↔ WaitFree valid := by
  refine ⟨?_, waitFree_imp_cof⟩
  intro h t ht i hi hc
  exact h t ht i hi hc (t.eventuallyConflictFree_of_empty hempty i)

end COF
