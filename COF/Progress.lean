import COF.Objects

/-! Trace-level progress conditions. Instances have their own identifiers, so repeated
invocations of the same operation are not conflated. A trace records only steps belonging
to pending invocations; `none` is an idle step. Implementation-specific trace validity is
supplied as a predicate, independently of the definitions below. -/
namespace COF

structure Trace (Instance Operation : Type*) where
  operation : Instance → Operation
  invoked : Instance → Prop
  correct : Instance → Prop
  completed : Instance → Prop
  step : ℕ → Option Instance

namespace Trace
variable {I O : Type*}

/-- Single-object version of eventual conflict-step-contention freedom. -/
def EventuallyConflictFree (t : Trace I O) (conflict : O → O → Prop) (i : I) : Prop :=
  t.completed i ∨ ∃ N, ∀ k ≥ N, ∀ j, t.step k = some j → j ≠ i →
    ¬ conflict (t.operation i) (t.operation j)

def EventuallySolo (t : Trace I O) (i : I) : Prop :=
  t.completed i ∨ ∃ N, ∀ k ≥ N, ∀ j, t.step k = some j → j = i

theorem eventuallyConflictFree_of_solo (t : Trace I O) (conflict : O → O → Prop)
    {i : I} (h : t.EventuallySolo i) : t.EventuallyConflictFree conflict i := by
  rcases h with h | ⟨N, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨N, fun k hk j hj hji => (hji (h k hk j hj)).elim⟩

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

theorem eventuallyConflictFree_of_empty (t : Trace I O)
    {conflict : O → O → Prop} (hempty : ∀ a b, ¬ conflict a b) (i : I) :
    t.EventuallyConflictFree conflict i :=
  Or.inr ⟨0, fun _ _ _ _ _ => hempty _ _⟩

end Trace

variable {I O : Type*}

def ConflictObstructionFree (valid : Trace I O → Prop) (conflict : O → O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i →
    t.EventuallyConflictFree conflict i → t.completed i

def ObstructionFree (valid : Trace I O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i → t.EventuallySolo i → t.completed i

def WaitFree (valid : Trace I O → Prop) : Prop :=
  ∀ t, valid t → ∀ i, t.invoked i → t.correct i → t.completed i

theorem waitFree_imp_cof {valid : Trace I O → Prop} {conflict : O → O → Prop}
    (h : WaitFree valid) : ConflictObstructionFree valid conflict := by
  intro t ht i hi hc _
  exact h t ht i hi hc

theorem cof_imp_obstructionFree {valid : Trace I O → Prop} {conflict : O → O → Prop}
    (h : ConflictObstructionFree valid conflict) : ObstructionFree valid := by
  intro t ht i hi hc hs
  exact h t ht i hi hc (t.eventuallyConflictFree_of_solo conflict hs)

/-- Section 3, first lemma. -/
theorem cof_iff_obstructionFree_of_full {valid : Trace I O → Prop}
    {conflict : O → O → Prop} (hfull : ∀ a b, conflict a b) :
    ConflictObstructionFree valid conflict ↔ ObstructionFree valid := by
  refine ⟨cof_imp_obstructionFree, ?_⟩
  intro h t ht i hi hc hf
  exact h t ht i hi hc ((t.eventuallyConflictFree_iff_solo hfull i).mp hf)

/-- Section 3, second lemma. -/
theorem cof_iff_waitFree_of_empty {valid : Trace I O → Prop}
    {conflict : O → O → Prop} (hempty : ∀ a b, ¬ conflict a b) :
    ConflictObstructionFree valid conflict ↔ WaitFree valid := by
  refine ⟨?_, waitFree_imp_cof⟩
  intro h t ht i hi hc
  exact h t ht i hi hc (t.eventuallyConflictFree_of_empty hempty i)

end COF
