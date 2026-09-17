import Mathlib.Tactic.Common

/-! Sequential objects and the response-sensitive conflict relation of Section 2. -/
namespace COF

/-- A deterministic sequential object. -/
structure Object (State Operation Response : Type*) where
  initial : State
  transition : Operation → State → Response × State

namespace Object
variable {S O R : Type*} (obj : Object S O R)

/-- Both final state and each individual operation's response must be preserved. -/
def CommuteAt (a b : O) (s : S) : Prop :=
  (obj.transition b (obj.transition a s).2).2 =
    (obj.transition a (obj.transition b s).2).2 ∧
  (obj.transition a s).1 = (obj.transition a (obj.transition b s).2).1 ∧
  (obj.transition b (obj.transition a s).2).1 = (obj.transition b s).1

/-- As in the paper, quantification is over all object states. -/
def Conflict (a b : O) : Prop := ∃ s, ¬ obj.CommuteAt a b s

theorem commuteAt_symm {a b : O} {s : S} :
    obj.CommuteAt a b s ↔ obj.CommuteAt b a s := by
  unfold CommuteAt
  aesop

theorem conflict_symm {a b : O} : obj.Conflict a b ↔ obj.Conflict b a := by
  simp only [Conflict, obj.commuteAt_symm (a := a) (b := b)]

end Object

/-- The binary consensus object, with `none` denoting the undecided state. -/
def consensusObject : Object (Option Bool) Bool Bool where
  initial := none
  transition v s := let d := s.getD v; (d, some d)

/-- Equal proposals commute, including their responses. -/
theorem consensus_commute_iff (a b : Bool) :
    (∀ s, consensusObject.CommuteAt a b s) ↔ a = b := by
  constructor
  · intro h
    have hn := (h none).2.1
    simpa [consensusObject] using hn
  · rintro rfl s
    cases s <;> simp [Object.CommuteAt, consensusObject, Option.getD]

/-- The conflict relation used for the reduction to consensus. -/
theorem consensus_conflict_iff (a b : Bool) :
    consensusObject.Conflict a b ↔ a ≠ b := by
  rw [Object.Conflict, ← not_forall, consensus_commute_iff]

end COF
