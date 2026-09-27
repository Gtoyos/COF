import Mathlib.Tactic.Common

/-!
# Sequential objects and their conflict relation (paper §2)

> A sequential object is defined as a tuple `(Q, q₀, O, R, σ)`, where `Q` is a set of states,
> `q₀ ∈ Q` is the initial state, `O` is a set of operations, `R` is a set of responses, and
> `σ : O × Q → R × Q` is a state transition function specifying the response and next state for
> each operation and state. […] Given two operations `o, o' ∈ O`, we say that they commute in a
> state `q` if `o·o'(q) = o'·o(q)` and each operation returns the same result in both sequences.
> The object defines a symmetric conflict relation, written `≍ ⊆ O × O`, where `o ≍ o'` if there
> exists a state `q` in which `o` and `o'` do not commute.

The file also defines the binary consensus object of §4.1 and computes its conflict relation, as
the paper does: two proposals conflict exactly when they propose different values.
-/

namespace COF

/-- A sequential object `(Q, q₀, O, R, σ)`; `transition` is `σ`, curried. -/
structure Object (State Operation Response : Type*) where
  initial : State
  transition : Operation → State → Response × State

namespace Object
variable {S O R : Type*} (obj : Object S O R)

/-- `a` and `b` commute in state `s`. The three conjuncts say that `a` then `b` and `b` then `a`
end in the same state, that `a` returns the same response in both orders, and that `b` does. -/
def CommuteAt (a b : O) (s : S) : Prop :=
  (obj.transition b (obj.transition a s).2).2 =
    (obj.transition a (obj.transition b s).2).2 ∧
  (obj.transition a s).1 = (obj.transition a (obj.transition b s).2).1 ∧
  (obj.transition b (obj.transition a s).2).1 = (obj.transition b s).1

/-- The conflict relation `a ≍ b`: `a` and `b` fail to commute in some state. As in the paper,
the state ranges over all states, reachable or not. -/
def Conflict (a b : O) : Prop := ∃ s, ¬ obj.CommuteAt a b s

theorem commuteAt_symm {a b : O} {s : S} :
    obj.CommuteAt a b s ↔ obj.CommuteAt b a s := by
  unfold CommuteAt
  aesop

/-- The conflict relation is symmetric. -/
theorem conflict_symm {a b : O} : obj.Conflict a b ↔ obj.Conflict b a := by
  simp only [Conflict, obj.commuteAt_symm (a := a) (b := b)]

end Object

/-! ## The binary consensus object -/

/-- The binary consensus object (paper §4.1). States are `Option Bool`, with `none` for the
undecided state `⊥`; the operation `v : Bool` is `propose(v)`; responses are `Bool`. "The
transition function sets the state to the argument of the first propose operation and returns
that value; subsequent operations return the decision value associated with the state without
modifying it." -/
def consensusObject : Object (Option Bool) Bool Bool where
  initial := none
  transition v s := let d := s.getD v; (d, some d)

/-- "Any pair of propose operations commute in states `0` and `1`". -/
theorem consensus_commuteAt_decided (d a b : Bool) :
    consensusObject.CommuteAt a b (some d) := by
  cases d <;> cases a <;> cases b <;> simp [Object.CommuteAt, consensusObject]

/-- "Two operations `propose(v)` and `propose(v')` commute in state `⊥` iff `v = v'`." -/
theorem consensus_commuteAt_undecided_iff (a b : Bool) :
    consensusObject.CommuteAt a b none ↔ a = b := by
  cases a <;> cases b <;> simp [Object.CommuteAt, consensusObject]

/-- "Thus, two proposals conflict if and only if they propose different values." -/
theorem consensus_conflict_iff (a b : Bool) :
    consensusObject.Conflict a b ↔ a ≠ b := by
  constructor
  · rintro ⟨s, hs⟩ rfl
    cases s with
    | none => exact hs ((consensus_commuteAt_undecided_iff a a).mpr rfl)
    | some d => exact hs (consensus_commuteAt_decided d a a)
  · intro hne
    exact ⟨none, fun h => hne ((consensus_commuteAt_undecided_iff a b).mp h)⟩

end COF
