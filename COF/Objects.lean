import Mathlib.Tactic.Common

/-! Sequential objects and the response-sensitive conflict relation of Section 2. -/
namespace COF

/-- A deterministic sequential object: the paper's `(Q, q₀, O, R, σ)`. -/
structure Object (State Operation Response : Type*) where
  initial : State
  transition : Operation → State → Response × State

namespace Object
variable {S O R : Type*} (obj : Object S O R)

/-- `a` and `b` commute in state `s`. Commutation is response-sensitive: the two orders
must agree on the final state *and* each operation must return the same response in
either order. The three conjuncts are, in order, equal final states, `a`'s response, and
`b`'s response. -/
def CommuteAt (a b : O) (s : S) : Prop :=
  (obj.transition b (obj.transition a s).2).2 =
    (obj.transition a (obj.transition b s).2).2 ∧
  (obj.transition a s).1 = (obj.transition a (obj.transition b s).2).1 ∧
  (obj.transition b (obj.transition a s).2).1 = (obj.transition b s).1

/-- The paper's `a ≍ b`: a *single* state in which the two operations fail to commute is
enough for them to conflict. As in the paper, quantification is over all object states,
reachable or not. -/
def Conflict (a b : O) : Prop := ∃ s, ¬ obj.CommuteAt a b s

theorem commuteAt_symm {a b : O} {s : S} :
    obj.CommuteAt a b s ↔ obj.CommuteAt b a s := by
  unfold CommuteAt
  aesop

theorem conflict_symm {a b : O} : obj.Conflict a b ↔ obj.Conflict b a := by
  simp only [Conflict, obj.commuteAt_symm (a := a) (b := b)]

end Object

/-- The binary consensus object: `none` is the undecided state, the first proposal wins,
and every later proposal returns the value already stored. -/
def consensusObject : Object (Option Bool) Bool Bool where
  initial := none
  transition v s := let d := s.getD v; (d, some d)

/-- Two proposals commute in every state exactly when they propose the same value.
Distinct proposals commute on the state but not on the responses, which is why
commutation has to be response-sensitive for the conflict relation to be useful. -/
theorem consensus_commute_iff (a b : Bool) :
    (∀ s, consensusObject.CommuteAt a b s) ↔ a = b := by
  constructor
  · intro h
    have hn := (h none).2.1
    simpa [consensusObject] using hn
  · rintro rfl s
    cases s <;> simp [Object.CommuteAt, consensusObject, Option.getD]

/-- The paper's `propose(v) ≍ propose(w) ↔ v ≠ w`. This is the conflict relation the
universal-construction reduction feeds to the COF liveness clause: a schedule is
conflict-free for `p` exactly when everyone still stepping proposed what `p` proposed. -/
theorem consensus_conflict_iff (a b : Bool) :
    consensusObject.Conflict a b ↔ a ≠ b := by
  rw [Object.Conflict, ← not_forall, consensus_commute_iff]

end COF
