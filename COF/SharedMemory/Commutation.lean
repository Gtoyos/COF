import COF.SharedMemory.Model

/-! The read/write case analysis used in both critical-configuration arguments. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- Two distinct processes either commute, or one step erases the other's effect
as observed by every process except the one whose step was erased. This statement
would be false for read-modify-write primitives such as compare-and-swap. -/
theorem commutation_or_erasure (c : Config P R V S) {p q : P} (hne : p ≠ q) :
    a.step (a.step c p) q = a.step (a.step c q) p ∨
    Indist {r | r ≠ p} (a.step (a.step c p) q) (a.step c q) ∨
    Indist {r | r ≠ q} (a.step (a.step c q) p) (a.step c p) := by
  have hqp := hne.symm
  cases hp : a.instruction p (c.proc p).state with
  | read rp kp =>
    cases hq : a.instruction q (c.proc q).state with
    | read rq kq =>
      left
      apply Config.ext
      · simp [step, hp, hq, hne, hqp]
      · funext r
        by_cases hrp : r = p <;> by_cases hrq : r = q <;>
          simp_all [step, Function.update]
    | write rq vq kq =>
      right; left
      constructor
      · simp [step, hp, hq, hqp]
      · intro r hr
        simp only [Set.mem_ofPred_eq] at hr
        by_cases hrq : r = q <;> simp_all [step, Function.update]
  | write rp vp kp =>
    cases hq : a.instruction q (c.proc q).state with
    | read rq kq =>
      right; right
      constructor
      · simp [step, hp, hq, hne]
      · intro r hr
        simp only [Set.mem_ofPred_eq] at hr
        by_cases hrp : r = p <;> simp_all [step, Function.update]
    | write rq vq kq =>
      by_cases heq : rp = rq
      · subst rq
        right; left
        constructor
        · simp [step, hp, hq, hqp]
        · intro r hr
          simp only [Set.mem_ofPred_eq] at hr
          by_cases hrq : r = q <;> simp_all [step, Function.update]
      · left
        apply Config.ext
        · funext r
          by_cases hrp : r = rp <;> by_cases hrq : r = rq <;>
            simp_all [step, Function.update]
        · funext r
          by_cases hrp : r = p <;> by_cases hrq : r = q <;>
            simp_all [step, Function.update]

end COF.SharedMemory.Algorithm
