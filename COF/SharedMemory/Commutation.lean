import COF.SharedMemory.Model

/-! The read/write case analysis used in both critical-configuration arguments. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- For any two distinct processes `p` and `q`, one of three things happens:

1. their steps commute outright; or
2. `p`'s step is *erased* — running `p` then `q` is indistinguishable from running `q`
   alone, to every process except `p` itself; or
3. symmetrically, `q`'s step is erased.

The observer set in cases 2 and 3 excludes the process whose step was erased, because
that process does see its own step. An argument that needs a witness therefore needs a
*third* process, which is why the impossibility requires three and not two.

This is the only place where "atomic read/write register" does real work: the statement
is false for read-modify-write primitives such as compare-and-swap, whose steps neither
commute nor vanish. -/
theorem commutation_or_erasure (c : Config P R V S) {p q : P} (hne : p ≠ q) :
    a.step (a.step c p) q = a.step (a.step c q) p ∨
    Indist {r | r ≠ p} (a.step (a.step c p) q) (a.step c q) ∨
    Indist {r | r ≠ q} (a.step (a.step c q) p) (a.step c p) := by
  have hqp := hne.symm
  cases hp : a.instruction p (c.proc p).state with
  | read rp kp =>
    cases hq : a.instruction q (c.proc q).state with
    | read rq kq =>
      -- Two reads: neither touches memory, and each updates only its own local state.
      left
      apply Config.ext
      · simp [step, hp, hq, hne, hqp]
      · funext r
        by_cases hrp : r = p <;> by_cases hrq : r = q <;>
          simp_all [step, Function.update]
    | write rq vq kq =>
      -- `p` reads, `q` writes: `p`'s read leaves memory untouched, so only `p` can tell
      -- that it happened.
      right; left
      constructor
      · simp [step, hp, hq, hqp]
      · intro r hr
        simp only [Set.mem_ofPred_eq] at hr
        by_cases hrq : r = q <;> simp_all [step, Function.update]
  | write rp vp kp =>
    cases hq : a.instruction q (c.proc q).state with
    | read rq kq =>
      -- `p` writes, `q` reads: symmetric to the previous case, with `q`'s read erased.
      right; right
      constructor
      · simp [step, hp, hq, hne]
      · intro r hr
        simp only [Set.mem_ofPred_eq] at hr
        by_cases hrp : r = p <;> simp_all [step, Function.update]
    | write rq vq kq =>
      by_cases heq : rp = rq
      · -- Two writes to the same register: `q` overwrites `p`'s value, so nothing but
        -- `p`'s own local state records that `p` wrote. A compare-and-swap would instead
        -- report the overwritten value to `q`, and this case would fail.
        subst rq
        right; left
        constructor
        · simp [step, hp, hq, hqp]
        · intro r hr
          simp only [Set.mem_ofPred_eq] at hr
          by_cases hrq : r = q <;> simp_all [step, Function.update]
      · -- Two writes to different registers: the updates are independent.
        left
        apply Config.ext
        · funext r
          by_cases hrp : r = rp <;> by_cases hrq : r = rq <;>
            simp_all [step, Function.update]
        · funext r
          by_cases hrp : r = p <;> by_cases hrq : r = q <;>
            simp_all [step, Function.update]

end COF.SharedMemory.Algorithm
