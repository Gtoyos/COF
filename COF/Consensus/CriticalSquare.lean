import COF.Consensus.Valency
import COF.SharedMemory.Commutation

/-!
# The critical square

Both critical-configuration arguments of the paper, in the proofs of Lemmas 4 and 5, end the same
way. Two processes `p` and `q` each take a step from `c`, and each branch is then extended by the
other process's step:

```text
            c
       p ↙     ↘ q
     c_p         c_q
       q ↘     ↙ p
    c_pq         c_qp
```

If `c_p` and `c_pq` are `v`-valent, and `c_q` and `c_qp` are `w`-valent, then `v = w`. The
paper's proofs do this by cases on the two steps ("`e` must be a write … If `m ≠ m'`, then `e'`
and `e` commute … If instead `m = m'`, then `p₂` cannot distinguish …"). Here the cases are those
of `commutation_or_erasure`: either the bottom corners coincide, or one of them looks like the
opposite top corner to everyone but the process whose step was erased. An active process other
than that one then observes the same thing in both, and `indist_valent_eq` equates the valencies.
-/

namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- The critical square. The observer `o₁` is used when `p`'s step is erased, and `o₂` when `q`'s
is. When both `p` and `q` are active they can observe for each other (`o₁ = q`, `o₂ = p`); when
`p` is not active, as in Lemma 4, a third process observes for both.

The valency of each bottom corner is a hypothesis, rather than being derived from the corner above
it, because `p` need not be active. -/
theorem valent_eq_of_square (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q : P} {v w : Bool}
    (hr : a.Reachable input c) (hne : p ≠ q)
    {o₁ o₂ : P} (ho₁ : o₁ ∈ active) (ho₂ : o₂ ∈ active) (ho₁p : o₁ ≠ p) (ho₂q : o₂ ≠ q)
    (hv : a.Valent active (a.step c p) v)
    (hvq : a.Valent active (a.step (a.step c p) q) v)
    (hw : a.Valent active (a.step c q) w)
    (hwp : a.Valent active (a.step (a.step c q) p) w) : v = w := by
  rcases a.commutation_or_erasure c hne with he | he | he
  · -- The steps commute: `c_pq = c_qp` carries both valencies.
    exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) ho₁
      ⟨congrArg Config.memory he, fun r _ => congrArg (fun c => c.proc r) he⟩ hvq hwp
  · -- `p`'s step is erased: `o₁` cannot tell `c_pq` from `c_q`.
    exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) ho₁
      (he.restrict (by simpa using ho₁p)) hvq hw
  · -- `q`'s step is erased: `o₂` cannot tell `c_qp` from `c_p`.
    exact (a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr q) p) ho₂
      (he.restrict (by simpa using ho₂q)) hwp hv).symm

end COF.SharedMemory.Algorithm
