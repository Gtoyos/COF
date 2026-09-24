import COF.Termination
import COF.SharedMemory.Commutation

/-! The critical-square argument and the bivalent-successor lemma. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- The critical square at `c`: `p` and `q` each take a step, and each branch is then
extended by one step of the other process.

```text
            c
       p ↙     ↘ q
     c_p         c_q
       q ↘     ↙ p
    c_pq         c_qp
```

`commutation_or_erasure` says that either the two bottom corners coincide, or one of them
is indistinguishable from the opposite top corner to everyone but a single process. In
each case `indist_valent_eq` forces the two valencies to agree, so `v = w`.

Two observers are needed because which process is blind depends on which step was erased:
`o₁` serves when `p`'s step is erased, `o₂` when `q`'s is. They may be the same process if
a third process is available, and otherwise `q` and `p` themselves will do.

The valencies of both bottom corners are taken as hypotheses rather than derived from the
top ones, because `p` need not belong to `active` — that is exactly the situation in
`reachable_bivalent`, where `p` is the process excluded from the active set. -/
theorem valent_eq_of_square (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q : P} {v w : Bool}
    (hr : a.Reachable input c) (hne : p ≠ q)
    {o₁ o₂ : P} (ho₁ : o₁ ∈ active) (ho₂ : o₂ ∈ active) (ho₁p : o₁ ≠ p) (ho₂q : o₂ ≠ q)
    (hv : a.Valent active (a.step c p) v)
    (hvq : a.Valent active (a.step (a.step c p) q) v)
    (hw : a.Valent active (a.step c q) w)
    (hwp : a.Valent active (a.step (a.step c q) p) w) : v = w := by
  rcases a.commutation_or_erasure c hne with he | he | he
  · -- The branches meet: one configuration carries both valencies.
    exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) ho₁
      ⟨congrArg Config.memory he, fun r _ => congrArg (fun c => c.proc r) he⟩ hvq hwp
  · -- `p`'s step is erased: `c_pq` looks like `c_q` to `o₁`.
    exact a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr p) q) ho₁
      (he.restrict (by simpa using ho₁p)) hvq hw
  · -- `q`'s step is erased: `c_qp` looks like `c_p` to `o₂`.
    exact (a.indist_valent_eq ht (a.reachable_step (a.reachable_step hr q) p) ho₂
      (he.restrict (by simpa using ho₂q)) hwp hv).symm

/-- Two active processes cannot have oppositely valent immediate successors. Here both
processes are active, so each serves as the observer for the other's erased step and no
third process is required. -/
theorem successor_valencies_eq (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q : P} {v w : Bool}
    (hr : a.Reachable input c) (hp : p ∈ active) (hq : q ∈ active) (hne : p ≠ q)
    (hv : a.Valent active (a.step c p) v) (hw : a.Valent active (a.step c q) w) : v = w :=
  a.valent_eq_of_square ht hr hne hq hp hne.symm hne
    hv (a.valent_mono hv (Reach.single a _ hq))
    hw (a.valent_mono hw (Reach.single a _ hp))

/-- If every active successor of `c` is `v`-valent, so is `c`. A continuation of `c` is
either empty — and then any single step still leads to the same decision — or it begins
with a step of some active process. -/
theorem valent_of_successors {active : Set P} (hne : active.Nonempty)
    {c : Config P R V S} {v : Bool}
    (h : ∀ p ∈ active, a.Valent active (a.step c p) v) : a.Valent active c v := by
  rintro ⟨d, ⟨ps, hps, rfl⟩, hd⟩
  cases ps with
  | nil =>
    obtain ⟨p, hp⟩ := hne
    exact h p hp ⟨a.step c p, Reach.refl a _ _, a.decided_run hd [p]⟩
  | cons p ps =>
    exact h p (hps p (by simp)) ⟨a.run (a.step c p) ps,
      ⟨ps, fun q hq => hps q (by simp [hq]), rfl⟩, hd⟩

/-- Paper Lemma `bivalent_to_bivalent`: a reachable bivalent configuration has a bivalent
successor, reached by a step of one of the two active processes.

If both successors were univalent they would carry the same valency, by
`successor_valencies_eq`, and `c` would inherit it. No fairness of the choice is assumed:
the lemma does not say *which* process must move, which is why the schedule built from it
may starve one of the two. -/
theorem bivalent_successor (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} {p q : P} (hne : p ≠ q)
    (hr : a.Reachable input c) (hb : a.Bivalent {p, q} c) :
    a.Bivalent {p, q} (a.step c p) ∨ a.Bivalent {p, q} (a.step c q) := by
  by_contra hn
  have hu : a.Univalent {p, q} (a.step c p) ∧ a.Univalent {p, q} (a.step c q) := by
    simpa only [not_or, Bivalent, not_not] using hn
  have eqv := fun v w => a.successor_valencies_eq ht (active := {p, q})
    (v := v) (w := w) hr (by simp) (by simp) hne
  rcases hu with ⟨hp | hp, hq | hq⟩
  · apply hb; left
    apply a.valent_of_successors ⟨p, by simp⟩
    intro r hmem
    rcases (show r = p ∨ r = q by simpa using hmem) with rfl | rfl <;> assumption
  · cases eqv false true hp hq
  · cases eqv true false hp hq
  · apply hb; right
    apply a.valent_of_successors ⟨p, by simp⟩
    intro r hmem
    rcases (show r = p ∨ r = q by simpa using hmem) with rfl | rfl <;> assumption

end COF.SharedMemory.Algorithm
