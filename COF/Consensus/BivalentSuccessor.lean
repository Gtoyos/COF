import COF.Consensus.CriticalSquare

/-!
# Lemma 5: a bivalent configuration has a bivalent successor

> **Lemma 5.** Any bivalent configuration `C` with `I ⇝ C` has an enabled step `e` by a process
> in `{p₁,p₂}` such that the resulting configuration `C'` with `C →e C'` is bivalent.

The paper's proof: let `C₁` and `C₂` be the configurations after the steps of `p₁` and `p₂`, and
assume both are univalent. They cannot have the same valency, or `C` would have it too. They cannot
have different valencies either, by the case analysis on the two steps: here, the critical square
with `p₁` and `p₂` observing for each other (`successor_valencies_eq`).

Reachability of `C` is needed: the proof runs processes solo until they decide, which COF
termination guarantees only in executions. Without it the statement is false
(`COF/Checks/Lemma5Reachability.lean`).
-/

namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- The successors of `c` by two distinct active processes cannot have different valencies. -/
theorem successor_valencies_eq (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c : Config P R V S} {p q : P} {v w : Bool}
    (hr : a.Reachable input c) (hp : p ∈ active) (hq : q ∈ active) (hne : p ≠ q)
    (hv : a.Valent active (a.step c p) v) (hw : a.Valent active (a.step c q) w) : v = w :=
  a.valent_eq_of_square ht hr hne hq hp hne.symm hne
    hv (a.valent_mono hv (Reach.single a _ hq))
    hw (a.valent_mono hw (Reach.single a _ hp))

/-- If every active successor of `c` is `v`-valent, so is `c`: an `active`-only continuation of
`c` is either empty, or starts with a step of an active process. -/
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

/-- **Lemma 5**: a reachable configuration that is bivalent for `{p₁,p₂}` has a bivalent
successor, reached by a step of `p₁` or of `p₂`. It holds for every input vector, and uses only
COF termination.

The lemma does not say which of the two processes moves, so the execution built from it may
starve one of them. -/
theorem bivalent_successor (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} {p₁ p₂ : P} (h₁₂ : p₁ ≠ p₂)
    (hr : a.Reachable input c) (hb : a.Bivalent {p₁, p₂} c) :
    a.Bivalent {p₁, p₂} (a.step c p₁) ∨ a.Bivalent {p₁, p₂} (a.step c p₂) := by
  by_contra hn
  simp only [Bivalent, univalent_iff, not_or, not_not] at hn
  obtain ⟨⟨v, h₁⟩, ⟨w, h₂⟩⟩ := hn
  -- The two successors cannot have different valencies, and a common valency passes to `c`.
  obtain rfl := a.successor_valencies_eq ht hr (by simp) (by simp) h₁₂ h₁ h₂
  refine hb ((a.univalent_iff _ _).mpr ⟨v, a.valent_of_successors ⟨p₁, by simp⟩ fun p hp => ?_⟩)
  rcases (show p = p₁ ∨ p = p₂ by simpa using hp) with rfl | rfl
  · exact h₁
  · exact h₂

end COF.SharedMemory.Algorithm
