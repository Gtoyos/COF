import COF.Consensus.CriticalSquare

/-!
# Lemma 4: a bivalent configuration is reachable

> **Lemma 4.** There exists a bivalent configuration reachable from `I`.

The paper argues by contradiction. If every configuration reachable from `I` were univalent,
`p₀` running solo from `I` would decide `0` while `I` is `1`-valent, so some step of `p₀` would
be *critical*: it would take a `1`-valent configuration `C` to a `0`-valent one. Following `p₁`'s
solo run from `C`, with `p₂` observing, rules such a step out.

The formal proof has the same two parts. `no_critical_step` shows that no step of `p₀` is
critical: were one critical, it would stay critical along `p₁`'s solo run
(`critical_step_persists`, by the critical square with `p₂` as observer) until `p₁` decides, which
is impossible. Hence `1`-valency survives `p₀`'s solo run, contradicting `p₀`'s decision of `0`
(`reachable_bivalent`).
-/

namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

open scoped Classical in
/-- The inputs of the paper's instance: `p₀` proposes `0` and every other process proposes `1`.
With three processes `p₀, p₁, p₂` this is `I = (0,1,1)`. -/
noncomputable def zeroAt (p₀ : P) : P → Bool :=
  fun p => if p = p₀ then false else true

@[simp] theorem zeroAt_self (p₀ : P) : zeroAt p₀ p₀ = false := by simp [zeroAt]

theorem zeroAt_of_ne {p₀ p : P} (h : p ≠ p₀) : zeroAt p₀ p = true := by simp [zeroAt, h]

/-- The step of `p` at `d` is *critical*: it takes the `v`-valent configuration `d` to a
`!v`-valent one. -/
def CriticalStep (active : Set P) (d : Config P R V S) (p : P) (v : Bool) : Prop :=
  a.Valent active d v ∧ a.Valent active (a.step d p) (!v)

/-- If every reachable configuration is univalent, a critical step of `p` stays critical after a
step of the active process `q`. The critical square at `d`, with the third process `r` as
observer, rules out the valency `v` for `step (step d q) p`; univalence leaves `!v`. -/
theorem critical_step_persists (ht : a.COFTermination) {input : P → Bool} {active : Set P}
    {p q r : P} (hq : q ∈ active) (hr : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {d : Config P R V S} {v : Bool} (hd : a.Reachable input d)
    (hcrit : a.CriticalStep active d p v) : a.CriticalStep active (a.step d q) p v := by
  obtain ⟨hdv, hflip⟩ := hcrit
  have hnext := a.valent_mono hdv (Reach.single a _ hq)
  refine ⟨hnext, ?_⟩
  have hn : ¬ a.Valent active (a.step (a.step d q) p) v := by
    intro hn
    have he := a.valent_eq_of_square ht hd hpq hr hr hrp hrq
      hflip (a.valent_mono hflip (Reach.single a _ hq)) hnext hn
    cases v <;> cases he
  exact a.valent_of_univalent (hall _ (a.reachable_step (a.reachable_step hd q) p))
    (by simpa using hn)

/-- If every reachable configuration is univalent, no step of `p` is critical. Otherwise let the
active process `q` run solo until it decides; by valency it decides `v`. The step of `p` is still
critical at the end (`critical_step_persists`), yet `q`'s decision of `v` is already visible after
it, so the successor cannot be `!v`-valent. -/
theorem no_critical_step (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {p q r : P} (hq : q ∈ active) (hr : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {c : Config P R V S} {v : Bool} (hc : a.Reachable input c) :
    ¬ a.CriticalStep active c p v := by
  intro hcrit
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hc q
  have hreach : a.Reach active c (a.run c ps) := ⟨ps, fun t htps => (hps t htps) ▸ hq, rfl⟩
  obtain rfl := a.valent_decision hcrit.1 hreach ⟨q, hb⟩
  have hend := a.run_induction
    (Motive := fun d => a.CriticalStep active d p v) (allowed := fun t => t = q)
    (fun d t htq hd hcd => by
      subst htq
      exact a.critical_step_persists ht hq hr hpq hrp hrq hall hd hcd)
    ps c hc hcrit hps
  refine hend.2 ⟨a.step (a.run c ps) p, Reach.refl a _ _, ?_⟩
  simpa using (show (a.step (a.run c ps) p).Decided v from
    ⟨q, a.step_decision (a.run c ps) p q v hb⟩)

/-- If every reachable configuration is univalent, a step of `p` preserves valency. -/
theorem step_preserves_valency (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {p q r : P} (hq : q ∈ active) (hr : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {c : Config P R V S} {v : Bool} (hc : a.Reachable input c)
    (hv : a.Valent active c v) : a.Valent active (a.step c p) v :=
  a.valent_of_univalent (hall _ (a.reachable_step hc p)) fun hflip =>
    a.no_critical_step ht hq hr hpq hrp hrq hall hc ⟨hv, hflip⟩

/-- **Lemma 4**: for any three distinct processes, some configuration reachable from
`initial (zeroAt p₀)` is bivalent for `{p₁,p₂}`. Other processes, if any, never take a step.

Suppose not. Then `initial (zeroAt p₀)` is `1`-valent (Lemma 3), and `p₀` running solo decides,
necessarily `0`. Every step of that run preserves `1`-valency (`step_preserves_valency`, with `p₁`
running solo and `p₂` observing), so the configuration where `p₀` has decided `0` is `1`-valent: a
contradiction. Only Validity and COF termination are used. -/
theorem reachable_bivalent (hval : a.Validity) (ht : a.COFTermination)
    (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
    ∃ c, a.Reachable (zeroAt p₀) c ∧ a.Bivalent {p₁, p₂} c := by
  by_contra hn
  have hall : ∀ c, a.Reachable (zeroAt p₀) c → a.Univalent {p₁, p₂} c :=
    fun c hc => Classical.byContradiction fun hu => hn ⟨c, hc, hu⟩
  have hI : a.Reachable (zeroAt p₀) (a.initial (zeroAt p₀)) := Reach.refl a _ _
  -- Lemma 3: `p₁` and `p₂` propose `1`, so `I` is `1`-valent.
  have hI1 : a.Valent {p₁, p₂} (a.initial (zeroAt p₀)) true := by
    apply a.initial_valent hval
    intro p hp
    rcases (show p = p₁ ∨ p = p₂ by simpa using hp) with rfl | rfl
    · exact zeroAt_of_ne h₀₁.symm
    · exact zeroAt_of_ne h₀₂.symm
  -- `p₀` running solo decides, and it can only decide its own input `0`.
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hI p₀
  have hI0 : a.Valent {p₀} (a.initial (zeroAt p₀)) false := by
    apply a.initial_valent hval
    intro p hp
    rw [Set.mem_singleton_iff.mp hp, zeroAt_self]
  obtain rfl := a.valent_decision hI0 ⟨ps, by simpa using hps, rfl⟩
    (show (a.run (a.initial (zeroAt p₀)) ps).Decided b from ⟨p₀, hb⟩)
  -- No step of `p₀` changes the valency seen by `{p₁,p₂}`.
  have hend := a.run_induction
    (Motive := fun c => a.Valent {p₁, p₂} c true) (allowed := fun t => t = p₀)
    (fun c t ht₀ hc hv => by
      subst ht₀
      exact a.step_preserves_valency ht (q := p₁) (r := p₂) (by simp) (by simp)
        h₀₁ h₀₂.symm h₁₂.symm hall hc hv)
    ps
  exact hend _ hI hI1 hps ⟨a.run (a.initial (zeroAt p₀)) ps, Reach.refl a _ _, p₀, hb⟩

end COF.SharedMemory.Algorithm
