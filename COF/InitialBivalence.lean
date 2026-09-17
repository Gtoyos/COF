import COF.Bivalence

/-! A reachable bivalent configuration, obtained by moving a step of the excluded
process across a solo execution. The third process supplies the observer needed
for the indistinguishability argument. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- A *valency flip* at `d`: the configuration is `v`-valent, but one step of the excluded
process `p` makes it `!v`-valent. Assuming every reachable configuration is univalent, a
flip survives a step of the active process `q`.

The critical square at `d` rules out `v` at `step (step d q) p` — otherwise `!v = v` —
and univalence then leaves only `!v`. Note `p ∉ active` is permitted: `r` is the third
process, which observes on `p`'s behalf. -/
theorem flip_step (ht : a.COFTermination) {input : P → Bool} {active : Set P}
    {p q r : P} (hq : q ∈ active) (hobs : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {d : Config P R V S} {v : Bool} (hdr : a.Reachable input d)
    (hdv : a.Valent active d v) (hflip : a.Valent active (a.step d p) (!v)) :
    a.Valent active (a.step d q) v ∧ a.Valent active (a.step (a.step d q) p) (!v) := by
  have hnext := a.valent_mono hdv (Reach.single a _ hq)
  refine ⟨hnext, ?_⟩
  have hn : ¬ a.Valent active (a.step (a.step d q) p) v := by
    intro hn
    have he := a.valent_eq_of_square ht hdr hpq hobs hobs hrp hrq
      hflip (a.valent_mono hflip (Reach.single a _ hq)) hnext hn
    cases v <;> cases he
  exact a.valent_of_univalent (hall _ (a.reachable_step (a.reachable_step hdr q) p))
    (by simpa using hn)

/-- If all reachable configurations were univalent, an excluded process's step
could not change valency.

Were there a flip, `flip_step` would carry it along the whole solo run in which `q`
decides. That decision is `v`, by the valency of the starting configuration, so `p`'s
successor there has `v` decided and cannot be `!v`-valent. -/
theorem external_step_preserves_valency (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {p q r : P} (hq : q ∈ active) (hobs : r ∈ active)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hall : ∀ c, a.Reachable input c → a.Univalent active c)
    {c : Config P R V S} {v : Bool} (hr : a.Reachable input c)
    (hv : a.Valent active c v) : a.Valent active (a.step c p) v := by
  refine a.valent_of_univalent (hall _ (a.reachable_step hr p)) ?_
  intro hflip
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hr q
  have hreach : a.Reach active c (a.run c ps) :=
    ⟨ps, fun t ht => (hps t ht) ▸ hq, rfl⟩
  obtain rfl := a.valent_decision hv hreach ⟨q, hb⟩
  have hfinal := a.run_induction
    (Motive := fun d => a.Valent active d v ∧ a.Valent active (a.step d p) (!v))
    (allowed := fun t => t = q)
    (fun d t htq hdr hpair => by
      subst htq
      exact a.flip_step ht hq hobs hpq hrp hrq hall hdr hpair.1 hpair.2)
    ps c hr ⟨hv, hflip⟩ hps
  refine hfinal.2 ⟨a.step (a.run c ps) p, Reach.refl a _ _, ?_⟩
  simpa using (show (a.step (a.run c ps) p).Decided v from
    ⟨q, a.step_decision (a.run c ps) p q v hb⟩)

/-- Paper Lemma `init_tobivalent`, generalized to any process type containing three
distinct processes. Processes other than these three need never be scheduled.

The input vector has `p₀` proposing `false` and everyone else `true`. Suppose no reachable
configuration were bivalent for `{p₁, p₂}`. The initial configuration is `true`-valent for
them, since that is all they propose, while `p₀` running solo must decide — and can only
decide `false`. Yet `external_step_preserves_valency` says none of `p₀`'s steps can move
the `true`-valency seen by `p₁` and `p₂`, so `false` was never decidable: contradiction. -/
theorem reachable_bivalent (hs : a.Safe) (ht : a.COFTermination)
    (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) :
    let input : P → Bool := fun p => if p = p₀ then false else true
    ∃ c, a.Reachable input c ∧ a.Bivalent {p₁, p₂} c := by
  classical
  dsimp only
  let input : P → Bool := fun p => if p = p₀ then false else true
  change ∃ c, a.Reachable input c ∧ a.Bivalent {p₁, p₂} c
  by_contra hn
  have hall : ∀ c, a.Reachable input c → a.Univalent {p₁, p₂} c := by
    intro c hc
    by_contra hu
    exact hn ⟨c, hc, hu⟩
  have hi : a.Reachable input (a.initial input) := Reach.refl a _ _
  -- `p₁` and `p₂` both propose `true`, so nothing they do alone can decide `false`.
  have hiv : a.Valent {p₁, p₂} (a.initial input) true := by
    apply a.initial_valent hs
    intro p hp
    rcases (show p = p₁ ∨ p = p₂ by simpa using hp) with rfl | rfl
    · simp [input, h₀₁.symm]
    · simp [input, h₂₀]
  -- `p₀` running solo decides, and by its own valency it decides `false`.
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hi p₀
  have hiv0 : a.Valent {p₀} (a.initial input) false := by
    apply a.initial_valent hs
    simp [input]
  obtain rfl := a.valent_decision hiv0 ⟨ps, by simpa using hps, rfl⟩
    (show (a.run (a.initial input) ps).Decided b from ⟨p₀, hb⟩)
  -- But no step of `p₀` disturbs the `true`-valency seen by `p₁` and `p₂`.
  have preserve := a.run_induction
    (Motive := fun c => a.Valent {p₁, p₂} c true) (allowed := fun t => t = p₀)
    (fun c t htp₀ hc hv => by
      subst htp₀
      exact a.external_step_preserves_valency ht (q := p₁) (r := p₂) (by simp) (by simp)
        h₀₁ h₂₀ h₂₁ hall hc hv)
    ps
  exact preserve _ hi hiv hps ⟨a.run (a.initial input) ps, Reach.refl a _ _, p₀, hb⟩

end COF.SharedMemory.Algorithm
