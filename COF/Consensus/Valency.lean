import COF.Consensus.Specification

/-!
# Valency (paper §4.2)

> A configuration `C` is `v`-deciding if some process has decided `v` in `C`. We say that a
> configuration `C` is `v`-valent if there is no `{p₁,p₂}`-only sequence `π`, such that `C ⇝π C'`
> and `C'` is `(1−v)`-deciding. We say that a configuration is univalent if it is `0`-valent or
> `1`-valent. Otherwise, we say that the configuration is bivalent.

The definitions take the set of *active* processes as a parameter; the paper's is `{p₁,p₂}`.

Valency is a negative notion: a configuration from which nothing can ever be decided is both
`0`-valent and `1`-valent. So whenever an argument needs a configuration to have a single valency,
it obtains an actual decision from COF termination (`solo_terminates`).

Besides the definitions, this file proves Lemma 3 (`initial_valent`) and the two facts that the
critical-configuration arguments are built from: a process running solo decides
(`solo_terminates`), and two configurations that an active process cannot tell apart have the same
valency (`indist_valent_eq`).
-/

namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-! ## Definitions -/

/-- Some `active`-only continuation of `c`, possibly empty, reaches a configuration where some
process has decided `v`. -/
def CanDecide (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ∃ d, a.Reach active c d ∧ d.Decided v

/-- `c` is `v`-valent: no `active`-only continuation of `c` reaches a configuration where some
process has decided `!v`. -/
def Valent (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ¬ a.CanDecide active c (!v)

/-- `c` is `0`-valent or `1`-valent. -/
def Univalent (active : Set P) (c : Config P R V S) : Prop :=
  a.Valent active c false ∨ a.Valent active c true

/-- `c` is not univalent. -/
def Bivalent (active : Set P) (c : Config P R V S) : Prop :=
  ¬ a.Univalent active c

/-- Bivalence, stated positively: `active`-only continuations can reach a decision of `0` and a
decision of `1`. -/
theorem bivalent_iff (active : Set P) (c : Config P R V S) :
    a.Bivalent active c ↔ a.CanDecide active c false ∧ a.CanDecide active c true := by
  simp only [Bivalent, Univalent, Valent, Bool.not_false, Bool.not_true, not_or, not_not]
  exact and_comm

/-- A configuration is univalent exactly when it has a valency. -/
theorem univalent_iff (active : Set P) (c : Config P R V S) :
    a.Univalent active c ↔ ∃ v, a.Valent active c v :=
  (Bool.exists_bool (p := a.Valent active c)).symm

/-! ## Basic facts -/

/-- "If a configuration `C` is `v`-valent and it has a descendant `C'`, `C ⇝π C'`, where `π` is
`{p₁,p₂}`-only, then `C'` is also `v`-valent." -/
theorem valent_mono {active : Set P} {c d : Config P R V S} {v : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) : a.Valent active d v := by
  rintro ⟨e, he, hd⟩
  exact hv ⟨e, Reach.trans a hr he, hd⟩

/-- A univalent configuration that is not `!v`-valent is `v`-valent. -/
theorem valent_of_univalent {active : Set P} {c : Config P R V S} {v : Bool}
    (hu : a.Univalent active c) (h : ¬ a.Valent active c (!v)) : a.Valent active c v := by
  cases v
  · exact hu.resolve_right h
  · exact hu.resolve_left h

theorem decided_run {c : Config P R V S} {v : Bool}
    (h : c.Decided v) (ps : List P) : (a.run c ps).Decided v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, a.run_decision c ps p v hp⟩

/-- A reachable configuration where `v` has been decided is `v`-valent, by Agreement. -/
theorem decided_valent (hag : a.Agreement) {input : P → Bool} {active : Set P}
    {c : Config P R V S} {v : Bool} (hr : a.Reachable input c) (hd : c.Decided v) :
    a.Valent active c v := by
  rintro ⟨d, ⟨ps, _, rfl⟩, hop⟩
  have heq := hag input _ (a.reachable_run hr ps) v (!v) (a.decided_run hd ps) hop
  cases v <;> cases heq

/-- Nobody has decided in a reachable bivalent configuration. -/
theorem bivalent_not_decided (hag : a.Agreement) {input : P → Bool} {active : Set P}
    {c : Config P R V S} (hr : a.Reachable input c) (hb : a.Bivalent active c)
    (v : Bool) : ¬ c.Decided v := fun hd =>
  hb ((a.univalent_iff active c).mpr ⟨v, a.decided_valent hag hr hd⟩)

/-! ## Lemma 3 -/

/-- **Lemma 3**, generalized: if every active process proposes `v`, the initial configuration is
`v`-valent. The paper's statement is the case `active = {p₁,p₂}`, `input = (0,1,1)`, `v = 1`.

Paper's proof: "Consider any execution `π` from `I` in which only `p₁` and `p₂` take steps. This
execution is indistinguishable to `p₁` and `p₂` from an execution starting from the input vector
`(1,1,1)`; therefore, by Validity, no process decides `0` in `π`." Only Validity is needed. -/
theorem initial_valent (hval : a.Validity) (active : Set P) (input : P → Bool) (v : Bool)
    (hinput : ∀ p ∈ active, input p = v) : a.Valent active (a.initial input) v := by
  rintro ⟨d, ⟨ps, hps, rfl⟩, p, hp⟩
  by_cases hmem : p ∈ ps
  · -- `p` took steps, so it is active; it decides `!v` in the all-`v` execution too.
    have hi : Indist active (a.initial input) (a.initial (fun _ => v)) := by
      refine ⟨rfl, ?_⟩
      intro q hq
      simp [initial, hinput q hq]
    have he := a.indist_run hi hps
    have hp' : ((a.run (a.initial (fun _ => v)) ps).proc p).decision = some (!v) := by
      rw [← he.2 p (hps p hmem)]
      exact hp
    have hr : a.Reachable (fun _ => v) (a.run (a.initial (fun _ => v)) ps) :=
      ⟨ps, by simp, rfl⟩
    obtain ⟨q, hq⟩ := hval _ _ hr (!v) ⟨p, hp'⟩
    cases v <;> cases hq
  · -- `p` took no step, so it still has no decision.
    rw [a.run_local_untouched _ hmem] at hp
    simp [initial] at hp

/-! ## The two facts behind the critical-configuration arguments -/

/-- From every reachable configuration, a process running solo decides after finitely many steps:
only one process takes steps, so COF termination applies. -/
theorem solo_terminates (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} (hr : a.Reachable input c) (p : P) :
    ∃ ps, (∀ q ∈ ps, q = p) ∧ ∃ v, ((a.run c ps).proc p).decision = some v := by
  obtain ⟨n, hd⟩ := ht.exists_decided hr (fun _ => p)
    ⟨0, input p, by simp⟩ (fun N => ⟨N, le_rfl, rfl⟩)
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hd
  exact ⟨List.replicate n p, by simp, v, by simpa [a.execution_solo] using hv⟩

/-- A decision reached by an `active`-only continuation agrees with the valency. -/
theorem valent_decision {active : Set P} {c d : Config P R V S} {v w : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) (hd : d.Decided w) : v = w := by
  cases v <;> cases w
  · rfl
  · exact (hv ⟨d, hr, hd⟩).elim
  · exact (hv ⟨d, hr, hd⟩).elim
  · rfl

/-- Two configurations that an active process `p` cannot tell apart have the same valency: `p`
running solo decides the same value from both, and each valency must agree with that decision.
This is how every indistinguishability argument of the paper concludes. -/
theorem indist_valent_eq (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c d : Config P R V S} {p : P} {v w : Bool}
    (hr : a.Reachable input c) (hp : p ∈ active)
    (hi : Indist {p} c d) (hc : a.Valent active c v) (hd : a.Valent active d w) :
    v = w := by
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hr p
  have hactive : ∀ q ∈ ps, q ∈ active := by
    intro q hq
    simpa [hps q hq] using hp
  have he := a.indist_run hi (ps := ps) (by simpa using hps)
  have hb' : ((a.run d ps).proc p).decision = some b := by
    rw [← he.2 p (by simp)]
    exact hb
  exact (a.valent_decision hc ⟨ps, hactive, rfl⟩ ⟨p, hb⟩).trans
    (a.valent_decision hd ⟨ps, hactive, rfl⟩ ⟨p, hb'⟩).symm

end COF.SharedMemory.Algorithm
