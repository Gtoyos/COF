import COF.SharedMemory.Model

/-! The paper's restricted valency. Only continuations by `active` are considered,
but an endpoint is deciding if *any* process has decided. In the main argument,
`active` is `{p₁,p₂}`. Empty continuations are included. -/
namespace COF.SharedMemory

variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]

namespace Config

/-- Some process has decided `v`. -/
def Decided (c : Config P R V S) (v : Bool) : Prop :=
  ∃ p, (c.proc p).decision = some v

end Config

namespace Algorithm
variable (a : Algorithm P R V S)

/-- Consensus safety: agreement (no two processes decide differently) and validity
(a decided value was proposed), at every reachable configuration. -/
def Safe : Prop :=
  ∀ input c, a.Reachable input c →
    (∀ v w, c.Decided v → c.Decided w → v = w) ∧
    (∀ v, c.Decided v → ∃ p, input p = v)

/-- Some finite continuation scheduling only `active` reaches a decision of `v`. -/
def CanDecide (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ∃ d, a.Reach active c d ∧ d.Decided v

/-- The negative definition from the paper, not unrestricted FLP valency: *no*
`active`-only continuation of `c` ever decides `!v`. The empty continuation is included,
so a `v`-valent configuration has no process that has already decided `!v`.

Being negative, this does not by itself say that `v` is still decidable; a configuration
from which nothing is ever decided is vacuously valent for both values. Every step that
needs the two valencies to be exclusive supplies an actual decision, via
`solo_terminates`. -/
def Valent (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ¬ a.CanDecide active c (!v)

/-- At most one value is still reachable — or nothing is decidable at all. -/
def Univalent (active : Set P) (c : Config P R V S) : Prop :=
  a.Valent active c false ∨ a.Valent active c true

/-- Both values remain reachable; `bivalent_iff` states this positively. -/
def Bivalent (active : Set P) (c : Config P R V S) : Prop :=
  ¬ a.Univalent active c

/-- Bivalence, stated positively: both decisions are still reachable by `active`-only
continuations. This is what makes the negative `Valent` safe to use. -/
theorem bivalent_iff (active : Set P) (c : Config P R V S) :
    a.Bivalent active c ↔ a.CanDecide active c false ∧ a.CanDecide active c true := by
  simp only [Bivalent, Univalent, Valent, Bool.not_false, Bool.not_true, not_or, not_not]
  exact and_comm

/-- Valency is inherited by every `active`-reachable successor: continuations of a
continuation are continuations. -/
theorem valent_mono {active : Set P} {c d : Config P R V S} {v : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) : a.Valent active d v := by
  rintro ⟨e, he, hd⟩
  exact hv ⟨e, Reach.trans a hr he, hd⟩

/-- A univalent configuration that cannot decide `!v` is `v`-valent. This is the only way
univalence is ever consumed. -/
theorem valent_of_univalent {active : Set P} {c : Config P R V S} {v : Bool}
    (hu : a.Univalent active c) (h : ¬ a.Valent active c (!v)) : a.Valent active c v := by
  cases v
  · exact hu.resolve_right h
  · exact hu.resolve_left h

theorem decided_run {c : Config P R V S} {v : Bool}
    (h : c.Decided v) (ps : List P) : (a.run c ps).Decided v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, a.run_decision c ps p v hp⟩

/-- An already-decided configuration is valent for the decided value: by agreement, no
continuation can produce the opposite decision. -/
theorem decided_valent (hsafe : a.Safe) {input : P → Bool} {active : Set P}
    {c : Config P R V S} {v : Bool} (hr : a.Reachable input c) (hd : c.Decided v) :
    a.Valent active c v := by
  rintro ⟨d, ⟨ps, _, rfl⟩, hop⟩
  have heq := (hsafe input _ (a.reachable_run hr ps)).1 v (!v)
    (a.decided_run hd ps) hop
  cases v <;> cases heq

/-- A bivalent configuration is undecided: agreement plus persistence of decisions would
otherwise pin the outcome. This is what makes the infinite bivalent execution a genuine
liveness violation. -/
theorem bivalent_not_decided (hsafe : a.Safe) {input : P → Bool} {active : Set P}
    {c : Config P R V S} (hr : a.Reachable input c) (hb : a.Bivalent active c)
    (v : Bool) : ¬ c.Decided v := by
  intro hd
  have hv := a.decided_valent hsafe hr hd (active := active)
  cases v
  · exact hb (Or.inl hv)
  · exact hb (Or.inr hv)

/-- Nonvacuity must be justified by termination: negative valency alone does not
exclude a configuration from having both valencies. -/
theorem not_both_valent {active : Set P} {c : Config P R V S}
    (hdec : ∃ v, a.CanDecide active c v) :
    ¬ (a.Valent active c false ∧ a.Valent active c true) := by
  obtain ⟨v, hv⟩ := hdec
  cases v <;> simp_all [Valent]

/-- Paper Lemma `init_config_1valent`, generalized: if every process in `active` proposes
`v`, then no `active`-only continuation of the initial configuration decides `!v`.

Nobody has decided initially, so any such decision would have to be taken by a scheduled
process; those processes cannot distinguish `input` from the all-`v` input vector, under
which validity forbids deciding `!v`. Only indistinguishability and validity are used —
no termination assumption. -/
theorem initial_valent (hsafe : a.Safe) (active : Set P) (input : P → Bool) (v : Bool)
    (hinput : ∀ p ∈ active, input p = v) : a.Valent active (a.initial input) v := by
  rintro ⟨d, ⟨ps, hps, rfl⟩, p, hp⟩
  by_cases hmem : p ∈ ps
  · have hi : Indist active (a.initial input) (a.initial (fun _ => v)) := by
      refine ⟨rfl, ?_⟩
      intro q hq
      simp [initial, hinput q hq]
    have he := a.indist_run hi hps
    have hp' : ((a.run (a.initial (fun _ => v)) ps).proc p).decision = some (!v) := by
      rw [← he.2 p (hps p hmem)]
      exact hp
    have hr : a.Reachable (fun _ => v) (a.run (a.initial (fun _ => v)) ps) :=
      ⟨ps, by simp, rfl⟩
    obtain ⟨q, hq⟩ := (hsafe _ _ hr).2 (!v) ⟨p, hp'⟩
    cases v <;> cases hq
  · rw [a.run_local_untouched _ hmem] at hp
    simp [initial] at hp

end Algorithm
end COF.SharedMemory
