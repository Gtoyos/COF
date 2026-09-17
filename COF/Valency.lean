import COF.SharedMemory.Model

/-! The paper's restricted valency. Only continuations by `active` are considered,
but an endpoint is deciding if *any* process has decided. In the main argument,
`active` is `{p₁,p₂}`. Empty continuations are included. -/
namespace COF.SharedMemory

variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]

namespace Config

def Decided (c : Config P R V S) (v : Bool) : Prop :=
  ∃ p, (c.proc p).decision = some v

end Config

namespace Algorithm
variable (a : Algorithm P R V S)

def Safe : Prop :=
  ∀ input c, a.Reachable input c →
    (∀ v w, c.Decided v → c.Decided w → v = w) ∧
    (∀ v, c.Decided v → ∃ p, input p = v)

def CanDecide (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ∃ d, a.Reach active c d ∧ d.Decided v

/-- The negative definition from the paper, not unrestricted FLP valency. -/
def Valent (active : Set P) (c : Config P R V S) (v : Bool) : Prop :=
  ¬ a.CanDecide active c (!v)

def Univalent (active : Set P) (c : Config P R V S) : Prop :=
  a.Valent active c false ∨ a.Valent active c true

def Bivalent (active : Set P) (c : Config P R V S) : Prop :=
  ¬ a.Univalent active c

theorem bivalent_iff (active : Set P) (c : Config P R V S) :
    a.Bivalent active c ↔ a.CanDecide active c false ∧ a.CanDecide active c true := by
  simp only [Bivalent, Univalent, Valent, Bool.not_false, Bool.not_true, not_or, not_not]
  exact and_comm

theorem valent_mono {active : Set P} {c d : Config P R V S} {v : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) : a.Valent active d v := by
  rintro ⟨e, he, hd⟩
  exact hv ⟨e, Reach.trans a hr he, hd⟩

theorem decided_run {c : Config P R V S} {v : Bool}
    (h : c.Decided v) (ps : List P) : (a.run c ps).Decided v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, a.run_decision c ps p v hp⟩

theorem decided_valent (hsafe : a.Safe) {input : P → Bool} {active : Set P}
    {c : Config P R V S} {v : Bool} (hr : a.Reachable input c) (hd : c.Decided v) :
    a.Valent active c v := by
  rintro ⟨d, ⟨ps, _, rfl⟩, hop⟩
  have heq := (hsafe input _ (a.reachable_run hr ps)).1 v (!v)
    (a.decided_run hd ps) hop
  cases v <;> cases heq

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

/-- With no initially decided processes, unchanged inputs of all scheduled processes
make a finite execution indistinguishable from one with uniform input. -/
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
