import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Common

/-! Deterministic asynchronous atomic-register algorithms. The scheduler chooses one
process per step, with no fairness requirement. A crash is represented by the scheduler
never choosing that process again. Register and local-state types may be infinite.
Inputs are private and the initial memory is independent of them. -/
namespace COF.SharedMemory

@[ext]
structure Local (S : Type*) where
  state : S
  decision : Option Bool

/-- A read continuation receives the value read; a write continuation receives no
information from memory. This distinction is essential to the impossibility proof. -/
inductive Instruction (R V S : Type*) where
  | read (register : R) (next : V → Local S)
  | write (register : R) (value : V) (next : Local S)

@[ext]
structure Config (P R V S : Type*) where
  memory : R → V
  proc : P → Local S

structure Algorithm (P R V S : Type*) where
  initialMemory : R → V
  initialState : P → Bool → S
  instruction : P → S → Instruction R V S

variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]

namespace Algorithm
variable (a : Algorithm P R V S)

def initial (input : P → Bool) : Config P R V S :=
  ⟨a.initialMemory, fun p => ⟨a.initialState p (input p), none⟩⟩

/-- Decisions are irrevocable. Continuing to schedule a decided process is harmless
for the proofs; liveness concerns only processes that have not yet decided. -/
def step (c : Config P R V S) (p : P) : Config P R V S :=
  let old := c.proc p
  let finish := fun (memory : R → V) (next : Local S) =>
    Config.mk memory (Function.update c.proc p
      ⟨next.state, old.decision.or next.decision⟩)
  match a.instruction p old.state with
  | .read r next => finish c.memory (next (c.memory r))
  | .write r v next => finish (Function.update c.memory r v) next

/-- Execute a finite schedule. -/
def run (a : Algorithm P R V S) (c : Config P R V S) : List P → Config P R V S
  | [] => c
  | p :: ps => a.run (a.step c p) ps

@[simp] theorem run_nil (c : Config P R V S) : a.run c [] = c := rfl
@[simp] theorem run_cons (c : Config P R V S) (p : P) (ps : List P) :
    a.run c (p :: ps) = a.run (a.step c p) ps := rfl

@[simp] theorem run_append (c : Config P R V S) (xs ys : List P) :
    a.run c (xs ++ ys) = a.run (a.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons p ps ih => exact ih _

/-- Restricted reachability: all scheduled processes belong to `active`. -/
def Reach (active : Set P) (c d : Config P R V S) : Prop :=
  ∃ ps, (∀ p ∈ ps, p ∈ active) ∧ d = a.run c ps

def Reachable (input : P → Bool) (c : Config P R V S) : Prop :=
  a.Reach Set.univ (a.initial input) c

theorem Reach.refl (active : Set P) (c : Config P R V S) : a.Reach active c c :=
  ⟨[], by simp, rfl⟩

theorem Reach.single {active : Set P} (c : Config P R V S) {p : P} (hp : p ∈ active) :
    a.Reach active c (a.step c p) := ⟨[p], by simpa, rfl⟩

theorem Reach.trans {active : Set P} {c d e : Config P R V S}
    (h₁ : a.Reach active c d) (h₂ : a.Reach active d e) : a.Reach active c e := by
  obtain ⟨xs, hx, rfl⟩ := h₁
  obtain ⟨ys, hy, rfl⟩ := h₂
  exact ⟨xs ++ ys, by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hx p hp
    · exact hy p hp, by simp⟩

theorem Reach.mono {active other : Set P} {c d : Config P R V S}
    (h : a.Reach active c d) (hsub : active ⊆ other) : a.Reach other c d := by
  obtain ⟨ps, hp, hd⟩ := h
  exact ⟨ps, fun p hmem => hsub (hp p hmem), hd⟩

theorem reachable_run {input : P → Bool} {c : Config P R V S}
    (h : a.Reachable input c) (ps : List P) : a.Reachable input (a.run c ps) :=
  Reach.trans a h ⟨ps, by simp, rfl⟩

@[simp] theorem step_local_other (c : Config P R V S) {p q : P} (h : q ≠ p) :
    (a.step c p).proc q = c.proc q := by
  unfold step
  dsimp only
  split <;> simp [Function.update, h]

theorem step_decision (c : Config P R V S) (p q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.step c p).proc q).decision = some v := by
  by_cases hp : q = p
  · subst q
    unfold step
    dsimp only
    split <;> simp [h]
  · simpa [a.step_local_other c hp] using h

theorem run_decision (c : Config P R V S) (ps : List P) (q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.run c ps).proc q).decision = some v := by
  induction ps generalizing c with
  | nil => exact h
  | cons p ps ih => exact ih _ (a.step_decision c p q v h)

/-- Equal shared memory and equal local states for the observing processes. -/
def Indist (observers : Set P) (c d : Config P R V S) : Prop :=
  c.memory = d.memory ∧ ∀ p ∈ observers, c.proc p = d.proc p

theorem indist_step {observers : Set P} {c d : Config P R V S}
    (h : Indist observers c d) {p : P} (hp : p ∈ observers) :
    Indist observers (a.step c p) (a.step d p) := by
  obtain ⟨hm, hl⟩ := h
  have hlocal := hl p hp
  unfold step
  dsimp only
  rw [hm, hlocal]
  split <;> constructor
  all_goals try rfl
  all_goals
    intro q hq
    by_cases heq : q = p
    · subst q; simp
    · simp [Function.update, heq, hl q hq]

theorem indist_run {observers : Set P} {c d : Config P R V S}
    (h : Indist observers c d) {ps : List P} (hps : ∀ p ∈ ps, p ∈ observers) :
    Indist observers (a.run c ps) (a.run d ps) := by
  induction ps generalizing c d with
  | nil => exact h
  | cons p ps ih =>
    exact ih (a.indist_step h (hps p (by simp))) (by simp_all)

theorem run_local_untouched (c : Config P R V S) {ps : List P} {p : P}
    (h : p ∉ ps) : (a.run c ps).proc p = c.proc p := by
  induction ps generalizing c with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, a.step_local_other c h.1]

/-- Infinite execution under an arbitrary scheduler. -/
def execution (a : Algorithm P R V S) (c : Config P R V S) (schedule : ℕ → P) : ℕ → Config P R V S
  | 0 => c
  | n + 1 => a.step (a.execution c schedule n) (schedule n)

end Algorithm
end COF.SharedMemory
