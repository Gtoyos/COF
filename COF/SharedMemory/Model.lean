import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Common

/-! Deterministic asynchronous atomic-register algorithms. The scheduler chooses one
process per step, with no fairness requirement. A crash is represented by the scheduler
never choosing that process again. Register and local-state types may be infinite.
Inputs are private and the initial memory is independent of them. -/
namespace COF.SharedMemory

/-- The local state of a process, together with the response of its pending high-level
operation. `decision = none` means the operation has not returned yet. -/
@[ext]
structure Local (S : Type*) where
  state : S
  decision : Option Bool

/-- One step: arbitrary local computation plus a single shared-memory event.

A read continuation receives the value read; a write continuation receives no
information from memory. This distinction is essential to the impossibility proof. -/
inductive Instruction (R V S : Type*) where
  | read (register : R) (next : V → Local S)
  | write (register : R) (value : V) (next : Local S)

/-- A complete system state: the contents of the shared registers together with the
local state of every process. -/
@[ext]
structure Config (P R V S : Type*) where
  memory : R → V
  proc : P → Local S

/-- A deterministic algorithm. The next instruction of a process depends only on its own
local state, and its initial state only on its own input, so inputs are private. -/
structure Algorithm (P R V S : Type*) where
  initialMemory : R → V
  initialState : P → Bool → S
  instruction : P → S → Instruction R V S

variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]

namespace Algorithm
variable (a : Algorithm P R V S)

/-- The initial configuration for an input vector: nobody has decided, and each process
holds only its own input. -/
def initial (input : P → Bool) : Config P R V S :=
  ⟨a.initialMemory, fun p => ⟨a.initialState p (input p), none⟩⟩

/-- Schedule one step of `p`: perform its shared-memory event and install its new local
state.

Decisions are irrevocable — `old.decision.or next.decision` keeps the first response.
Continuing to schedule a decided process is harmless for the proofs; liveness concerns
only processes that have not yet decided. -/
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

/-- Running a concatenated schedule is running one schedule after the other. -/
@[simp] theorem run_append (c : Config P R V S) (xs ys : List P) :
    a.run c (xs ++ ys) = a.run (a.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons p ps ih => exact ih _

/-- Restricted reachability: all scheduled processes belong to `active`. -/
def Reach (active : Set P) (c d : Config P R V S) : Prop :=
  ∃ ps, (∀ p ∈ ps, p ∈ active) ∧ d = a.run c ps

/-- Reachable from the initial configuration for `input`, with no restriction on who
takes steps. -/
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

/-- Allowing more processes to take steps preserves reachability. -/
theorem Reach.mono {active other : Set P} {c d : Config P R V S}
    (h : a.Reach active c d) (hsub : active ⊆ other) : a.Reach other c d := by
  obtain ⟨ps, hp, hd⟩ := h
  exact ⟨ps, fun p hmem => hsub (hp p hmem), hd⟩

/-- Reachability is closed under further steps, by anyone. -/
theorem reachable_run {input : P → Bool} {c : Config P R V S}
    (h : a.Reachable input c) (ps : List P) : a.Reachable input (a.run c ps) :=
  Reach.trans a h ⟨ps, by simp, rfl⟩

theorem reachable_step {input : P → Bool} {c : Config P R V S}
    (hr : a.Reachable input c) (p : P) : a.Reachable input (a.step c p) :=
  a.reachable_run hr [p]

/-- Induction along a finite schedule. A property that survives one step of an `allowed`
process, taken from any reachable configuration, survives a whole run of such steps.

Both critical-configuration arguments push a valency property along a solo run this way. -/
theorem run_induction {input : P → Bool} {Motive : Config P R V S → Prop}
    {allowed : P → Prop}
    (hstep : ∀ c p, allowed p → a.Reachable input c → Motive c → Motive (a.step c p))
    (ps : List P) :
    ∀ c, a.Reachable input c → Motive c → (∀ p ∈ ps, allowed p) → Motive (a.run c ps) := by
  induction ps with
  | nil => intro c _ hm _; exact hm
  | cons p ps ih =>
    intro c hc hm hps
    exact ih (a.step c p) (a.reachable_step hc p)
      (hstep c p (hps p (by simp)) hc hm) (fun t ht => hps t (by simp [ht]))

@[simp] theorem step_local_other (c : Config P R V S) {p q : P} (h : q ≠ p) :
    (a.step c p).proc q = c.proc q := by
  unfold step
  dsimp only
  split <;> simp [Function.update, h]

/-- Decisions persist across a step, whoever is scheduled. -/
theorem step_decision (c : Config P R V S) (p q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.step c p).proc q).decision = some v := by
  by_cases hp : q = p
  · subst q
    unfold step
    dsimp only
    split <;> simp [h]
  · simpa [a.step_local_other c hp] using h

/-- Decisions persist across a finite schedule. -/
theorem run_decision (c : Config P R V S) (ps : List P) (q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.run c ps).proc q).decision = some v := by
  induction ps generalizing c with
  | nil => exact h
  | cons p ps ih => exact ih _ (a.step_decision c p q v h)

/-- Equal shared memory and equal local states for the observing processes. -/
def Indist (observers : Set P) (c d : Config P R V S) : Prop :=
  c.memory = d.memory ∧ ∀ p ∈ observers, c.proc p = d.proc p

omit [DecidableEq P] [DecidableEq R] in
/-- Fewer observers can distinguish less. -/
theorem Indist.restrict {observers other : Set P} {c d : Config P R V S}
    (h : Indist observers c d) (hs : other ⊆ observers) : Indist other c d :=
  ⟨h.1, fun p hp => h.2 p (hs hp)⟩

/-- An observer that cannot tell two configurations apart cannot tell their successors
apart either, as long as it is the observer that is scheduled. -/
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

/-- Indistinguishability is preserved by any schedule of observing processes: this is
what lets a solo run be replayed from a different configuration. -/
theorem indist_run {observers : Set P} {c d : Config P R V S}
    (h : Indist observers c d) {ps : List P} (hps : ∀ p ∈ ps, p ∈ observers) :
    Indist observers (a.run c ps) (a.run d ps) := by
  induction ps generalizing c d with
  | nil => exact h
  | cons p ps ih =>
    exact ih (a.indist_step h (hps p (by simp))) (by simp_all)

/-- A process that is never scheduled keeps its local state, decision included. -/
theorem run_local_untouched (c : Config P R V S) {ps : List P} {p : P}
    (h : p ∉ ps) : (a.run c ps).proc p = c.proc p := by
  induction ps generalizing c with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, a.step_local_other c h.1]

/-- Infinite execution under an arbitrary scheduler. -/
def execution (a : Algorithm P R V S) (c : Config P R V S) (schedule : ℕ → P) :
    ℕ → Config P R V S
  | 0 => c
  | n + 1 => a.step (a.execution c schedule n) (schedule n)

end Algorithm
end COF.SharedMemory
