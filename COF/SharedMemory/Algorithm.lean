import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Common

/-!
# Consensus algorithms in the read/write model

The asynchronous shared-memory model of the paper (§2, *System model* and *Algorithms and
executions*; §4.2, steps and configurations), for algorithms in which every process has a binary
input and may decide a binary value. Consensus algorithms are exactly such algorithms.

* A **configuration** (`Config`) is the contents of the shared registers together with the local
  state of every process. A process's local state records its decision, if it has made one.
* An **algorithm** (`Algorithm`) gives every process a deterministic automaton. A process's
  initial local state depends only on its own input, its next step only on its local state, and
  the initial memory not on the inputs at all.
* A **step** (`Algorithm.step`) is one read or one write of an atomic register, together with
  local computation. A read sees the value read. A write sees nothing of the memory. A process that
  has decided has completed its `propose` operation and takes no further steps.
* An **execution** is given by the processes taking its steps, in order: a list of them
  (`Algorithm.run`) or a sequence of them (`Algorithm.execution`). There is no fairness, and a
  process that stops taking steps before deciding has crashed. An entry naming a process that has
  already decided is not a step and changes nothing (`step_of_decided`). In an `Admissible`
  execution, every entry is a step.

Nothing is assumed of the types of processes `P`, registers `R`, register values `V` or local
states `S`, not even decidable equality: `step` decides equality classically.
-/

namespace COF.SharedMemory

/-! ## The model -/

/-- The local state of a process, with the decision of its `propose` operation. `decision = none`
means the operation is still pending. -/
@[ext]
structure Local (S : Type*) where
  state : S
  decision : Option Bool

/-- A step: a single shared-memory event, followed by local computation. A read continuation
receives the value read. A write continuation receives nothing from memory: this is what makes
the registers read/write registers, and it is what the impossibility proof exploits. -/
inductive Instruction (R V S : Type*) where
  | read (register : R) (next : V → Local S)
  | write (register : R) (value : V) (next : Local S)

/-- A configuration: "the local states of all processes together with the state of the shared
memory" (paper §2). -/
@[ext]
structure Config (P R V S : Type*) where
  memory : R → V
  proc : P → Local S

/-- A deterministic algorithm, one automaton per process. The next step of a process depends only
on its own local state, its initial state only on its own input, and the initial memory on no
input: inputs are private. -/
structure Algorithm (P R V S : Type*) where
  initialMemory : R → V
  initialState : P → Bool → S
  instruction : P → S → Instruction R V S

variable {P R V S : Type*}

namespace Algorithm
variable (a : Algorithm P R V S)

/-- The initial configuration for the input vector `input`: nobody has decided, and each process
knows only its own input. -/
def initial (input : P → Bool) : Config P R V S :=
  ⟨a.initialMemory, fun p => ⟨a.initialState p (input p), none⟩⟩

/-! ## Steps and finite runs -/

open scoped Classical in
/-- `step c p` is the configuration after `p` takes its enabled step in `c`: `C →e C'` in the
paper, for the step `e` of `p`. Only `p`'s local state and the register `p` writes, if any,
change.

A process that has decided has completed its `propose` operation, and takes no further steps: for
it, `step c p = c`. So a decision, once taken, is never revised. -/
noncomputable def step (c : Config P R V S) (p : P) : Config P R V S :=
  match (c.proc p).decision with
  | some _ => c
  | none =>
    match a.instruction p (c.proc p).state with
    | .read r next => ⟨c.memory, Function.update c.proc p (next (c.memory r))⟩
    | .write r v next => ⟨Function.update c.memory r v, Function.update c.proc p next⟩

/-- A process that has decided takes no step. -/
theorem step_of_decided {c : Config P R V S} {p : P} {v : Bool}
    (h : (c.proc p).decision = some v) : a.step c p = c := by
  simp [step, h]

/-- Run the processes of a list, in order, from `c`. -/
noncomputable def run (a : Algorithm P R V S) (c : Config P R V S) : List P → Config P R V S
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

/-! ## Reachability -/

/-- `d` is reachable from `c` by steps of processes in `active`: `c ⇝π d` for an `active`-only
`π`, in the paper's notation. The empty sequence of steps is allowed. -/
def Reach (active : Set P) (c d : Config P R V S) : Prop :=
  ∃ ps, (∀ p ∈ ps, p ∈ active) ∧ d = a.run c ps

/-- `c` is reachable from the initial configuration for `input`, by steps of any processes: `c`
is a configuration of an execution. -/
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
  exact ⟨xs ++ ys, fun p hp => (List.mem_append.mp hp).elim (hx p) (hy p), by simp⟩

theorem reachable_run {input : P → Bool} {c : Config P R V S}
    (h : a.Reachable input c) (ps : List P) : a.Reachable input (a.run c ps) :=
  Reach.trans a h ⟨ps, by simp, rfl⟩

theorem reachable_step {input : P → Bool} {c : Config P R V S}
    (hr : a.Reachable input c) (p : P) : a.Reachable input (a.step c p) :=
  a.reachable_run hr [p]

/-- Induction along a run of `allowed` processes, through reachable configurations. -/
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

/-! ## Steps are local, and decisions persist -/

@[simp] theorem step_local_other (c : Config P R V S) {p q : P} (h : q ≠ p) :
    (a.step c p).proc q = c.proc q := by
  unfold step
  split
  · rfl
  · split <;> simp [Function.update, h]

/-- Decisions persist across a step, whoever takes it. -/
theorem step_decision (c : Config P R V S) (p q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.step c p).proc q).decision = some v := by
  by_cases hp : q = p
  · subst q
    rw [a.step_of_decided h, h]
  · simpa [a.step_local_other c hp] using h

/-- Decisions persist across a run. -/
theorem run_decision (c : Config P R V S) (ps : List P) (q : P) (v : Bool)
    (h : (c.proc q).decision = some v) :
    ((a.run c ps).proc q).decision = some v := by
  induction ps generalizing c with
  | nil => exact h
  | cons p ps ih => exact ih _ (a.step_decision c p q v h)

/-- A process that takes no step keeps its local state, decision included. -/
theorem run_local_untouched (c : Config P R V S) {ps : List P} {p : P}
    (h : p ∉ ps) : (a.run c ps).proc p = c.proc p := by
  induction ps generalizing c with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, a.step_local_other c h.1]

/-! ## Indistinguishability -/

/-- `c` and `d` are indistinguishable to the processes in `observers`: the shared memory is the
same, and so is the local state of every observer. -/
def Indist (observers : Set P) (c d : Config P R V S) : Prop :=
  c.memory = d.memory ∧ ∀ p ∈ observers, c.proc p = d.proc p

/-- Fewer observers can distinguish less. -/
theorem Indist.restrict {observers other : Set P} {c d : Config P R V S}
    (h : Indist observers c d) (hs : other ⊆ observers) : Indist other c d :=
  ⟨h.1, fun p hp => h.2 p (hs hp)⟩

/-- A step of an observer preserves indistinguishability for the observers. -/
theorem indist_step {observers : Set P} {c d : Config P R V S}
    (h : Indist observers c d) {p : P} (hp : p ∈ observers) :
    Indist observers (a.step c p) (a.step d p) := by
  obtain ⟨hm, hl⟩ := h
  have hlocal := hl p hp
  unfold step
  rw [hm, hlocal]
  split
  · exact ⟨hm, hl⟩
  · split <;> constructor
    all_goals try rfl
    all_goals
      intro q hq
      by_cases heq : q = p
      · subst q; simp
      · simp [Function.update, heq, hl q hq]

/-- A run of observers preserves indistinguishability for the observers: a solo run can be
replayed from a configuration that the running process cannot tell apart. -/
theorem indist_run {observers : Set P} {c d : Config P R V S}
    (h : Indist observers c d) {ps : List P} (hps : ∀ p ∈ ps, p ∈ observers) :
    Indist observers (a.run c ps) (a.run d ps) := by
  induction ps generalizing c d with
  | nil => exact h
  | cons p ps ih =>
    exact ih (a.indist_step h (hps p (by simp))) (by simp_all)

/-! ## Infinite executions -/

/-- The configurations of the infinite execution from `c` in which the processes `σ 0, σ 1, …`
take the successive steps. -/
noncomputable def execution (a : Algorithm P R V S) (c : Config P R V S) (σ : ℕ → P) :
    ℕ → Config P R V S
  | 0 => c
  | n + 1 => a.step (a.execution c σ n) (σ n)

theorem execution_succ (c : Config P R V S) (σ : ℕ → P) (n : ℕ) :
    a.execution c σ (n + 1) = a.step (a.execution c σ n) (σ n) := rfl

/-- Decisions persist along an execution. -/
theorem execution_decision {c : Config P R V S} {σ : ℕ → P}
    {n m : ℕ} {p : P} {v : Bool} (hn : n ≤ m)
    (hd : ((a.execution c σ n).proc p).decision = some v) :
    ((a.execution c σ m).proc p).decision = some v := by
  induction m, hn using Nat.le_induction with
  | base => exact hd
  | succ m _ ih => exact a.step_decision _ _ _ _ ih

/-- A process that has taken no step yet keeps its initial local state. -/
theorem execution_proc_of_no_steps (c : Config P R V S) (σ : ℕ → P) {p : P} {t : ℕ}
    (h : ∀ m < t, σ m ≠ p) : (a.execution c σ t).proc p = c.proc p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [execution_succ, a.step_local_other _ (Ne.symm (h t (by omega))),
      ih fun m hm => h m (by omega)]

/-- A process that takes no step between times `s` and `t` keeps its local state. -/
theorem execution_proc_of_no_steps_between (c : Config P R V S) (σ : ℕ → P) {p : P}
    {s t : ℕ} (hst : s ≤ t) (h : ∀ m, s ≤ m → m < t → σ m ≠ p) :
    (a.execution c σ t).proc p = (a.execution c σ s).proc p := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [execution_succ, a.step_local_other _ (Ne.symm (h t hst (by omega))),
      ih fun m h₁ h₂ => h m h₁ (by omega)]

/-- The execution of the constant sequence `p, p, …` is a solo run of `p`. -/
theorem execution_solo (c : Config P R V S) (p : P) (n : ℕ) :
    a.execution c (fun _ => p) n = a.run c (List.replicate n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [execution, ih, List.replicate_succ', run_append]
    rfl

/-- The sequence that runs the list `ps` and then `σ`. -/
def prepend (ps : List P) (σ : ℕ → P) : ℕ → P :=
  match ps with
  | [] => σ
  | p :: ps => fun n => match n with
    | 0 => p
    | n + 1 => prepend ps σ n

@[simp] theorem prepend_add (ps : List P) (σ : ℕ → P) (n : ℕ) :
    prepend ps σ (ps.length + n) = σ n := by
  induction ps with
  | nil => simp [prepend]
  | cons p ps ih => simpa [prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

/-- The first entry of `prepend (p :: ps) σ` is `p`, and the rest is `prepend ps σ`. -/
theorem execution_prepend_cons (c : Config P R V S) (p : P) (ps : List P) (σ : ℕ → P) (m : ℕ) :
    a.execution c (prepend (p :: ps) σ) (m + 1) = a.execution (a.step c p) (prepend ps σ) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [execution_succ, ih]; rfl

/-! ## Admissible executions -/

/-- Every entry of `σ` is a step: in the execution from `c`, the process `σ k` has not decided
when it takes step `k`. -/
def Admissible (c : Config P R V S) (σ : ℕ → P) : Prop :=
  ∀ k, ((a.execution c σ k).proc (σ k)).decision = none

/-- If `σ` is admissible after the run `ps` from `c`, then some run followed by `σ` is admissible
from `c`: `ps` without its entries that are not steps, which change nothing. This turns executions
from reachable configurations into executions from initial configurations. -/
theorem exists_admissible_prepend (c : Config P R V S) (ps : List P) {σ : ℕ → P}
    (hσ : a.Admissible (a.run c ps) σ) : ∃ qs, a.Admissible c (prepend qs σ) := by
  induction ps generalizing c with
  | nil => exact ⟨[], hσ⟩
  | cons p ps ih =>
    cases hp : (c.proc p).decision with
    | some v =>
      -- `p` has decided, so its entry is not a step: drop it.
      rw [run_cons, a.step_of_decided hp] at hσ
      exact ih c hσ
    | none =>
      obtain ⟨qs, hqs⟩ := ih (a.step c p) hσ
      refine ⟨p :: qs, fun k => ?_⟩
      cases k with
      | zero => exact hp
      | succ k => rw [execution_prepend_cons]; exact hqs k

/-- In an admissible execution, a process that has decided takes no further step, so it takes
only finitely many steps. -/
theorem Admissible.finite_of_decided {a : Algorithm P R V S} {c : Config P R V S} {σ : ℕ → P}
    (h : a.Admissible c σ)
    {n : ℕ} {p : P} {v : Bool} (hd : ((a.execution c σ n).proc p).decision = some v) :
    ¬ ∀ N, ∃ k ≥ N, σ k = p := by
  intro hinf
  obtain ⟨k, hk, rfl⟩ := hinf n
  have := h k
  rw [a.execution_decision hk hd] at this
  cases this

end Algorithm
end COF.SharedMemory
