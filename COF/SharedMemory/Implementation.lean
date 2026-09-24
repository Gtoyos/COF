import COF.Linearizability
import COF.Progress
import Mathlib.Tactic.Common

/-! Implementations of arbitrary sequential objects in the read/write model, with repeated
invocations: the setting of the paper's universal-construction corollary. The consensus model
of `Model.lean` is recovered as a single-shot client in `UniversalConstruction.lean`.

Each process runs a deterministic automaton. The environment invokes operations on idle
processes, at arbitrary times. A process with a pending operation takes steps, each one read or
one write of an atomic register together with local computation, until a step returns a
response. Processes take steps only while executing an operation. Invocations and scheduling
are arbitrary: there is no fairness, and a process that is no longer scheduled has crashed. -/
namespace COF.SharedMemory

/-- One step of a process executing an operation: local computation and a single shared-memory
event, after which the process may return a response. As in `Instruction`, a read continuation
receives the value read and a write continuation receives nothing from memory. -/
inductive OpInstruction (R V S Resp : Type*) where
  | read (register : R) (next : V → S × Option Resp)
  | write (register : R) (value : V) (next : S × Option Resp)

/-- The register an instruction accesses. -/
def OpInstruction.register {R V S Resp : Type*} : OpInstruction R V S Resp → R
  | .read r _ => r
  | .write r _ _ => r

/-- A deterministic implementation of an object with operations `O` and responses `Resp`: one
automaton per process. An invocation updates the invoking process's local state; while its
operation is pending, the process follows `instruction` until a step returns a response. -/
structure Implementation (P R V S O Resp : Type*) where
  /-- The initial contents of the shared registers. -/
  initialMemory : R → V
  /-- Each process's initial local state. -/
  initialState : P → S
  /-- How a process's local state absorbs an invocation. -/
  invoke : P → O → S → S
  /-- A process's next step, determined by its local state. -/
  instruction : P → S → OpInstruction R V S Resp

/-- A process in a configuration: its local state, the operation it is executing, if any, and
how many of its operations have returned. The last two are bookkeeping for histories and
traces; the automaton sees only `state`. -/
@[ext]
structure ProcState (S O : Type*) where
  /-- The automaton's local state. -/
  state : S
  /-- The pending operation; `none` when the process is idle. -/
  pending : Option O
  /-- The number of operations of the process that have returned. -/
  done : ℕ

/-- The process state after a step of operation `o` that ends in local state `s` and returns
`r?`: a response makes the process idle, and counts as one more returned operation. -/
def ProcState.after {S O Resp : Type*} (st : ProcState S O) (o : O) (s : S) :
    Option Resp → ProcState S O
  | some _ => ⟨s, none, st.done + 1⟩
  | none => ⟨s, some o, st.done⟩

/-- A configuration of an implementation: shared memory and every process's state. -/
@[ext]
structure ImplConfig (P R V S O : Type*) where
  /-- The contents of the shared registers. -/
  memory : R → V
  /-- Each process's state. -/
  proc : P → ProcState S O

/-- What the environment and the scheduler do: invoke an operation on a process, or let a
process take a step. -/
inductive Action (P O : Type*) where
  | invoke (p : P) (o : O)
  | step (p : P)

namespace Implementation
variable {P R V S O Resp : Type*} [DecidableEq P] [DecidableEq R]
variable (I : Implementation P R V S O Resp)

/-- The initial configuration: every process is idle, in its initial state. -/
def initial : ImplConfig P R V S O :=
  ⟨I.initialMemory, fun p => ⟨I.initialState p, none, 0⟩⟩

/-- One step of `p`, executing `o`: the new memory, `p`'s new state, and the response, if the
step returns one. -/
def stepResult (c : ImplConfig P R V S O) (p : P) (o : O) :
    (R → V) × ProcState S O × Option Resp :=
  match I.instruction p (c.proc p).state with
  | .read r next =>
    (c.memory, (c.proc p).after o (next (c.memory r)).1 (next (c.memory r)).2,
      (next (c.memory r)).2)
  | .write r v next => (Function.update c.memory r v, (c.proc p).after o next.1 next.2, next.2)

omit [DecidableEq P] in
/-- A step of an operation leaves the process in the state `ProcState.after` describes, for the
response the step returns. -/
theorem stepResult_after (c : ImplConfig P R V S O) (p : P) (o : O) :
    ∃ s, (I.stepResult c p o).2.1 = (c.proc p).after o s (I.stepResult c p o).2.2 := by
  unfold stepResult
  cases I.instruction p (c.proc p).state <;> exact ⟨_, rfl⟩

/-- The effect of an action. Invoking a busy process, or scheduling an idle one, does nothing:
processes are sequential, and take steps only while executing an operation. -/
def act (c : ImplConfig P R V S O) : Action P O → ImplConfig P R V S O
  | .invoke p o =>
    match (c.proc p).pending with
    | none => ⟨c.memory, Function.update c.proc p
        ⟨I.invoke p o (c.proc p).state, some o, (c.proc p).done⟩⟩
    | some _ => c
  | .step p =>
    match (c.proc p).pending with
    | some o => ⟨(I.stepResult c p o).1, Function.update c.proc p (I.stepResult c p o).2.1⟩
    | none => c

/-- Returned operations are never taken back: the count only grows. -/
theorem done_le_act (c : ImplConfig P R V S O) (a : Action P O) (q : P) :
    (c.proc q).done ≤ ((I.act c a).proc q).done := by
  cases a with
  | invoke p o =>
    cases hp : (c.proc p).pending with
    | none =>
      simp only [act, hp]
      by_cases hq : q = p
      · subst hq
        simp
      · simp [Function.update_of_ne hq]
    | some _ => simp [act, hp]
  | step p =>
    cases hp : (c.proc p).pending with
    | none => simp [act, hp]
    | some o =>
      simp only [act, hp]
      by_cases hq : q = p
      · subst hq
        obtain ⟨s, hs⟩ := I.stepResult_after c q o
        simp only [Function.update_self, hs]
        cases (I.stepResult c q o).2.2 <;> simp [ProcState.after]
      · simp [Function.update_of_ne hq]

/-- The event an action contributes to the history: an invocation, a response, or nothing.
Steps that return no response are internal. -/
def event (c : ImplConfig P R V S O) : Action P O → Option (Event P O Resp)
  | .invoke p o =>
    match (c.proc p).pending with
    | none => some (.inv p o)
    | some _ => none
  | .step p =>
    match (c.proc p).pending with
    | some o => (I.stepResult c p o).2.2.map (.res p)
    | none => none

/-- Execute a finite sequence of actions. -/
def run (I : Implementation P R V S O Resp) (c : ImplConfig P R V S O) :
    List (Action P O) → ImplConfig P R V S O
  | [] => c
  | a :: as => I.run (I.act c a) as

/-- Execute `acts` from `c`, starting at time `t`, recording its events into `H`. -/
def recordRun (I : Implementation P R V S O Resp) (t : ℕ) (c : ImplConfig P R V S O)
    (H : History P O Resp) :
    List (Action P O) → History P O Resp
  | [] => H
  | a :: as => I.recordRun (t + 1) (I.act c a) (H.record t (I.event c a)) as

/-- The history of the finite execution `acts` from the initial configuration. -/
def history (acts : List (Action P O)) : History P O Resp :=
  I.recordRun 0 I.initial [] acts

/-- The implementation is linearizable for `obj`: every finite execution has a linearizable
history. -/
def Linearizable {Q : Type*} (obj : Object Q O Resp) : Prop :=
  ∀ acts, COF.Linearizable obj (I.history acts)

/-- The configurations of the infinite execution `α` from `c`. -/
def execution (I : Implementation P R V S O Resp) (c : ImplConfig P R V S O)
    (α : ℕ → Action P O) : ℕ → ImplConfig P R V S O
  | 0 => c
  | n + 1 => I.act (I.execution c α n) (α n)

/-- `p` takes a step at time `k` of the execution `α`: it is scheduled while it has a pending
operation. -/
def StepsAt (α : ℕ → Action P O) (k : ℕ) (p : P) : Prop :=
  α k = .step p ∧ ((I.execution I.initial α k).proc p).pending.isSome

/-- The trace of the infinite execution `α` from the initial configuration. The operation
instance `(p, k, o)` is the `k`-th invocation by `p`, of operation `o`.

It is invoked if `p` was invoked with `o` while idle with `k` returned operations. It completes
once `p` has more than `k` returned operations. Its process is correct if it takes infinitely
many steps or eventually has no pending operation. A step belongs to the pending instance of the
scheduled process; scheduling an idle process, or invoking one, is not a step. -/
def trace (α : ℕ → Action P O) : Trace (P × ℕ × O) O where
  operation i := i.2.2
  invoked i := ∃ t, α t = .invoke i.1 i.2.2 ∧
    ((I.execution I.initial α t).proc i.1).pending = none ∧
    ((I.execution I.initial α t).proc i.1).done = i.2.1
  correct i := (∀ N, ∃ k ≥ N, I.StepsAt α k i.1) ∨
    ∃ N, ∀ k ≥ N, ((I.execution I.initial α k).proc i.1).pending = none
  completed i := ∃ t, i.2.1 < ((I.execution I.initial α t).proc i.1).done
  step k :=
    match α k with
    | .step p => ((I.execution I.initial α k).proc p).pending.map
        fun o => (p, ((I.execution I.initial α k).proc p).done, o)
    | .invoke _ _ => none

/-- The traces of the implementation's infinite executions, all from its initial
configuration. -/
def ValidTrace (t : Trace (P × ℕ × O) O) : Prop := ∃ α, t = I.trace α

/-- The implementation is conflict-obstruction-free: the paper's trace-level condition of
Section 3, over every infinite execution. -/
def ConflictObstructionFree (conflict : O → O → Prop) : Prop :=
  COF.ConflictObstructionFree I.ValidTrace conflict

end Implementation
end COF.SharedMemory
