# The formal model

How the paper's notions are formalized in Lean. Names in backticks are declarations in `COF/`.

## Trusted base

Lean's kernel, Mathlib, and the definitions below, which a reader must check against the paper.
The one extra hypothesis is `TwoProcessCOFConsensus`, used only for the threshold theorem (see
[The two-process result](#the-two-process-result)).

## Objects and conflicts (§2)

- `Object Q O R`: a sequential object `(Q, q₀, O, R, σ)`.
- `CommuteAt a b s`: from state `s`, both orders of `a` and `b` reach the same state and return the
  same responses.
- `Conflict a b` (`a ≍ b`): `a` and `b` fail to commute in some state, reachable or not.
- `consensusObject`: binary consensus on `Option Bool`, where `none` is `⊥` and the first proposal
  wins. `consensus_conflict_iff`: two proposals conflict exactly when they differ.

## Progress conditions (§2, §3)

They are stated over a `Trace`: an infinite execution seen through its operation instances (their
operations, and which were invoked, invoked by a correct process, and completed), with each step
attributed to an instance, or to `none` if its process has no pending operation.

| Paper | Lean |
|---|---|
| Definition 1 | `Trace.EventuallyConflictFree` |
| Definition 2 | `ConflictObstructionFree` |
| §2 | `Trace.EventuallySolo`, `ObstructionFree`, `WaitFree` |
| Lemmas 1, 2 | `cof_iff_obstructionFree_of_full`, `cof_iff_waitFree_of_empty` |

An implementation is judged on the traces of all its infinite executions
(`Implementation.ValidTrace`). Instance `(p, k, o)` is the `k`-th invocation by `p`, so repeated
invocations are distinct instances.

## Read/write consensus algorithms

`COF/SharedMemory/Algorithm.lean`: asynchronous shared memory, binary inputs and decisions.

- **Configuration** (`Config`): register contents and every process's local state, including its
  decision, if any.
- **Algorithm** (`Algorithm`): one deterministic automaton per process. Initial memory is
  input-independent, and a process's initial state depends only on its own input.
- **Step** (`step`): one shared-memory event. A read receives the value read. A write receives
  nothing, which is what makes the registers read/write, and what the proof uses
  (`commutation_or_erasure`). A process that has decided has completed its operation and takes no
  further steps (`step_of_decided`), so decisions are irrevocable.
- **Execution** (`run`, `execution`): the processes taking the steps, in order, as a list or a
  sequence, with no fairness. A process that stops taking steps before deciding has crashed, and
  any number may crash. An entry naming a decided process is not a step and changes nothing. In an
  `Admissible` execution, every entry is a step.
- `Reach active c d` is `c ⇝π d` for `π` over `active`, and `Reachable input c` says `c` occurs in
  an execution. `Indist` is indistinguishability: same memory and same local state for each
  observer.

Process, register, value and local-state types may be infinite, and need no decidable equality.

## COF consensus (§4.1)

`COF/Consensus/Specification.lean`:

- `Validity` and `Agreement` hold in every reachable configuration.
- `COFTermination`: in every admissible execution, if from some point only processes that proposed
  the same value take steps, no process takes infinitely many steps.
- `COFConsensus`: all three.

That conclusion is the paper's "every correct process decides in finitely many steps": a decided
process takes no further steps, one that stops before deciding has crashed, and a correct process
that has not decided keeps taking steps.

`WFTermination` implies `COFTermination`, and `COF/Checks/Separation.lean` shows the converse fails.

## Valency (§4.2)

`COF/Consensus/Valency.lean` states the paper's definitions as written, with the pair `{p₁,p₂}`
generalized to a set `active` of processes:

- `Config.Decided c v`: `c` is `v`-deciding, that is, some process, active or not, has decided `v`.
- `CanDecide active c v`: some `active`-only continuation of `c`, possibly empty (`Reach`), reaches
  a `v`-deciding configuration.
- `Valent active c v`: `c` is `v`-valent, that is, `¬ CanDecide active c (!v)`.
- `Univalent`: `0`-valent or `1`-valent. `Bivalent`: not univalent, which amounts to both values
  being decidable (`bivalent_iff`).

This is not the usual notion of Fischer, Lynch and Paterson, where a configuration is `v`-valent
when `v` is the only decision value reachable from it by steps of any processes. It differs in two
ways:

- Only continuations by the active processes count: `p₁` and `p₂` in the paper.
- `v`-valent is negative: it says that `1 − v` cannot be decided, not that `v` can. A configuration
  from which no value can be decided is therefore both `0`- and `1`-valent, hence univalent,
  whereas it has no valency in the usual notion.

Under COF termination, the second difference disappears for reachable configurations: an active
process running solo decides (`solo_terminates`), so some value can always be decided, and
`v`-valent then means that `v` is the only one.

## Implementations and linearizability

`COF/SharedMemory/Implementation.lean`: implementations of objects with repeated invocations, for
Lemmas 1 and 2 and Corollary 7.

- An `Implementation` is one deterministic automaton per process: an initial state, a way to absorb
  an invocation, and a next step (a read or a write, possibly followed by a response).
- The environment invokes operations on idle processes, and processes with a pending operation take
  steps in any order (`Action`, `act`). Invoking a busy process does nothing, and an idle process
  takes no steps.
- The history of a finite execution is a list of intervals (`OpRecord`). `IsLinearization` is Herlihy
  and Wing's condition: it contains every completed instance with its actual response, may include
  a pending one with a chosen response, is legal for the object, and respects real-time order.
  `Linearizable` means every finite execution has one.
- The trace of an infinite execution (`trace`) is what the progress conditions read. A process is
  correct if it takes infinitely many steps or is eventually idle forever.
- `COFUniversal P` (`COF/Universal/Construction.lean`), a COF universal construction: every
  sequential object has a linearizable, COF implementation with processes `P`.

## Differences from the paper

Each makes the Lean statement at least as strong.

1. **More processes.** Theorem 6 and Corollary 7 hold for any process type with three distinct
   members (`theorem6_of_three`, `corollary7_of_three`). The paper's case is `Fin n`, `3 ≤ n`
   (`theorem6`, `corollary7`).
2. **Fewer hypotheses in Lemmas 3 to 5.** Lemma 3 assumes Validity, Lemma 4 Validity and COF
   termination, Lemma 5 COF termination. They also hold for any input vector and any three distinct
   processes.
3. **Weaker universal construction.** The paper's is one algorithm taking the specification as
   input. `COFUniversal` asks only that each object have some implementation, whose types may depend
   on the object.

Like the paper, the formalization treats binary consensus, which implies the result for any larger
set of values.

## Assumptions

Only the model above: deterministic automata over atomic read/write registers, private inputs, and
input-independent initial memory. There is no fairness, no bound on failures, on processes, or on
the size of registers, values or local states, and no use of FLP.

## The two-process result

The paper (§4.1) cites Attiya, Guerraoui, Hendler and Kuznetsov (*The complexity of obstruction-free
implementations*, JACM 56(4), 2009) for COF consensus among two processes. That is not formalized.
`COF/Consensus/Tightness.lean` states it as the proposition `TwoProcessCOFConsensus`, not an axiom.
`cofConsensusImplementable_fin_iff` takes it as an argument and concludes that COF consensus for `n`
processes is implementable exactly when `n ≤ 2`, and `twoProcessCOFConsensus_iff_threshold` shows
it is exactly the unproved part of the threshold.

## Checks

`COF/Checks/`, built with the library:

- `Audit.lean`: the axiom check and the pinned statements.
- `NonVacuity.lean`: the hypotheses are satisfiable (COF consensus and a COF universal construction
  for one process, and a linearizable COF implementation of some object for three).
- `Separation.lean`: COF termination without wait-free termination.
- `Lemma5Reachability.lean`: Lemma 5 fails without reachability.
- `Figure1.lean`: the paper's Figure 1. Obstruction freedom allows the increments to never complete,
  and COF rules it out.
- `Linearizability.lean`: `IsLinearization` accepts and rejects small histories as Herlihy and Wing
  do.
