# The formal model

This document explains how the paper's notions are formalized, and why each modelling choice is
faithful. The Lean files are authoritative: every definition below quotes the paper in its
docstring, and [`COF/Checks/Audit.lean`](COF/Checks/Audit.lean) records its exact text.

## What must be trusted

- Lean's kernel, and Mathlib.
- The definitions. They are the translation of the paper's notions, so they are what a reader must
  check against the paper. `COF/Paper.lean` restates the paper's results with them.
- For the threshold theorem only, the hypothesis `TwoProcessCOFConsensus` (see the last section).

Everything else is proved. The build fails on any `sorry`, any axiom beyond `propext`,
`Classical.choice` and `Quot.sound`, and any change to a pinned statement or definition.

## Objects and conflicts (§2)

`Object Q O R` is the paper's sequential object `(Q, q₀, O, R, σ)`: an initial state and a
transition function returning a response and a next state.

- `CommuteAt a b s`: `a` and `b` commute in state `s`. Both orders end in the same state *and* each
  operation returns the same response in both orders, as the paper requires.
- `Conflict a b`: the paper's `a ≍ b`. There is a state in which `a` and `b` do not commute. As in
  the paper, the state ranges over all states, reachable or not.
- `consensusObject`: binary consensus. The states are `Option Bool`, with `none` for `⊥`, and the
  first proposal wins. Following the paper, `consensus_commuteAt_decided` and
  `consensus_commuteAt_undecided_iff` give the commutation of proposals in each state, and
  `consensus_conflict_iff` derives that two proposals conflict exactly when they differ.

## Progress conditions (§2, §3)

The progress conditions are stated over a `Trace`: an infinite execution seen through its
operation instances. It records each instance's operation, and which instances were invoked, were
invoked by a correct process, and completed. For each step it records the instance taking it, or
`none` for a step of a process with no pending operation.

- `Trace.EventuallyConflictFree` is Definition 1, and `ConflictObstructionFree` is Definition 2.
- `Trace.EventuallySolo`, `ObstructionFree` and `WaitFree` are the paper's §2 notions.
- Lemmas 1 and 2 are `cof_iff_obstructionFree_of_full` and `cof_iff_waitFree_of_empty`.

Each condition quantifies over a set of traces; for an implementation, the traces of all its
infinite executions (`Implementation.ValidTrace`). A trace describes one object, so the object `x`
of the paper's operation instances `Φ = (x, o, p)` is implicit. In an implementation, the instance
`(p, k, o)` is the `k`-th invocation by `p`, so repeated invocations of one operation are distinct
instances.

## Consensus algorithms in the read/write model

`COF/SharedMemory/Algorithm.lean` models the paper's asynchronous shared memory, for algorithms in
which every process has a binary input and may decide a binary value.

- A **configuration** (`Config`) is the register contents together with every process's local
  state. A local state (`Local`) includes the process's decision, if any.
- An **algorithm** (`Algorithm`) has one deterministic automaton per process. The initial memory
  does not depend on the inputs, and each process's initial state depends only on its own input.
  (If the memory could depend on the inputs, consensus would be trivial.) A process's next step
  depends only on its own local state.
- A **step** (`step`) is one shared-memory event and local computation. A read continuation receives
  the value read. A write continuation receives nothing from memory: this is what makes the
  registers read/write registers, and it is exactly what the proof uses (`commutation_or_erasure`).
- Decisions are irrevocable. A process that has decided can still be scheduled; such steps belong
  to no pending operation.
- A **schedule** is a list (`run`) or a sequence (`execution`) of processes. It is arbitrary: there
  is no fairness, and a crash is a process that is never scheduled again. Any number of processes
  may crash.
- `Reach active c d` is the paper's `c ⇝π d` for an `active`-only `π`, the empty `π` included.
  `Reachable input c` says `c` is a configuration of an execution. `Indist` is indistinguishability:
  same memory, and same local state for each observer.

Nothing is assumed of the types of processes, registers, values or local states. They may be
infinite, and not even decidable equality is required: `step` decides equality classically.

## COF consensus (§4.1)

`COF/Consensus/Specification.lean` states the paper's three properties.

- `Validity` and `Agreement` hold in every reachable configuration. Decisions are irrevocable, so
  this is the paper's formulation in terms of executions.
- `COFTermination`: in the execution from any initial configuration, if from some point on every
  scheduled process proposed the same value, then every process scheduled infinitely often decides.
  A process scheduled infinitely often is correct. A correct process scheduled finitely often has
  no pending operation, so it has already decided.
- `COFConsensus` is the conjunction of the three.

The paper's "take steps" can be read in two ways, since a decided process may still be scheduled.
`COFTermination` counts every scheduled step. `StrictCOFTermination` counts only steps of pending
operations, which is the paper's §2 notion of an operation instance taking a step. The strict
reading demands termination in more executions, and implies the other
(`StrictCOFTermination.cofTermination`). Theorem 6 assumes `COFTermination`, so it covers both
readings; `theorem6_strict` states the strict case.

`WFTermination` is wait-free termination. It implies COF termination, which is what the paper's
"weaker liveness condition" means, and `COF/Checks/Separation.lean` shows that the converse fails.

## Valency and the proof of Theorem 6 (§4.2)

`COF/Consensus/Valency.lean` defines `CanDecide`, `Valent`, `Univalent` and `Bivalent` exactly as
the paper does, for a set of active processes (`{p₁, p₂}` in the paper). Valency is negative: a
configuration from which nothing can be decided is both `0`-valent and `1`-valent. Whenever the
proof needs a single valency, it gets an actual decision from COF termination (`solo_terminates`).

The proof follows the paper:

- **Lemma 3** (`initial_valent`). If every active process proposes `v`, the initial configuration is
  `v`-valent, by indistinguishability from the all-`v` input and Validity.
- **The critical square** (`COF/Consensus/CriticalSquare.lean`). Two steps of distinct processes
  either commute, or one of them is invisible to every other process (`commutation_or_erasure`).
  So an observer that runs solo cannot distinguish the two branches, and the branches have the
  same valency.
- **Lemma 4** (`reachable_bivalent`). If every reachable configuration were univalent, `p₀` running
  solo from `I` would decide `0` while `I` is `1`-valent, so some step of `p₀` would be critical.
  `no_critical_step` rules that out: a critical step stays critical along `p₁`'s solo run
  (`critical_step_persists`, with `p₂` observing) until `p₁` decides, which is impossible. This is
  where the third process is needed.
- **Lemma 5** (`bivalent_successor`). The two successors of a reachable bivalent configuration
  cannot both be univalent: equal valencies pass to the configuration, and different ones
  contradict the critical square with `p₁` and `p₂` observing for each other.
- **Theorem 6** (`no_cof_consensus`). Iterating Lemma 5 from the configuration of Lemma 4 gives an
  infinite execution through bivalent configurations in which only `p₁` and `p₂`, who proposed the
  same value, take steps. One of them is scheduled infinitely often, so COF termination makes it
  decide. But by Agreement nobody has decided in a bivalent configuration.

## Implementations and linearizability

`COF/SharedMemory/Implementation.lean` models the paper's implementations of objects, with
repeated invocations: the setting of Lemmas 1 and 2 and of Corollary 7.

- An `Implementation` has one deterministic automaton per process: an initial state, a way to
  absorb an invocation, and a next step (a read or a write, after which the process may return a
  response).
- The environment invokes operations on idle processes at arbitrary times, and schedules processes
  arbitrarily (`Action`, `act`). Invoking a busy process, or scheduling an idle one, does nothing:
  processes are sequential and take steps only while an operation is pending.
- The history of a finite execution lists its operation instances as intervals (`OpRecord`).
  `IsLinearization` is Herlihy and Wing's condition. The linearization contains every completed
  instance with its actual response, and may include a pending instance with a chosen response or
  leave it out. It is legal for the object, and respects real-time order. An implementation is
  `Linearizable` when every finite execution has a linearizable history.
- The trace of an infinite execution (`trace`) makes the progress conditions apply: instance
  `(p, k, o)` is invoked when `o` is invoked on `p` while `p` is idle with `k` returned operations.
  It completes when `p` has returned more than `k` operations. Its process is correct if it takes
  infinitely many steps or is eventually idle forever.

## Universal constructions and Corollary 7

`COFUniversal P` asks that every sequential object have an implementation, with processes `P`, that
is linearizable and conflict-obstruction-free for the object's conflict relation. The proof is the
paper's reduction (`COF/Universal/`). Run the implementation of the consensus object by processes
that each propose once (`Implementation.singleShot`). That client is a consensus algorithm, step
for step the same as the implementation (`embed_step`). Linearizability of the implementation gives
the client Validity and Agreement (`linearizes_singleShot`), and its COF gives the client COF
termination (`cofTerminationFor_singleShot`). Theorem 6 then applies.

## Differences from the paper

Each difference makes the Lean statement at least as strong as the paper's.

1. **More processes.** Theorem 6 and Corollary 7 hold for any process type with three distinct
   members (`theorem6_of_three`, `corollary7_of_three`), including infinite ones. The paper's
   "three or more processes" is the case `Fin n` with `3 ≤ n` (`theorem6`, `corollary7`).
2. **Fewer hypotheses for Lemmas 3 to 5.** The paper proves them for an algorithm implementing COF
   consensus. Here each assumes only what its proof uses: Lemma 3 uses Validity, Lemma 4 uses
   Validity and COF termination, and Lemma 5 uses COF termination. The development also proves
   them for any input vector and any three distinct processes.
3. **The weaker reading of COF termination.** Theorem 6 refutes `COFTermination`, which the strict
   reading implies (see *COF consensus* above).
4. **A weaker notion of universal construction.** The paper's universal construction is one
   algorithm taking the specification as input. `COFUniversal` asks only that every object have
   some implementation, whose register, value and local-state types may depend on the object and
   live in any universe.

The paper restricts attention to binary consensus, and so does the formalization. The impossibility
for binary consensus implies it for any larger set of values, by restricting the inputs to two of
them.

## What is assumed, and what is not

The impossibility results assume only the model of the sections above: deterministic automata
communicating through atomic read/write registers, with private inputs and input-independent
initial memory. They do not assume fairness, a bound on failures, finiteness of the registers,
values or local states, a bound on the number of processes, or decidable equality, and they do not
use the FLP impossibility theorem.

## The cited two-process result

The paper remarks (§4.1) that COF consensus is implementable for two processes, citing the
obstruction-free consensus algorithm of Attiya, Guerraoui, Hendler and Kuznetsov (*The complexity
of obstruction-free implementations*, JACM 56(4), 2009). This is outside the paper's proofs and is
not formalized. `COF/Consensus/Tightness.lean` states it as `TwoProcessCOFConsensus`, an ordinary
proposition rather than an axiom. The one theorem that uses it, `cofConsensusImplementable_fin_iff`,
takes it as an explicit argument and concludes that COF consensus for `n` processes is
implementable exactly when `n ≤ 2`. The hypothesis is stated with the weaker reading of COF
termination, so it asks for no more than the paper claims (`cofConsensusImplementable_of_strict`).
`twoProcessCOFConsensus_iff_threshold` shows it is exactly the part of the threshold statement that
is not proved here.

## Checks

The files in `COF/Checks/` are built with the library.

- `Audit.lean`: the project-wide axiom check, and the pinned statements and definitions.
- `NonVacuity.lean`: the hypotheses of the impossibility results are satisfiable. COF consensus is
  satisfiable with one process, a COF universal construction exists for one process, and with
  three processes some object has a linearizable, COF implementation.
- `Separation.lean`: an algorithm satisfies COF termination but not wait-free termination.
- `Lemma5Reachability.lean`: without its reachability hypothesis, Lemma 5 is false.
- `Figure1.lean`: the paper's Figure 1. Obstruction freedom allows the execution in which the
  increments never complete, and COF rules it out.
- `Linearizability.lean`: `IsLinearization` accepts and rejects small histories as Herlihy and
  Wing's definition does.
