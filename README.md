# Pending Conflicts Make Progress Impossible — Lean formalization

This project formalizes the main impossibility argument in
[`short_versionv2.tex`](short_versionv2.tex), using Lean 4 and Mathlib.

The development proves that a deterministic asynchronous read/write-register
algorithm cannot satisfy binary consensus safety and conflict-obstruction-free
termination when there are at least three processes. It also proves the paper's
corollary that no conflict-obstruction-free universal construction exists, with
linearizability and COF stated in full for implementations with repeated
invocations, and the two progress-equivalence lemmas in Section 3. There are no
admitted proofs or project-specific axioms.

The paper's remark that COF consensus *is* implementable for two processes is a
cited result, which the paper does not prove. The development takes it as a single
explicit hypothesis, `COF.TwoProcessCOFConsensus`, and derives from it that three
processes is the exact threshold. Nothing else depends on it.

[`MODEL.md`](MODEL.md) states the formal model in full: every assumption, every
place the formalization departs from the paper, and the non-vacuity checks.

## Build

The versions are pinned by `lean-toolchain` and `lake-manifest.json`.

```sh
lake build
```

`lake build` covers the whole development, including `COF/Audit.lean` (which
pins the axiom dependencies of each headline result) and `COF/NonVacuity.lean`
(which checks that the impossibility hypotheses are satisfiable). Replacing any
proof with `sorry` fails the build.

Import the complete development with `import COF`.

## Paper-to-code map

Names below are in `COF.SharedMemory.Algorithm`, unless otherwise qualified;
`Implementation.x` abbreviates `COF.SharedMemory.Implementation.x`.

| Paper result or definition | Lean declaration | File |
| --- | --- | --- |
| Sequential objects and response-sensitive commutativity | `COF.Object`, `COF.Object.CommuteAt`, `COF.Object.Conflict` | `COF/Objects.lean` |
| Consensus proposals conflict exactly when their inputs differ | `COF.consensus_conflict_iff` | `COF/Objects.lean` |
| Eventual conflict-step-contention freedom and COF | `COF.Trace.EventuallyConflictFree`, `COF.ConflictObstructionFree` | `COF/Progress.lean` |
| All operations conflict: COF iff OF | `COF.cof_iff_obstructionFree_of_full` | `COF/Progress.lean` |
| No operations conflict: COF iff WF | `COF.cof_iff_waitFree_of_empty` | `COF/Progress.lean` |
| Deterministic asynchronous atomic-register model | `COF.SharedMemory.Algorithm`, `step`, `run` | `COF/SharedMemory/Model.lean` |
| Read/write commutation and erasure | `commutation_or_erasure` | `COF/SharedMemory/Commutation.lean` |
| Consensus safety and restricted valency | `Safe`, `Valent`, `Bivalent` | `COF/Valency.lean` |
| Initial configuration is 1-valent (`init_config_1valent`) | `initial_valent` (generalized) | `COF/Valency.lean` |
| COF consensus termination; equivalence of initial/reachable formulations | `COFTermination`, `cofTermination_iff_initial` | `COF/Termination.lean` |
| A reachable bivalent configuration (`init_tobivalent`) | `reachable_bivalent` | `COF/InitialBivalence.lean` |
| A bivalent successor (`bivalent_to_bivalent`) | `bivalent_successor` | `COF/Bivalence.lean` |
| Consensus impossibility (`no_quasi_cons`) | `no_cof_consensus`, `no_cof_consensus_fin` | `COF/Impossibility.lean` |
| Two-process COF consensus is implementable (§4.1, cited, not proved) | `COF.TwoProcessCOFConsensus`: a **hypothesis** | `COF/Tightness.lean` |
| The three-process bound is tight, given the cited result | `COF.cofConsensusImplementable_fin_iff`, `COF.twoProcessCOFConsensus_iff_threshold` | `COF/Tightness.lean` |
| Implementations of arbitrary objects, with repeated invocations | `COF.SharedMemory.Implementation`, `Implementation.act`, `Implementation.history`, `Implementation.trace` | `COF/SharedMemory/Implementation.lean` |
| Histories, real-time order, linearizability (Herlihy–Wing) | `COF.OpRecord`, `COF.History`, `COF.Linearizable` | `COF/Linearizability.lean` |
| Linearizable, COF implementations of an object | `Implementation.Linearizable`, `Implementation.ConflictObstructionFree` | `COF/SharedMemory/Implementation.lean` |
| COF universal construction, and its impossibility (`cor:no_cof_univ`) | `COF.COFUniversal`, `COF.no_cofUniversal`, `COF.no_cofUniversal_fin` | `COF/UniversalConstruction.lean` |
| The reduction to consensus: a single-shot client is a consensus algorithm | `Implementation.singleShot`, `Implementation.embed_step`, `Implementation.no_linearizable_cof_consensus` | `COF/UniversalConstruction.lean` |
| Single-shot fragments, implied by the full notion | `Linearizes`, `ObjectCOF`, `COF.BinaryUniversal`, `COF.binaryUniversal_of_cofUniversal` | `COF/Universal.lean`, `COF/UniversalConstruction.lean` |
| Trace-level COF implies the concrete liveness condition | `objectCOF_of_trace_cof`, `cofTermination_of_initial_trace_cof`, `no_linearizable_cof` | `COF/TraceBridge.lean` |

## Model and scope

- A configuration contains shared registers and a local state for each process.
  Register, register-value, and local-state types may be infinite. Nothing is
  assumed of the process, register, value, or local-state types, not even
  decidable equality: the model decides equality classically, so no theorem
  carries a decidability hypothesis.
- Each step is one atomic read or write. A read continuation receives the read
  value; a write continuation cannot inspect the overwritten value. Decisions
  persist. The scheduler is arbitrary: there is no fairness assumption. A crash
  is represented by a process no longer being scheduled.
- Inputs are private: each initial local state depends only on the process ID and
  its own input. Initial shared memory is independent of the input vector.
- The consensus model is single-shot, with proposals present initially. Transitions
  are total, including after a decision; termination is required only for processes
  that take infinitely many steps. In the operation trace, a decided process's
  subsequent steps do not count as steps of its completed operation.
- `Valent active c v` means that **no** `active`-only finite continuation reaches a
  configuration where **any** process has decided `!v`. Empty continuations are
  included. Nonvacuity is justified using solo termination, rather than built into
  the valency definition.
- `no_cof_consensus` needs three distinct process identifiers, not a finite process
  type. Thus additional processes can remain unscheduled. The `Fin n` specialization
  states the result directly for `3 ≤ n`.
- The universal-construction corollary uses a multi-shot model: implementations of
  arbitrary sequential objects, where the environment invokes operations on idle
  processes at arbitrary times and each process runs until its operation returns.
  `COFUniversal` asks, for every object, for an implementation whose every finite
  history is linearizable (Herlihy–Wing, with real-time order) and that satisfies
  the Section 3 COF condition over all its infinite executions. The proof runs such
  an implementation under a single-shot client, which is a consensus algorithm of
  the model above. The single-shot fragment `BinaryUniversal` is an intermediate
  step, proved to follow from the full notion (`binaryUniversal_of_cofUniversal`).
- The trace-level progress lemmas apply to one object and abstract valid traces;
  `TraceBridge.lean` connects them to concrete single-shot executions, including
  reachable execution suffixes. An explicit multi-object composition model is
  outside this development.
- The paper's two-process implementability remark (§4.1) cites the obstruction-free
  consensus algorithm of Attiya, Guerraoui, Hendler and Kuznetsov rather than proving
  it, so it is **assumed, not proved**. `TwoProcessCOFConsensus` states it, and
  `cofConsensusImplementable_fin_iff` takes it as an explicit hypothesis, never an
  axiom, to conclude that COF consensus for `n` processes is implementable iff
  `n ≤ 2`. `twoProcessCOFConsensus_iff_threshold` shows the hypothesis is exactly the
  two-process case of that conclusion, and `cofConsensusImplementable_of_trace` shows
  that the claim in the paper's own terms implies it. The impossibility results do not
  depend on it.

## Relationship to CSLib's FLP development

CSLib's `Cslib.Computability.Distributed.FLP` models message-passing consensus.
Its message-delivery diamonds and fairness assumptions do not provide an atomic
shared-memory model, so this result is not an instance of it: the read/write case
analysis and the paper's restricted valency argument are proved here, rather than
assumed or imported from the FLP impossibility theorem.

Earlier revisions imported CSLib's general `LTS`/`MTr` API and related it to
executable finite schedules via `mTr_iff_run`, but no result depended on it --- the
bridge was never used downstream. The dependency has been dropped, and the
development now builds against Mathlib alone.

## Details made explicit by the formal proof

1. A finite continuation need not terminate. The initial-valency lemma uses
   indistinguishability and validity alone; solo termination supplies deciding
   continuations where the subsequent argument needs them.
2. A bivalent state is undecided by agreement and decision persistence.
3. The infinite bivalent schedule need not schedule **both** active processes
   infinitely often. `two_process_infinite` proves that **at least one** is scheduled
   infinitely often, which is sufficient for the liveness contradiction.
4. `cofTermination_iff_initial` proves that quantifying termination over reachable
   starting configurations does not strengthen the initial-execution requirement.

`COF/Audit.lean` checks the foundational axiom dependencies of the principal
results. The expected dependencies are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axioms. It also
pins the statements of the headline theorems, which carry exactly the paper's
hypotheses, and the statement of the one cited hypothesis,
`TwoProcessCOFConsensus`, with the signature of the theorem that assumes it. It is part of the default build target,
so a regression fails `lake build`.

`COF/NonVacuity.lean` rules out the ways these impossibility results could be
empty: `consensus_satisfiable` shows `Safe` and `COFTermination` are jointly
satisfiable, `alt_not_homogeneous` shows the COF liveness clause genuinely
exempts schedules, so it is strictly weaker than wait-free termination, and
`cofUniversal_unit` shows that a COF universal construction exists for one
process, so the full notions are satisfiable.
