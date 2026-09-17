# Pending Conflicts Make Progress Impossible — Lean formalization

This project formalizes the main impossibility argument in
[`short_versionv2.tex`](short_versionv2.tex), using Lean 4 and Mathlib.

The development proves that a deterministic asynchronous read/write-register
algorithm cannot satisfy binary consensus safety and conflict-obstruction-free
termination when there are at least three processes. It also proves the
universal-construction reduction and the two progress-equivalence lemmas in
Section 3. There are no admitted proofs or project-specific axioms.

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

Names below are in `COF.SharedMemory.Algorithm`, unless otherwise qualified.

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
| Universal-construction impossibility (`cor:no_cof_univ`) | `COF.no_binaryUniversal` | `COF/Universal.lean` |
| Trace-level COF implies the concrete liveness condition | `objectCOF_of_trace_cof`, `no_linearizable_cof` | `COF/TraceBridge.lean` |

## Model and scope

- A configuration contains shared registers and a local state for each process.
  Register, register-value, and local-state types may be infinite.
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
- `BinaryUniversal` is a deliberately weak necessary fragment of universality: it
  asks for implementations of all sequential specifications with Boolean operations
  and responses, allowing register/value/local-state types to vary with the object.
  Safety requires one sequential ordering explaining all completed responses in each
  finite execution, optionally including pending invocations. All invocations
  overlap in this restricted client. Impossibility of this fragment suffices to rule
  out a full linearizable COF universal construction. A general history framework
  with repeated invocations and real-time ordering is **not** implemented here.
- The trace-level progress lemmas apply to one object and abstract valid traces;
  `TraceBridge.lean` connects them to concrete single-shot executions, including
  reachable execution suffixes. An explicit multi-object composition model and the
  paper's two-process implementability remark are outside this development.

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
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axioms. It is
part of the default build target, so a regression fails `lake build`.

`COF/NonVacuity.lean` rules out the two ways this impossibility result could be
empty: `consensus_satisfiable` shows `Safe` and `COFTermination` are jointly
satisfiable, and `alt_not_homogeneous` shows the COF liveness clause genuinely
exempts schedules, so it is strictly weaker than wait-free termination.
