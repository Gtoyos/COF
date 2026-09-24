# The formal model

This document states exactly what the Lean development assumes and what it
proves, and records how each definition corresponds to the paper
(`short_versionv2.tex`, *Pending Conflicts Make Progress Impossible*).

Everything below is machine-checked. The development uses only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`); there are no
`sorry`s, no custom axioms, and no `native_decide`. `COF/Audit.lean` pins the
axiom footprint of each headline result and is part of the default build, so a
regression fails CI rather than passing with a warning.

One result is assumed, not proved: the paper's remark that COF consensus is
implementable for two processes, which the paper itself takes from the
literature. It is an explicit hypothesis of the one theorem that uses it, not an
axiom (§7).

---

## 1. What is proved

| Lean result | Paper |
|---|---|
| `SharedMemory.Algorithm.no_cof_consensus` (`COF/Impossibility.lean:84`) | Theorem `th:no_quasi_cons` — no COF consensus for ≥ 3 processes |
| `SharedMemory.Algorithm.no_cof_consensus_fin` (`COF/Impossibility.lean:92`) | same, for `Fin n` with `3 ≤ n` |
| `no_cofUniversal` (`COF/UniversalConstruction.lean:677`) | Corollary `cor:no_cof_univ` — no COF universal construction, with linearizability and COF in full (§6) |
| `no_cofUniversal_fin` (`COF/UniversalConstruction.lean:684`) | same, for `Fin n` with `3 ≤ n` |
| `SharedMemory.Implementation.no_linearizable_cof_consensus` (`COF/UniversalConstruction.lean:650`) | the corollary's core: no linearizable COF implementation of binary consensus for ≥ 3 processes |
| `SharedMemory.Algorithm.no_linearizable_cof` (`COF/TraceBridge.lean:76`) | the same impossibility, stated against the paper's own trace-level COF definition |
| `cofConsensusImplementable_fin_iff` (`COF/Tightness.lean:132`) | the remark in §4.1 that three processes is the exact threshold, **assuming** the cited two-process result (§7) |

Supporting lemmas map one-to-one onto the paper's:

| Lean | Paper |
|---|---|
| `initial_valent` (`COF/Valency.lean:115`) | Lemma `init_config_1valent` |
| `reachable_bivalent` (`COF/InitialBivalence.lean:72`) | Lemma `init_tobivalent` |
| `bivalent_successor` (`COF/Bivalence.lean:83`) | Lemma `bivalent_to_bivalent` |
| `cof_iff_obstructionFree_of_full` (`COF/Progress.lean`) | §3, first lemma (`≍ = O × O` ⟹ COF = OF) |
| `cof_iff_waitFree_of_empty` (`COF/Progress.lean`) | §3, second lemma (`≍ = ∅` ⟹ COF = WF) |

---

## 2. The computational model

Defined in `COF/SharedMemory/Model.lean`. Corresponds to the paper's
*System Model* and *Algorithms and executions* paragraphs (§2).

### Types

The model is parametric in four types, with no cardinality or finiteness
constraints on any of them:

- `P` — processes
- `R` — shared registers
- `V` — register values
- `S` — process-local state

`R`, `V`, `S` may be infinite. `P` may be infinite. Nothing else is assumed of
them, not even decidable equality: `step` has to tell which process and which
register it updates, and it decides that classically. So `step`, `run` and
`execution` are `noncomputable`, which is irrelevant for proofs, and no theorem
carries a decidability hypothesis. `COF/Audit.lean` pins the statements of the
headline theorems to keep it that way.

### An algorithm (`Algorithm`, line 35)

```lean
structure Algorithm (P R V S : Type*) where
  initialMemory : R → V
  initialState  : P → Bool → S
  instruction   : P → S → Instruction R V S
```

- **Deterministic.** `instruction` is a function of the process and its local
  state. No randomization. *(Paper: "Processes are deterministic.")*
- **Private inputs.** `initialState p b` depends only on `p`'s own input `b`.
- **Input-independent memory.** `initialMemory` does not depend on the input
  vector — shared memory cannot encode inputs for free.
- **Full generality otherwise.** `S` is arbitrary, so a process may remember
  its entire history; `R` is arbitrary, so there are arbitrarily many registers.

### A step (`Instruction` line 22, `step` line 61)

```lean
inductive Instruction (R V S : Type*) where
  | read  (register : R) (next : V → Local S)
  | write (register : R) (value : V) (next : Local S)
```

One step = one shared-memory event (a read *or* a write of one atomic register)
plus arbitrary local computation. *(Paper: "Each step consists of local
computation and one shared memory event — either a read or a write to an atomic
register.")*

The asymmetry is the crux of the whole proof and is deliberate: a **read**
continuation receives the value read (`V → Local S`); a **write** continuation
receives nothing from memory (`Local S`). This is what makes atomic registers
atomic registers. The model would be unsound for read-modify-write primitives
such as compare-and-swap, and `COF/SharedMemory/Commutation.lean:19` says so
explicitly.

### Local state and decisions (`Local`, line 14)

```lean
structure Local (S : Type*) where
  state    : S
  decision : Option Bool
```

`decision = none` means the invocation is still pending. `step` sets the new
decision to `old.decision.or next.decision`, so **decisions are irrevocable**:
once a process has decided, its decision never changes. *(Paper: "After each
step, `p` updates its local state and optionally returns a response on the
pending high-level operation.")*

Processes always have a next instruction, so a decided process may keep taking
steps. This is harmless — liveness only ever concerns processes that have not
decided — and it avoids having to model halting.

### Configurations, schedules, crashes

- `Config` (line 29) = shared memory (`R → V`) together with every process's
  local state (`P → Local S`). *(Paper: "A configuration represents a complete
  system state, that is, the local states of all processes together with the
  state of the shared memory.")*
- `run` (line 71) executes a finite schedule (`List P`); `execution` (line 214)
  executes an infinite one (`ℕ → P`).
- **The scheduler is arbitrary.** A schedule is any function `ℕ → P`. No
  fairness, no bound on relative speeds, no timing assumptions. *(Paper: "There
  is no bound on relative process speeds, and no assumptions are made about
  timing or scheduling fairness.")*
- **A crash is simply never being scheduled again.** Any number of processes may
  crash, at any point. There is no failure detector and no bound on failures.
- `Reach active c d` (line 87) — `d` is reachable from `c` scheduling only
  processes in `active`. `Reachable input c` (line 92) = reachable from the
  initial configuration for `input`, with no restriction on who takes steps.
- `Indist observers c d` (line 168) — equal shared memory, and equal local state
  for every process in `observers`. This is the indistinguishability relation
  used throughout.

### The read/write case analysis

`commutation_or_erasure` (`COF/SharedMemory/Commutation.lean:22`) is the one
place where "atomic read-write register" does real work. For `p ≠ q`, either

1. the two steps commute outright, or
2. `p`'s step followed by `q`'s is indistinguishable from `q`'s step alone, to
   everyone **except `p`**, or
3. symmetrically with `p` and `q` exchanged.

Cases 2 and 3 are the erasure cases: a step of `p` leaves no trace for anyone
else either because it was a read (reads do not touch memory) or because it was
a write that `q` immediately overwrote. Because the erased-step process is
excluded from the observers, an argument that needs an observer requires a
*third* process — which is precisely why the impossibility needs three processes
and not two.

---

## 3. Objects and the conflict relation

`COF/Objects.lean`. A sequential object is `(State, Operation, Response)` with
an initial state and a transition function — the paper's `(Q, q₀, O, R, σ)`.

`CommuteAt a b s` (line 18) requires **both** that the final state agrees and
that each operation returns the same response in either order. `Conflict a b`
(line 27) is `∃ s, ¬ CommuteAt a b s`: quantified over *all* object states, not
just reachable ones.

> Paper: "we say that they *commute* in a state `q` if `o·o'(q) = o'·o(q)` and
> each operation returns the same result in both sequences"; "`o ≍ o'` if there
> **exists** a state `q` in which `o` and `o'` do not commute."

`consensusObject` (line 41) is binary consensus: state `Option Bool` with `none`
undecided, the first proposal wins, later proposals return the stored value.
`consensus_conflict_iff` (line 60) proves the paper's claim that
`propose(v) ≍ propose(w) ↔ v ≠ w`.

---

## 4. Progress conditions

`COF/Progress.lean` states the paper's §3 definitions at the trace level,
independently of any particular implementation. A `Trace` records, per operation
instance, its operation, and whether it was invoked / is by a correct process /
completed, plus a step function `ℕ → Option Instance`.

Crucially, `step k = none` marks an idle step: **steps of already-completed
invocations do not count as contention.** This matches the paper's "`Φ` takes a
step when the process `p` that invoked `Φ` takes a step *and `Φ` has not yet
returned a response*".

- `EventuallyConflictFree` (line 29) — `Φ` completes, or some suffix contains no
  step of a *conflicting* other instance.
- `ConflictObstructionFree` (line 71) — every invoked instance of a correct
  process that is eventually conflict-free completes.
- `ObstructionFree` (line 76), `WaitFree` (line 80) — the standard conditions.

The two sanity lemmas from §3 are proved: conflict relation `= O × O` collapses
COF to OF; empty conflict relation collapses COF to wait-freedom.

---

## 5. The consensus specification

`COF/Valency.lean` and `COF/Termination.lean`. `Consensus := Safe ∧ COFTermination`.

### Safety (`Safe`, `COF/Valency.lean:23`)

For every input vector and every reachable configuration:

- **Agreement** — `∀ v w, c.Decided v → c.Decided w → v = w`
- **Validity** — `∀ v, c.Decided v → ∃ p, input p = v`

`c.Decided v` means *some* process has decided `v`.

### Liveness (`COFTermination`, `COF/Termination.lean:19`)

> Paper: "**COF termination:** If eventually only processes that proposed the
> same value take steps, then every correct process decides in finitely many
> steps."

```lean
∀ input c, a.Reachable input c → ∀ schedule : ℕ → P,
  (∃ N v, ∀ k ≥ N, input (schedule k) = v) →        -- eventually homogeneous
  ∀ p, (∀ N, ∃ k ≥ N, schedule k = p) →             -- p is correct
    ∃ n v, ((a.execution c schedule n).proc p).decision = some v
```

Two modelling choices worth stating:

- **"Correct" = takes infinitely many steps.** This is the paper's own
  definition ("a process is *correct* if it takes an infinite number of steps or
  it has no pending operation").
- **Quantifying over reachable `c` adds nothing.** One might worry that
  requiring termination from every reachable configuration is stronger than the
  paper's "every execution has a conflict-free suffix ⟹ termination".
  `cofTermination_iff_initial` (`COF/Termination.lean:39`) proves the two forms
  equivalent, by prepending the finite prefix to the infinite schedule.

### Valency

`Valent active c v := ¬ CanDecide active c (!v)` (`COF/Valency.lean:40`) — the
paper's *negative* notion ("the initial configuration with input vector (0,1,1)
is 1-valent" = no execution from it decides 0), restricted to continuations that
schedule only `active`.

Under this negative reading, a configuration from which *nothing* can ever be
decided is both 0-valent and 1-valent. That is intentional and is handled
correctly: `Bivalent` is positively characterised by `bivalent_iff` as "both
values are still decidable", and every step that needs valencies to be exclusive
goes through `solo_terminates`, which uses `COFTermination` to produce an actual
decision. `not_both_valent` (`COF/Valency.lean:102`) records the side condition.

---

## 6. The universal-construction corollary

The paper's Corollary `cor:no_cof_univ` concerns a universal construction: "an
algorithm that takes as input a sequential object specification and produces a
linearizable shared-memory implementation satisfying COF termination". It is
stated here with the full notions, in a model with repeated invocations, and
proved by the paper's reduction to consensus.

### The multi-shot model

`COF/SharedMemory/Implementation.lean`. An `Implementation P R V S O Resp`
implements an object with operations `O` and responses `Resp` by one
deterministic automaton per process:

```lean
structure Implementation (P R V S O Resp : Type*) where
  initialMemory : R → V
  initialState  : P → S
  invoke        : P → O → S → S                      -- absorb an invocation
  instruction   : P → S → OpInstruction R V S Resp   -- next step while pending
```

As in §2, a step is one read or one write plus local computation: a read
continuation sees the value read, a write continuation sees nothing, and a step
may return a response. The environment invokes operations on idle processes, at
arbitrary times (`Action.invoke p o`). A process with a pending operation takes
steps when scheduled (`Action.step p`), until one returns. Processes take steps
only while executing an operation, so invoking a busy process or scheduling an
idle one does nothing. Executions are arbitrary sequences of actions from the
initial configuration: there is no fairness, and a crash is a process no longer
scheduled. A configuration also records each process's pending operation and
number of returned operations, as bookkeeping the automaton cannot see.

### Histories and linearizability

`COF/Linearizability.lean`. The history of a finite execution lists its operation
instances, each an interval (`OpRecord`): process, operation, invocation time,
and, once it has returned, response and response time. `Linearizable obj H` is
Herlihy and Wing's condition: some sequence `S` of distinct instances of `H`,
each paired with a response,

- contains every completed instance with its actual response, while a pending
  instance may be included with a response chosen for it, or dropped;
- is legal for the sequential specification (`Object.Legal`); and
- respects real-time order: no instance is placed after one that returned before
  it was invoked.

An implementation is linearizable when every finite execution has a
linearizable history (`Implementation.Linearizable`).

### Conflict-obstruction freedom

`Implementation.trace` presents an infinite execution as a `Trace` (§4). The
operation instance `(p, k, o)` is `p`'s `k`-th invocation, of `o`. A step belongs
to the scheduled process's pending instance, and a process is correct if it
takes infinitely many steps or eventually has no pending operation.
`Implementation.ConflictObstructionFree` is the paper's §3 condition,
`ConflictObstructionFree` of `COF/Progress.lean`, over the traces of *all*
infinite executions from the initial configuration.

### The corollary

`COF/UniversalConstruction.lean`:

```lean
def COFUniversal (P : Type*) : Prop :=
  ∀ (Q O Resp : Type) (obj : Object Q O Resp),
    ∃ (R V S : Type) (I : Implementation P R V S O Resp),
      I.Linearizable obj ∧ I.ConflictObstructionFree obj.Conflict

theorem no_cofUniversal (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) : ¬ COFUniversal P
```

The proof is the paper's. `singleShot` runs an implementation of a binary object
under a single-shot client: at its first step, a process invokes the operation
its input names, and it decides the response. This client is an `Algorithm` of
§2, and `embed_step` proves that it is the implementation, step for step: each
client step is one action of the implementation. Linearizability of the implementation yields `Linearizes` for
the client (`linearizes_singleShot`), and its COF yields `ObjectCOF`
(`objectCOF_singleShot`). At the consensus object these give `Safe` and
`COFTermination`, which `no_cof_consensus` refutes
(`Implementation.no_linearizable_cof_consensus`).

### The single-shot fragments

`COF/Universal.lean` defines the single-shot fragments that the reduction passes
through:

- `Linearizes obj` — from every reachable configuration, a single duplicate-free
  sequential order of invocations accounts for every decision.
- `ObjectCOF obj` — per-process conflict-free termination, for single-shot
  executions.
- `BinaryUniversal P` — for every binary object, an algorithm satisfying both.

`binaryUniversal_of_cofUniversal` proves that the full notion implies the
fragment, for the same processes, so the fragment is a consequence of the full
notion rather than a stand-in for it.
`safe_of_consensus_linearizes` and `termination_of_consensus_objectCOF` turn the
fragments for `consensusObject` into `Safe` and `COFTermination`.
`COF/TraceBridge.lean` relates the fragment to the paper's trace-level condition
directly, for single-shot executions: `objectCOF_of_trace_cof` derives
`ObjectCOF` from `ConflictObstructionFree`.

---

## 7. The cited two-process result: a hypothesis

`COF/Tightness.lean`. The paper states (§4.1) that COF consensus *is* implementable
in the read–write model for two processes, which is what makes three the exact
threshold. It does not prove this. It cites the obstruction-free consensus algorithm
of Attiya, Guerraoui, Hendler and Kuznetsov (*The complexity of obstruction-free
implementations*, JACM 56(4), 2009), which terminates in solo runs and whenever all
processes propose the same value; for two processes, those two guarantees together
are exactly COF termination. Constructing and verifying that algorithm is outside
the scope of the paper, and of this development. The result is therefore
**assumed, not proved**:

```lean
def COFConsensusImplementable (P : Type*) : Prop :=
  ∃ (R V S : Type) (a : Algorithm P R V S), a.Consensus

def TwoProcessCOFConsensus : Prop := COFConsensusImplementable (Fin 2)
```

- **A hypothesis, not an axiom.** `TwoProcessCOFConsensus` is an ordinary
  proposition. The theorem that needs it takes it as an explicit argument, so the
  dependency is visible in that theorem's statement, and nothing else depends on it:
  the impossibility theorems, the universality reduction and the trace bridge are
  unconditional. An `axiom` would instead be global and invisible in the statements
  that rely on it, and a misstated one could make the whole development
  inconsistent. `COF/Audit.lean` pins the hypothesis and the signature of the
  theorem that assumes it.
- **What it is used for.** The paper uses the remark to show that its
  three-process bound is tight, and so does the development:

  ```lean
  theorem cofConsensusImplementable_fin_iff (h₂ : TwoProcessCOFConsensus) (n : ℕ) :
      COFConsensusImplementable (Fin n) ↔ n ≤ 2
  ```

  The hypothesis is used for `n = 2` only. The case `n ≥ 3` is
  `no_cof_consensus_fin`, and `n ≤ 1` is proved outright with the trivial algorithm
  `decideOwnInput`, in which each process decides its own input at its first step.
- **No more than needed.** `twoProcessCOFConsensus_iff_threshold` proves the
  hypothesis *equivalent* to the threshold statement: it is exactly the part of
  that conclusion not proved here.
- **No more than the paper claims.** The hypothesis is stated with `Consensus`, the
  notion that `no_cof_consensus` refutes, so the threshold theorem speaks of a
  single notion throughout. Its liveness clause `COFTermination` is weaker than the
  paper's (§9, item 1), and `cofConsensusImplementable_of_trace` proves that the
  claim in the paper's own terms implies the hypothesis: `Safe` together with the
  §3 trace-level `ConflictObstructionFree` for `consensusObject`, required only of
  the paper's executions, those from an initial configuration (`InitialTrace`).
  The bridge is `cofTermination_of_initial_trace_cof` (`COF/TraceBridge.lean`).
- **Trusted, not checked.** If the hypothesis failed in this model, the threshold
  theorem would hold vacuously. It rests on the cited algorithm alone. The
  impossibility results do not depend on it either way.

---

## 8. Complete list of assumptions

The impossibility theorem assumes **only**:

1. The algorithm fits the model of §2 — deterministic, atomic read/write
   registers, private inputs.
2. `Safe` — agreement and validity.
3. `COFTermination` — the paper's COF liveness clause.
4. Three distinct processes exist (`p₀ ≠ p₁`, `p₂ ≠ p₀`, `p₂ ≠ p₁`).

Nothing else. In particular the following are **not** assumed:

- no bound on the number of processes (`P` may be infinite; processes other than
  the three named ones need never take a step)
- no finiteness of registers, values, or local states
- no decidable equality of processes or registers, nor anything else about their
  types (§2)
- no fairness, no synchrony, no failure bound, no failure detector
- no bound on how many processes crash
- no restriction on which configurations the scheduler may visit

The universal-construction corollary `no_cofUniversal` likewise assumes only a
`COFUniversal` construction, with the full notions of §6, and three distinct
processes.

These are the assumptions of the impossibility results. The one theorem that goes
beyond them, `cofConsensusImplementable_fin_iff`, additionally takes the cited
two-process result `TwoProcessCOFConsensus` (§7) as an explicit hypothesis.

---

## 9. Where the formalization departs from the paper

Every departure makes the theorem **stronger** (a weaker hypothesis, or a more
careful proof). None weakens it.

1. **`COFTermination` counts steps of decided processes.** The homogeneity
   premise `∀ k ≥ N, input (schedule k) = v` constrains *all* steps after `N`,
   including those of processes that have already decided; the paper's condition
   ignores completed invocations. This constrains *fewer* schedules, so it is a
   *weaker* liveness assumption and the impossibility is stronger. The
   paper-faithful version lives in `COF/Progress.lean` + `COF/TraceBridge.lean`
   and is proved to imply this one, so nothing is lost. The two-process hypothesis
   of §7 uses the same clause, so it too assumes less than the paper's claim.

2. **Only one of the two active processes need be scheduled infinitely often.**
   The paper's proof of `th:no_quasi_cons` says "both `p₁` and `p₂` are required
   to complete their operations". The schedule built by the bivalence argument
   need not schedule both infinitely often — it may starve one. The Lean proof
   uses `two_process_infinite` (`COF/Impossibility.lean:15`) to extract whichever
   of the two *is* scheduled infinitely often, and derives the contradiction from
   that one alone. This closes a small gap in the written proof.

3. **`reachable_bivalent` is stated for an arbitrary process type** containing
   three distinct processes, rather than for a three-process system. Other
   processes may exist and simply never be scheduled.

4. **A universal construction is asked of each object separately.** The paper's
   construction is one algorithm taking the specification as input;
   `COFUniversal` asks only that each object, with types in `Type`, have some
   implementation. A uniform algorithm provides such a family, so this is a
   weaker hypothesis and the corollary is stronger.

---

## 10. Scope limitations

These match the paper and are stated here so they are not mistaken for gaps:

- **Deterministic algorithms only.** Randomized algorithms are outside the model,
  as in the paper (and as in FLP).
- **Atomic read/write registers only.** The result is false for stronger
  primitives; `commutation_or_erasure` is exactly where this is used.
- **Binary consensus.** The impossibility is for binary consensus, the easiest
  case, which makes it stronger. The universal-construction corollary uses only
  the construction's implementation of the binary consensus object.
- **One object at a time.** The multi-shot model implements a single object, as
  the corollary requires; a model of several objects composed together is not
  needed and is not formalized.
- **The two-process converse is assumed, not proved** (§7). The paper notes
  (§4.1) that COF consensus *is* implementable for two processes, which is what
  makes the three-process bound tight, and cites rather than proves it.
  `TwoProcessCOFConsensus` states it, and only `cofConsensusImplementable_fin_iff`
  assumes it; the impossibility does not depend on it.

---

## 11. Non-vacuity

An impossibility theorem is worthless if its hypotheses are unsatisfiable.
`COF/NonVacuity.lean` is part of the build and proves three things:

- `consensus_satisfiable` — `∃ a, a.Consensus`. `Safe` and `COFTermination` are
  jointly satisfiable (witness: `decideOwnInput` on one process, which decides its
  own input at its first step), so `no_cof_consensus` is not true merely because
  its hypotheses contradict each other.
- `alt_not_homogeneous` — the alternating schedule over two processes with
  opposite inputs is not eventually homogeneous. So `COFTermination` genuinely
  exempts some schedules and is strictly weaker than wait-free termination: the
  result is not a restatement of FLP.
- `cofUniversal_unit` — `COFUniversal Unit`. With one process, every object has a
  linearizable, wait-free implementation: the process keeps the object's state
  and answers each operation at its first step (`seqImpl`). So the full notions
  of §6 are satisfiable, and `no_cofUniversal` really needs its three processes.

The hypothesis of the threshold theorem is a different matter: it is the cited
result itself, so its non-vacuity is exactly what is assumed (§7).

---

## 12. Dependencies and verification

The development depends on **Mathlib only**. It is self-contained: it does not
use CSLib's FLP proof, and does not derive the result from FLP.

```bash
lake build
```

builds every module, including `COF/Audit.lean` (which pins the axiom footprint
of each headline theorem via `#guard_msgs`) and `COF/NonVacuity.lean`. Replacing
any proof with `sorry` fails the build.
