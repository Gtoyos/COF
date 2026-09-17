# The formal model

This document states exactly what the Lean development assumes and what it
proves, and records how each definition corresponds to the paper
(`short_versionv2.tex`, *Pending Conflicts Make Progress Impossible*).

Everything below is machine-checked. The development uses only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`); there are no
`sorry`s, no custom axioms, and no `native_decide`. `COF/Audit.lean` pins the
axiom footprint of each headline result and is part of the default build, so a
regression fails CI rather than passing with a warning.

---

## 1. What is proved

| Lean result | Paper |
|---|---|
| `SharedMemory.Algorithm.no_cof_consensus` (`COF/Impossibility.lean:85`) | Theorem `th:no_quasi_cons` — no COF consensus for ≥ 3 processes |
| `SharedMemory.Algorithm.no_cof_consensus_fin` (`COF/Impossibility.lean:93`) | same, for `Fin n` with `3 ≤ n` |
| `no_binaryUniversal` (`COF/Universal.lean:111`) | Corollary `cor:no_cof_univ` — no COF universal construction |
| `SharedMemory.Algorithm.no_linearizable_cof` (`COF/TraceBridge.lean:51`) | the same impossibility, stated against the paper's own trace-level COF definition |

Supporting lemmas map one-to-one onto the paper's:

| Lean | Paper |
|---|---|
| `initial_valent` (`COF/Valency.lean:115`) | Lemma `init_config_1valent` |
| `reachable_bivalent` (`COF/InitialBivalence.lean:71`) | Lemma `init_tobivalent` |
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

`R`, `V`, `S` may be infinite. `P` may be infinite. The only requirement is
`DecidableEq P` and `DecidableEq R`, which is not a restriction: any type admits
such an instance classically, and it is used purely so `Function.update` computes.

### An algorithm (`Algorithm`, line 34)

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

### A step (`Instruction` line 21, `step` line 55)

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

### Local state and decisions (`Local`, line 13)

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

- `Config` (line 28) = shared memory (`R → V`) together with every process's
  local state (`P → Local S`). *(Paper: "A configuration represents a complete
  system state, that is, the local states of all processes together with the
  state of the shared memory.")*
- `run` (line 65) executes a finite schedule (`List P`); `execution` (line 209)
  executes an infinite one (`ℕ → P`).
- **The scheduler is arbitrary.** A schedule is any function `ℕ → P`. No
  fairness, no bound on relative speeds, no timing assumptions. *(Paper: "There
  is no bound on relative process speeds, and no assumptions are made about
  timing or scheduling fairness.")*
- **A crash is simply never being scheduled again.** Any number of processes may
  crash, at any point. There is no failure detector and no bound on failures.
- `Reach active c d` (line 81) — `d` is reachable from `c` scheduling only
  processes in `active`. `Reachable input c` (line 86) = reachable from the
  initial configuration for `input`, with no restriction on who takes steps.
- `Indist observers c d` (line 162) — equal shared memory, and equal local state
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

## 6. The universality reduction

`COF/Universal.lean`. Both hypotheses are deliberately *weak* — they are
necessary fragments of the real conditions, so refuting them refutes the real
thing.

- `Linearizes obj` (line 47) — from every reachable configuration there is a
  single duplicate-free sequential order of invocations whose responses account
  for *every* decision in that configuration. One order is shared by all
  decisions, not chosen per decision. This is implied by, and much weaker than,
  full linearizability.
- `ObjectCOF obj` (line 54) — per-process conflict-free termination, restricted
  to single-shot executions.
- `BinaryUniversal P` (line 103) — for *every* binary object there exist register,
  value and state types and an algorithm satisfying the two fragments above.

`safe_of_consensus_linearizes` derives agreement and validity from
linearizability of `consensusObject`; `termination_of_consensus_objectCOF`
derives `COFTermination` from `ObjectCOF consensusObject`. All invocations are
present initially, so their intervals overlap and any of them may be linearized.

`COF/TraceBridge.lean` closes the loop: `objectCOF_of_trace_cof` derives
`ObjectCOF` from the paper's trace-level `ConflictObstructionFree`, so
`no_linearizable_cof` is stated directly against the §3 definition rather than
against a hand-tailored liveness clause.

---

## 7. Complete list of assumptions

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
- no fairness, no synchrony, no failure bound, no failure detector
- no bound on how many processes crash
- no restriction on which configurations the scheduler may visit

---

## 8. Where the formalization departs from the paper

Every departure makes the theorem **stronger** (a weaker hypothesis, or a more
careful proof). None weakens it.

1. **`COFTermination` counts steps of decided processes.** The homogeneity
   premise `∀ k ≥ N, input (schedule k) = v` constrains *all* steps after `N`,
   including those of processes that have already decided; the paper's condition
   ignores completed invocations. This constrains *fewer* schedules, so it is a
   *weaker* liveness assumption and the impossibility is stronger. The
   paper-faithful version lives in `COF/Progress.lean` + `COF/TraceBridge.lean`
   and is proved to imply this one, so nothing is lost.

2. **Only one of the two active processes need be scheduled infinitely often.**
   The paper's proof of `th:no_quasi_cons` says "both `p₁` and `p₂` are required
   to complete their operations". The schedule built by the bivalence argument
   need not schedule both infinitely often — it may starve one. The Lean proof
   uses `two_process_infinite` (`COF/Impossibility.lean:16`) to extract whichever
   of the two *is* scheduled infinitely often, and derives the contradiction from
   that one alone. This closes a small gap in the written proof.

3. **`reachable_bivalent` is stated for an arbitrary process type** containing
   three distinct processes, rather than for a three-process system. Other
   processes may exist and simply never be scheduled.

4. **Linearizability and universality are replaced by necessary fragments**
   (§6), which strengthens the corollary.

---

## 9. Scope limitations

These match the paper and are stated here so they are not mistaken for gaps:

- **Deterministic algorithms only.** Randomized algorithms are outside the model,
  as in the paper (and as in FLP).
- **Atomic read/write registers only.** The result is false for stronger
  primitives; `commutation_or_erasure` is exactly where this is used.
- **Binary consensus**, and **single-shot** invocations for the universality
  reduction. Both make the impossibility stronger, since binary single-shot
  consensus is the easiest case.
- **The converse for two processes is not formalized.** The paper notes (§4.1)
  that COF consensus *is* implementable for two processes, which is what makes
  the three-process bound tight. That direction is out of scope here; the
  impossibility does not depend on it.

---

## 10. Non-vacuity

An impossibility theorem is worthless if its hypotheses are unsatisfiable.
`COF/NonVacuity.lean` is part of the build and proves two things:

- `consensus_satisfiable` — `∃ a, a.Consensus`. `Safe` and `COFTermination` are
  jointly satisfiable (witness: a one-process system that decides its own
  input), so `no_cof_consensus` is not true merely because its hypotheses
  contradict each other.
- `alt_not_homogeneous` — the alternating schedule over two processes with
  opposite inputs is not eventually homogeneous. So `COFTermination` genuinely
  exempts some schedules and is strictly weaker than wait-free termination: the
  result is not a restatement of FLP.

---

## 11. Dependencies and verification

The development depends on **Mathlib only**. It is self-contained: it does not
use CSLib's FLP proof, and does not derive the result from FLP.

```bash
lake build
```

builds every module, including `COF/Audit.lean` (which pins the axiom footprint
of each headline theorem via `#guard_msgs`) and `COF/NonVacuity.lean`. Replacing
any proof with `sorry` fails the build.
