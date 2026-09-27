# Audit

How the formalization was checked against the paper, and what the build keeps checking.

## Verdict

The formalization matches every numbered result of the paper. Where a Lean statement differs
from the paper's, it is stronger. No finding is open.

One result is assumed rather than proved: the paper's remark that COF consensus is implementable
for two processes, which the paper cites from the literature. It is an explicit hypothesis of a
single theorem, the three-process threshold, and none of the paper's results depends on it.

## Scope

- **Paper**: `short_versionv2.tex`, in its version of 27 September 2026, where Lemma 5 is stated
  for configurations reachable from `I`.
- **Results**: Definitions 1 and 2, Lemmas 1 to 5, Theorem 6 and Corollary 7, and the unnumbered
  claims their proofs use. `COF/Paper.lean` lists them all.
- **Out of scope**: the two-process remark of §4.1, which is cited, and the introduction's
  informal example of a collection of queues.

## Method

1. **Reading.** The paper, and every Lean file, with each definition compared to the paper's text.
2. **Build.** A clean `lake build`, and a scan of the sources, with comments removed, for `sorry`,
   `axiom`, `native_decide`, `unsafe`, `extern`, custom syntax or instances, and option changes.
3. **Axioms.** The axioms of every declaration of the development.
4. **Independent restatement.** Definitions written from the paper's text alone: Validity and
   Agreement over executions, both readings of COF termination, and the paper's valency on three
   processes with input vector `(0,1,1)`. Each numbered result, stated with these definitions, was
   derived from the development's theorems. `COF/Paper.lean` now states the results in the same
   setting.
5. **Adversarial checks**, kept in `COF/Checks/`:
   - a counterexample to Lemma 5 without its reachability hypothesis;
   - an algorithm separating COF termination from wait-free termination;
   - the satisfiability of the hypotheses, including a linearizable COF implementation with three
     processes;
   - the paper's Figure 1, against Definitions 1 and 2;
   - linearizability on small histories.
6. **Regression guards.** In a copy of the project, each of the following failed the build:
   - a `sorry` in a proof that no pinned statement depends on;
   - Theorem 6 silently weakened from `3 ≤ n` to `4 ≤ n`;
   - a new `axiom`.

## Results

| Paper | `COF.Paper` | Verdict |
|---|---|---|
| Definition 1 | `definition1` | Exact |
| Definition 2 | `definition2` | Exact, over every infinite execution of an implementation |
| Lemma 1 | `lemma1` | Exact |
| Lemma 2 | `lemma2` | Exact |
| §4.1, commutation and conflicts of proposals | `propose_commute_decided`, `propose_commute_undecided`, `propose_conflict_iff` | Exact |
| §4.1, a COF consensus implementation satisfies COF termination | `cof_implementation_cofTermination` | Exact |
| §4.2, valency passes to descendants | `valent_descendant` | Exact |
| Lemma 3 | `lemma3` | Stronger: uses only Validity |
| Lemma 4 | `lemma4` | Stronger: uses only Validity and COF termination |
| Lemma 5 | `lemma5` | Stronger: uses only COF termination |
| Theorem 6 | `theorem6`, `theorem6_of_three`, `theorem6_strict` | Stronger: weaker liveness hypothesis; any process type with three members |
| Corollary 7 | `corollary7`, `corollary7_of_three` | Stronger: one implementation per object suffices, with types in any universe |

[`MODEL.md`](MODEL.md#differences-from-the-paper) explains each difference.

## Findings

Every finding of the audits of this development is resolved.

| Finding | Resolution |
|---|---|
| Lemma 5 was stated for any bivalent configuration; without reachability it is false | The manuscript now states it for `C` with `I ⇝ C`; `COF/Checks/Lemma5Reachability.lean` gives the counterexample |
| Lemma 3's proof invoked COF termination for arbitrary finite executions | Removed from the manuscript; the argument never needed it |
| Corollary 7 was proved only for a single-shot fragment of universality | Proved in full: `COFUniversal`, with Herlihy–Wing linearizability and Definition 2 |
| The main theorems assumed decidable equality of processes and registers | Removed; the model decides equality classically |
| A `sorry` outside the pinned theorems did not fail the build | Warnings are errors, and every declaration's axioms are checked |
| The documentation claimed a strict separation of COF and wait-free termination without proof | Proved: `COF/Checks/Separation.lean` |
| Non-vacuity of the multi-shot notions was checked for one process only | A three-process witness: `COF/Checks/NonVacuity.lean` |
| `COFUniversal` required implementation types in `Type` | They may now live in any universe |
| The documentation described earlier versions of the code and of the paper | Rewritten |

## What remains trusted

- **The definitions.** A formalization can only be as faithful as its definitions. Each quotes the
  paper, `MODEL.md` explains each modelling choice, the checks test the definitions on examples,
  and `COF/Checks/Audit.lean` records their exact text. They were compared with the paper by hand.
- **Lean's kernel and Mathlib.**
- **The two-process hypothesis**, for the threshold theorem only.

## Reproducing

```sh
lake build
```

This builds the development and every check. In particular, `COF/Checks/Audit.lean` fails the
build if any declaration depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`, or if the statement of a result of `COF/Paper.lean`, or a definition it is built
from, changes. When a change is intended, `#guard_msgs` prints the new text, which then replaces the
recorded one.
