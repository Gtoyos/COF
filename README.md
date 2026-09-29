# Pending Conflicts Make Progress Impossible: a Lean Formalization

A Lean 4 and Mathlib formalization of *Pending Conflicts Make Progress Impossible* [1].

It formalizes the model of the paper and proves every numbered result:

- **Theorem 6.** No read/write algorithm implements conflict-obstruction-free (COF) consensus for
  three or more processes.
- **Corollary 7.** No universal construction is conflict-obstruction-free in the read/write model
  for three or more processes.
- **Lemmas 1 and 2** (COF versus obstruction freedom and wait freedom), and
  **Lemmas 3 to 5** (the valency argument behind Theorem 6).

Every proof uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
`lake build` checks this, and also fails on any warning (including `sorry`) and on any change to
the statements recorded in [`COF/Checks/Audit.lean`](COF/Checks/Audit.lean).

## Where to start

Read [`COF/Paper.lean`](COF/Paper.lean). It states each result in the paper's terms, next to the
paper's own wording, and proves it from the rest of the development.
[`MODEL.md`](MODEL.md) explains the formal model and how it corresponds to the paper.

## Building

```sh
lake build
```

The Lean and Mathlib versions are pinned by `lean-toolchain` and `lake-manifest.json`.

## The results

The Lean statements are in [`COF/Paper.lean`](COF/Paper.lean). Where one differs from the paper's,
it is stronger (it assumes less, or holds for more processes);
[`MODEL.md`](MODEL.md#differences-from-the-paper) lists each difference.

| Paper | Proof |
|---|---|
| Definitions 1 and 2 (conflict-obstruction-free) | `COF/Progress.lean` |
| Lemmas 1 and 2 (COF vs OF vs WF) | `COF/Progress.lean` |
| §4.1: consensus proposals conflict iff they differ | `COF/Objects.lean` |
| Lemma 3 (the initial configuration $I=(0,1,1)$ is 1-valent) | `COF/Consensus/Valency.lean` |
| Lemma 4 (a bivalent configuration is reachable from $I$) | `COF/Consensus/InitialBivalence.lean` |
| Lemma 5 (a bivalent configuration is reachable from any reachable bivalent one) | `COF/Consensus/BivalentSuccessor.lean` |
| Theorem 6 (no read/write COF consensus algorithm for $n \geq 3$) | `COF/Consensus/Impossibility.lean` |
| Corollary 7 (no read/write COF universal construction for $n \geq 3$) | `COF/Universal/Construction.lean` |

The paper remarks that COF consensus *is* implementable for two processes, citing
Attiya, Guerraoui, Hendler and Kuznetsov (JACM, 2009). That result is outside the paper's proofs
and is not formalized.
[`COF/Consensus/Tightness.lean`](COF/Consensus/Tightness.lean) states it as the explicit hypothesis
`TwoProcessCOFConsensus` and derives from it that three processes is the exact threshold. Nothing
else depends on it.

## Layout

```text
COF.lean                 imports the development; a guide to its modules
COF/
  Paper.lean             every result of the paper, in its terms
  Objects.lean           sequential objects, commutation, conflicts; the consensus object
  Progress.lean          Definitions 1 and 2, obstruction and wait freedom; Lemmas 1 and 2
  Linearizability.lean   histories; Herlihy–Wing linearizability
  SharedMemory/          the read/write model: consensus algorithms, implementations of objects,
                         and the read/write case analysis
  Consensus/             Theorem 6: the specification, valency, Lemmas 3 to 5, the theorem, and
                         the threshold
  Universal/             Corollary 7: an implementation run as a consensus algorithm
  Checks/                the audit, and checks that the hypotheses are satisfiable, that COF
                         termination is strictly weaker than wait-free termination, that Lemma 5
                         needs reachability, and that the definitions behave on the paper's
                         Figure 1 and on small histories
```

## References

- [1] Petr Kuznetsov, Pierre Sutra, Guillermo Toyos-Marfurt, Pending conflicts make progress impossible, Information Processing Letters, Volume 196, 2027, 106668, ISSN 0020-0190, 10.1016/j.ipl.2026.106668.
