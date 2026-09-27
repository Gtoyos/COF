import COF.Objects
import COF.Progress
import COF.Linearizability
import COF.SharedMemory.Algorithm
import COF.SharedMemory.Commutation
import COF.SharedMemory.Implementation
import COF.Consensus.Specification
import COF.Consensus.Valency
import COF.Consensus.CriticalSquare
import COF.Consensus.InitialBivalence
import COF.Consensus.BivalentSuccessor
import COF.Consensus.Impossibility
import COF.Consensus.Tightness
import COF.Universal.Client
import COF.Universal.Transfer
import COF.Universal.Construction
import COF.Paper

/-!
# Pending Conflicts Make Progress Impossible: a Lean formalization

Start with `COF.Paper`, which states every result of the paper in the paper's own terms. The
modules, in dependency order:

**Objects and progress conditions** (paper §2 and §3)
* `COF.Objects`: sequential objects, commutation, the conflict relation; the consensus object.
* `COF.Progress`: Definitions 1 and 2, obstruction freedom and wait freedom; Lemmas 1 and 2.
* `COF.Linearizability`: histories and Herlihy–Wing linearizability.

**The read/write model**
* `COF.SharedMemory.Algorithm`: consensus algorithms; configurations, steps and executions.
* `COF.SharedMemory.Commutation`: two steps commute, or one is invisible to all but its process.
* `COF.SharedMemory.Implementation`: implementations of objects, with repeated invocations.

**Theorem 6: no COF consensus for three or more processes** (§4.1 and §4.2)
* `COF.Consensus.Specification`: Validity, Agreement and COF termination.
* `COF.Consensus.Valency`: valency, and Lemma 3.
* `COF.Consensus.CriticalSquare`: the case analysis that ends the proofs of Lemmas 4 and 5.
* `COF.Consensus.InitialBivalence`: Lemma 4.
* `COF.Consensus.BivalentSuccessor`: Lemma 5.
* `COF.Consensus.Impossibility`: Theorem 6.
* `COF.Consensus.Tightness`: three is the threshold, given the cited two-process result.

**Corollary 7: no COF universal construction** (§4)
* `COF.Universal.Client`: an implementation run by processes that each propose once.
* `COF.Universal.Transfer`: linearizability and COF pass from the implementation to the client.
* `COF.Universal.Construction`: Corollary 7.

**Checks**, built with the library but not imported here:
* `COF.Checks.Audit`: every declaration uses only the standard axioms; the statements of the
  paper's results, and the definitions they use, are pinned.
* `COF.Checks.NonVacuity`: the hypotheses of the impossibility results are satisfiable.
* `COF.Checks.Separation`: COF termination is strictly weaker than wait-free termination.
* `COF.Checks.Lemma5Reachability`: Lemma 5 is false without its reachability hypothesis.
* `COF.Checks.Figure1`: the example of Figure 1, against Definitions 1 and 2.
* `COF.Checks.Linearizability`: linearizability accepts and rejects the right small histories.
-/
