import COF.Consensus.Tightness
import COF.Universal.Construction

/-!
# The paper's results

Every numbered result of *Pending Conflicts Make Progress Impossible* (Kuznetsov, Sutra,
Toyos-Marfurt), and the unnumbered claims its proofs rely on, stated in the paper's terms and
proved from the rest of the development. To check the formalization against the paper, read this
file and the definitions it uses, each of which quotes the paper.

* Definitions 1 and 2: `definition1`, `definition2`.
* Lemmas 1 and 2: `lemma1`, `lemma2`.
* §4.1, the conflict relation of the consensus object: `propose_commute_decided`,
  `propose_commute_undecided`, `propose_conflict_iff`; and "a COF consensus implementation
  satisfies COF termination": `cof_implementation_cofTermination`.
* §4.2, valency passes to descendants: `valent_descendant`.
* Lemma 3 (`init_config_1valent`), Lemma 4 (`init_tobivalent`), Lemma 5 (`bivalent_to_bivalent`):
  `lemma3`, `lemma4`, `lemma5`.
* Theorem 6 (`no_quasi_cons`): `theorem6`, with `theorem6_of_three` for any process type.
* Corollary 7 (`no_cof_univ`): `corollary7`, with `corollary7_of_three` for any process type.

Where a statement here differs from the paper's, it is stronger: fewer hypotheses, or more
processes. The paper's remark that COF consensus is implementable for two processes is cited from
the literature, not proved; `COF/Consensus/Tightness.lean` takes it as an explicit hypothesis.
-/

namespace COF.Paper
open SharedMemory

/-! ## Section 3: conflict-obstruction freedom -/

section Section3

/-- **Definition 1.** "An operation instance `Φ = (x,o,p)` is eventually conflict-step-contention
free in an execution `α` if either `Φ` completes in `α`, or there exists a suffix of `α` in which
no other operation `Φ' = (x,o',q)` takes steps such that `o ≍ o'`." -/
theorem definition1 {Inst Op : Type*} (t : Trace Inst Op) (conflict : Op → Op → Prop) (Φ : Inst) :
    t.EventuallyConflictFree conflict Φ ↔
      t.completed Φ ∨ ∃ N, ∀ k ≥ N, ∀ Φ', t.step k = some Φ' → Φ' ≠ Φ →
        ¬ conflict (t.operation Φ) (t.operation Φ') :=
  Iff.rfl

/-- **Definition 2.** "An implementation is conflict-obstruction-free if, for every infinite
execution `α` and every operation instance `Φ` invoked by a correct process such that `Φ` is
eventually conflict-step-contention free in `α`, `Φ` completes in `α`." -/
theorem definition2 {P R V S Q O Resp : Type*} (I : Implementation P R V S O Resp)
    (obj : Object Q O Resp) :
    I.ConflictObstructionFree obj.Conflict ↔
      ∀ (α : ℕ → Action P O) Φ, (I.trace α).invoked Φ → (I.trace α).correct Φ →
        (I.trace α).EventuallyConflictFree obj.Conflict Φ → (I.trace α).completed Φ :=
  ⟨fun h α => h _ ⟨α, rfl⟩, fun h _ ⟨α, hα⟩ => hα ▸ h α⟩

/-- **Lemma 1.** "Let `𝓘` be an implementation of a shared object `(Q,q₀,O,R,σ)`. If the induced
conflict relation satisfies `≍ = O×O` (i.e., every pair of operations conflicts), then `𝓘` is
conflict-obstruction-free iff `𝓘` is obstruction-free." -/
theorem lemma1 {P R V S Q O Resp : Type*} (I : Implementation P R V S O Resp)
    (obj : Object Q O Resp) (hfull : ∀ o o', obj.Conflict o o') :
    I.ConflictObstructionFree obj.Conflict ↔ I.ObstructionFree :=
  cof_iff_obstructionFree_of_full hfull

/-- **Lemma 2.** "Let `𝓘` be an implementation of a shared object `(Q,q₀,O,R,σ)`. If the induced
conflict relation is empty, `≍ = ∅` (i.e., all operations commute), then `𝓘` is
conflict-obstruction-free iff `𝓘` is wait-free." -/
theorem lemma2 {P R V S Q O Resp : Type*} (I : Implementation P R V S O Resp)
    (obj : Object Q O Resp) (hempty : ∀ o o', ¬ obj.Conflict o o') :
    I.ConflictObstructionFree obj.Conflict ↔ I.WaitFree :=
  cof_iff_waitFree_of_empty hempty

end Section3

/-! ## Section 4.1: conflict-obstruction-free consensus -/

section Section41

/-- "Any pair of `propose` operations commute in states `0` and `1`". -/
theorem propose_commute_decided (d v v' : Bool) : consensusObject.CommuteAt v v' (some d) :=
  consensus_commuteAt_decided d v v'

/-- "Two operations `propose(v)` and `propose(v')` commute in state `⊥` iff `v = v'`." -/
theorem propose_commute_undecided (v v' : Bool) :
    consensusObject.CommuteAt v v' none ↔ v = v' :=
  consensus_commuteAt_undecided_iff v v'

/-- "Thus, two proposals conflict if and only if they propose different values:
`propose(0) ≍ propose(1)`." -/
theorem propose_conflict_iff (v v' : Bool) : consensusObject.Conflict v v' ↔ v ≠ v' :=
  consensus_conflict_iff v v'

/-- "Thus, a COF consensus implementation satisfies COF termination": run by processes that each
propose once (the single-shot client), a conflict-obstruction-free implementation of the
consensus object satisfies COF termination. -/
theorem cof_implementation_cofTermination {P R V S : Type*}
    (I : Implementation P R V S Bool Bool)
    (h : I.ConflictObstructionFree consensusObject.Conflict) :
    I.singleShot.COFTermination :=
  I.singleShot.cofTermination_of_cofTerminationFor (Implementation.cofTerminationFor_singleShot h)

end Section41

/-! ## Section 4.2: the impossibility proof

"We consider a minimal model instance with three processes `{p₀, p₁, p₂}`, where `p₀` proposes `0`
and both `p₁` and `p₂` propose `1`." Here the processes are `0, 1, 2 : Fin 3`; the valency
definitions are those of `COF/Consensus/Valency.lean`, with the active processes `{p₁, p₂}`.

Lemmas 3–5 are stated in the paper for an algorithm implementing COF consensus. Each is stated
here with only the properties its proof uses. -/

section Section42
variable {R V S : Type*} (a : Algorithm (Fin 3) R V S)

/-- The input vector `(0,1,1)`. -/
def inputI : Fin 3 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true

/-- The input vector of `Algorithm.reachable_bivalent`, for `p₀ = 0`, is `(0,1,1)`. -/
theorem zeroAt_zero : Algorithm.zeroAt (0 : Fin 3) = inputI := by
  funext p
  match p with
  | 0 => exact Algorithm.zeroAt_self 0
  | 1 => exact Algorithm.zeroAt_of_ne (by decide)
  | 2 => exact Algorithm.zeroAt_of_ne (by decide)

/-- "Clearly, if a configuration `C` is `v`-valent and it has a descendant `C'`, `C ⇝π C'`, where
`π` is `{p₁,p₂}`-only, then `C'` is also `v`-valent." -/
theorem valent_descendant {C C' : Config (Fin 3) R V S} {v : Bool}
    (hv : a.Valent {1, 2} C v) (hπ : a.Reach {1, 2} C C') : a.Valent {1, 2} C' v :=
  a.valent_mono hv hπ

/-- **Lemma 3** (`init_config_1valent`). "The initial configuration `I` with input vector
`(0,1,1)` is `1`-valent." Only Validity is used. -/
theorem lemma3 (hval : a.Validity) : a.Valent {1, 2} (a.initial inputI) true := by
  apply a.initial_valent hval
  intro p hp
  rcases (show p = 1 ∨ p = 2 by simpa using hp) with rfl | rfl <;> rfl

/-- **Lemma 4** (`init_tobivalent`). "There exists a bivalent configuration reachable from `I`."
Only Validity and COF termination are used. -/
theorem lemma4 (hval : a.Validity) (ht : a.COFTermination) :
    ∃ C, a.Reachable inputI C ∧ a.Bivalent {1, 2} C := by
  have := a.reachable_bivalent hval ht 0 1 2 (by decide) (by decide) (by decide)
  rwa [zeroAt_zero] at this

/-- **Lemma 5** (`bivalent_to_bivalent`). "Any bivalent configuration `C` with `I ⇝ C` has an
enabled step `e` by a process in `{p₁,p₂}` such that the resulting configuration `C'` with
`C →e C'` is bivalent." Only COF termination is used. -/
theorem lemma5 (ht : a.COFTermination) {C : Config (Fin 3) R V S}
    (hC : a.Reachable inputI C) (hb : a.Bivalent {1, 2} C) :
    ∃ p ∈ ({1, 2} : Set (Fin 3)), a.Bivalent {1, 2} (a.step C p) := by
  rcases a.bivalent_successor ht (by decide) hC hb with h | h
  · exact ⟨1, by simp, h⟩
  · exact ⟨2, by simp, h⟩

end Section42

/-! ## Theorem 6 and Corollary 7 -/

/-- **Theorem 6** (`no_quasi_cons`). "No algorithm implements conflict-obstruction-free consensus
in the read-write shared memory model of three or more processes." -/
theorem theorem6 {n : ℕ} (hn : 3 ≤ n) {R V S : Type*} (a : Algorithm (Fin n) R V S) :
    ¬ (a.Validity ∧ a.Agreement ∧ a.COFTermination) :=
  a.no_cof_consensus_fin hn

/-- Theorem 6 for any set of processes with three distinct members, possibly infinitely many. -/
theorem theorem6_of_three {P R V S : Type*} (a : Algorithm P R V S) (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
    ¬ (a.Validity ∧ a.Agreement ∧ a.COFTermination) :=
  a.no_cof_consensus p₀ p₁ p₂ h₀₁ h₀₂ h₁₂

/-- **Corollary 7** (`no_cof_univ`). "No universal construction algorithm is
conflict-obstruction-free in the read-write shared memory model of three or more processes." -/
theorem corollary7 {n : ℕ} (hn : 3 ≤ n) : ¬ COFUniversal (Fin n) :=
  no_cofUniversal_fin hn

/-- Corollary 7 for any set of processes with three distinct members. -/
theorem corollary7_of_three {P : Type*} (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) : ¬ COFUniversal P :=
  no_cofUniversal p₀ p₁ p₂ h₀₁ h₀₂ h₁₂

end COF.Paper
