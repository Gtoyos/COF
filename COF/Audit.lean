import COF

/-! Regression checks for the axiom dependencies of the paper results. These fail
if a proof is replaced by an admission or an additional axiom is introduced. -/

/-- info: 'COF.cof_iff_obstructionFree_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.cof_iff_obstructionFree_of_full

/-- info: 'COF.cof_iff_waitFree_of_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms COF.cof_iff_waitFree_of_empty

/--
info: 'COF.SharedMemory.Algorithm.initial_valent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.initial_valent

/-- info: 'COF.SharedMemory.Algorithm.reachable_bivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.reachable_bivalent

/-- info: 'COF.SharedMemory.Algorithm.bivalent_successor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.bivalent_successor

/-- info: 'COF.SharedMemory.Algorithm.no_cof_consensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.no_cof_consensus

/-- info: 'COF.SharedMemory.Algorithm.no_cof_consensus_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.no_cof_consensus_fin

/-- info: 'COF.no_binaryUniversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.no_binaryUniversal

/-- info: 'COF.SharedMemory.Algorithm.no_linearizable_cof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.SharedMemory.Algorithm.no_linearizable_cof

/-- info: 'COF.no_cofUniversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.no_cofUniversal

/-- info: 'COF.no_cofUniversal_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.no_cofUniversal_fin

/--
info: 'COF.binaryUniversal_of_cofUniversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms COF.binaryUniversal_of_cofUniversal

/--
info: 'COF.SharedMemory.Implementation.no_linearizable_cof_consensus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms COF.SharedMemory.Implementation.no_linearizable_cof_consensus

/-! The headline theorems carry exactly the paper's hypotheses: an algorithm, or a universal
construction, and three distinct processes. Nothing is assumed of the process or register
types, not even decidable equality: the model decides it classically. Their statements, and the
definition of a COF universal construction, are pinned. -/

/--
info: COF.SharedMemory.Algorithm.no_cof_consensus.{u_1, u_2, u_3, u_4} {P : Type u_1} {R : Type u_2} {V : Type u_3}
  {S : Type u_4} (a : COF.SharedMemory.Algorithm P R V S) (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀)
  (h₂₁ : p₂ ≠ p₁) : ¬a.Consensus
-/
#guard_msgs in
#check COF.SharedMemory.Algorithm.no_cof_consensus

/--
info: COF.no_cofUniversal.{u_1} {P : Type u_1} (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) :
  ¬COF.COFUniversal P
-/
#guard_msgs in
#check COF.no_cofUniversal

/--
info: def COF.COFUniversal.{u_1} : Type u_1 → Prop :=
fun P ↦
  ∀ (Q O Resp : Type) (obj : COF.Object Q O Resp),
    ∃ R V S I, I.Linearizable obj ∧ I.ConflictObstructionFree obj.Conflict
-/
#guard_msgs in
#print COF.COFUniversal

/-! The paper cites its two-process remark rather than proving it, and so does this
development: it enters only as the explicit hypothesis `TwoProcessCOFConsensus`, never as an
axiom, so it cannot show up in the axiom lists. Its statement and the signature of the theorem
that consumes it are pinned instead. -/

/-- info: def COF.TwoProcessCOFConsensus : Prop :=
COF.COFConsensusImplementable (Fin 2) -/
#guard_msgs in
#print COF.TwoProcessCOFConsensus

/-- info: COF.cofConsensusImplementable_fin_iff (h₂ : COF.TwoProcessCOFConsensus) (n : ℕ) :
  COF.COFConsensusImplementable (Fin n) ↔ n ≤ 2 -/
#guard_msgs in
#check COF.cofConsensusImplementable_fin_iff

/-- info: 'COF.cofConsensusImplementable_fin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.cofConsensusImplementable_fin_iff

/-- info: 'COF.twoProcessCOFConsensus_iff_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.twoProcessCOFConsensus_iff_threshold
