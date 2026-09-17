import COF

/-! Regression checks for the axiom dependencies of the paper results. These fail
if a proof is replaced by an admission or an additional axiom is introduced. -/

/-- info: 'COF.cof_iff_obstructionFree_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms COF.cof_iff_obstructionFree_of_full

/-- info: 'COF.cof_iff_waitFree_of_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms COF.cof_iff_waitFree_of_empty

/-- info: 'COF.SharedMemory.Algorithm.initial_valent' depends on axioms: [propext, Quot.sound] -/
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

