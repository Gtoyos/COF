import COF
import COF.Checks.NonVacuity
import COF.Checks.Separation
import COF.Checks.Lemma5Reachability
import COF.Checks.Figure1
import COF.Checks.Linearizability

/-!
# Audit

These checks run with `lake build`, and each one fails the build if what it checks changes.

1. **Axioms.** Every declaration in the `COF` namespace, checks included, depends only on Lean's
   standard axioms `propext`, `Classical.choice` and `Quot.sound`. A `sorry` (`sorryAx`), a
   `native_decide` (`Lean.ofReduceBool`) or a new `axiom` anywhere fails the build. (Warnings
   are errors too, see `lakefile.toml`, so a `sorry` fails twice over.)
2. **Statements.** `#check` prints the statement of every result of `COF/Paper.lean`, and
   `#guard_msgs` compares it with the text recorded here. A statement cannot change, gain a
   hypothesis or lose generality without this file changing too.
3. **Definitions.** `#print` does the same for the definitions those statements are built from,
   so this file is also a snapshot of the whole specification.

The recorded texts are Lean's own output. When a change is intended, `#guard_msgs` reports the new
text, which replaces the old one here.
-/

set_option linter.style.longLine false

-- Every declaration in the `COF` namespace depends only on the standard axioms.
open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut offending : Array MessageData := #[]
  for (name, _) in (← getEnv).constants.toList do
    if (`COF).isPrefixOf name then
      for ax in ← collectAxioms name do
        unless standard.contains ax do
          offending := offending.push m!"{name} depends on {ax}"
  unless offending.isEmpty do
    throwError m!"declarations depending on non-standard axioms: {offending}"

/-! ## The statements of the paper's results -/

/-! Each statement of `COF/Paper.lean`, and the threshold theorem that uses the cited two-process
result. -/

/--
info: COF.Paper.definition1.{u_1, u_2} {Inst : Type u_1} {Op : Type u_2} (t : COF.Trace Inst Op) (conflict : Op → Op → Prop)
  (Φ : Inst) :
  t.EventuallyConflictFree conflict Φ ↔
    t.completed Φ ∨
      ∃ N, ∀ (k : ℕ), k ≥ N → ∀ (Φ' : Inst), t.step k = some Φ' → Φ' ≠ Φ → ¬conflict (t.operation Φ) (t.operation Φ')
-/
#guard_msgs in
#check COF.Paper.definition1

/--
info: COF.Paper.definition2.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {P : Type u_1} {R : Type u_2} {V : Type u_3} {S : Type u_4}
  {Q : Type u_5} {O : Type u_6} {Resp : Type u_7} (I : COF.SharedMemory.Implementation P R V S O Resp)
  (obj : COF.Object Q O Resp) :
  I.ConflictObstructionFree obj.Conflict ↔
    ∀ (α : ℕ → COF.SharedMemory.Action P O) (Φ : P × ℕ × O),
      (I.trace α).invoked Φ →
        (I.trace α).correct Φ → (I.trace α).EventuallyConflictFree obj.Conflict Φ → (I.trace α).completed Φ
-/
#guard_msgs in
#check COF.Paper.definition2

/--
info: COF.Paper.lemma1.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {P : Type u_1} {R : Type u_2} {V : Type u_3} {S : Type u_4}
  {Q : Type u_5} {O : Type u_6} {Resp : Type u_7} (I : COF.SharedMemory.Implementation P R V S O Resp)
  (obj : COF.Object Q O Resp) (hfull : ∀ (o o' : O), obj.Conflict o o') :
  I.ConflictObstructionFree obj.Conflict ↔ I.ObstructionFree
-/
#guard_msgs in
#check COF.Paper.lemma1

/--
info: COF.Paper.lemma2.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {P : Type u_1} {R : Type u_2} {V : Type u_3} {S : Type u_4}
  {Q : Type u_5} {O : Type u_6} {Resp : Type u_7} (I : COF.SharedMemory.Implementation P R V S O Resp)
  (obj : COF.Object Q O Resp) (hempty : ∀ (o o' : O), ¬obj.Conflict o o') :
  I.ConflictObstructionFree obj.Conflict ↔ I.WaitFree
-/
#guard_msgs in
#check COF.Paper.lemma2

/--
info: COF.Paper.propose_commute_decided (d v v' : Bool) : COF.consensusObject.CommuteAt v v' (some d)
-/
#guard_msgs in
#check COF.Paper.propose_commute_decided

/--
info: COF.Paper.propose_commute_undecided (v v' : Bool) : COF.consensusObject.CommuteAt v v' none ↔ v = v'
-/
#guard_msgs in
#check COF.Paper.propose_commute_undecided

/--
info: COF.Paper.propose_conflict_iff (v v' : Bool) : COF.consensusObject.Conflict v v' ↔ v ≠ v'
-/
#guard_msgs in
#check COF.Paper.propose_conflict_iff

/--
info: COF.Paper.cof_implementation_cofTermination.{u_1, u_2, u_3, u_4} {P : Type u_1} {R : Type u_2} {V : Type u_3}
  {S : Type u_4} (I : COF.SharedMemory.Implementation P R V S Bool Bool)
  (h : I.ConflictObstructionFree COF.consensusObject.Conflict) : I.singleShot.COFTermination
-/
#guard_msgs in
#check COF.Paper.cof_implementation_cofTermination

/--
info: COF.Paper.valent_descendant.{u_1, u_2, u_3} {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin 3) R V S) {C C' : COF.SharedMemory.Config (Fin 3) R V S} {v : Bool}
  (hv : a.Valent {1, 2} C v) (hπ : a.Reach {1, 2} C C') : a.Valent {1, 2} C' v
-/
#guard_msgs in
#check COF.Paper.valent_descendant

/--
info: COF.Paper.lemma3.{u_1, u_2, u_3} {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin 3) R V S) (hval : a.Validity) : a.Valent {1, 2} (a.initial COF.Paper.inputI) true
-/
#guard_msgs in
#check COF.Paper.lemma3

/--
info: COF.Paper.lemma4.{u_1, u_2, u_3} {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin 3) R V S) (hval : a.Validity) (ht : a.COFTermination) :
  ∃ C, a.Reachable COF.Paper.inputI C ∧ a.Bivalent {1, 2} C
-/
#guard_msgs in
#check COF.Paper.lemma4

/--
info: COF.Paper.lemma5.{u_1, u_2, u_3} {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin 3) R V S) (ht : a.COFTermination) {C : COF.SharedMemory.Config (Fin 3) R V S}
  (hC : a.Reachable COF.Paper.inputI C) (hb : a.Bivalent {1, 2} C) : ∃ p, p ∈ {1, 2} ∧ a.Bivalent {1, 2} (a.step C p)
-/
#guard_msgs in
#check COF.Paper.lemma5

/--
info: COF.Paper.theorem6.{u_1, u_2, u_3} {n : ℕ} (hn : 3 ≤ n) {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin n) R V S) : ¬(a.Validity ∧ a.Agreement ∧ a.COFTermination)
-/
#guard_msgs in
#check COF.Paper.theorem6

/--
info: COF.Paper.theorem6_of_three.{u_1, u_2, u_3, u_4} {P : Type u_1} {R : Type u_2} {V : Type u_3} {S : Type u_4}
  (a : COF.SharedMemory.Algorithm P R V S) (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
  ¬(a.Validity ∧ a.Agreement ∧ a.COFTermination)
-/
#guard_msgs in
#check COF.Paper.theorem6_of_three

/--
info: COF.Paper.theorem6_strict.{u_1, u_2, u_3} {n : ℕ} (hn : 3 ≤ n) {R : Type u_1} {V : Type u_2} {S : Type u_3}
  (a : COF.SharedMemory.Algorithm (Fin n) R V S) : ¬(a.Validity ∧ a.Agreement ∧ a.StrictCOFTermination)
-/
#guard_msgs in
#check COF.Paper.theorem6_strict

/--
info: COF.Paper.corollary7.{u_1, u_2, u_3} {n : ℕ} (hn : 3 ≤ n) : ¬COF.COFUniversal (Fin n)
-/
#guard_msgs in
#check COF.Paper.corollary7

/--
info: COF.Paper.corollary7_of_three.{u_1, u_2, u_3, u_4} {P : Type u_1} (p₀ p₁ p₂ : P) (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂)
  (h₁₂ : p₁ ≠ p₂) : ¬COF.COFUniversal P
-/
#guard_msgs in
#check COF.Paper.corollary7_of_three

/--
info: COF.cofConsensusImplementable_fin_iff (h₂ : COF.TwoProcessCOFConsensus) (n : ℕ) :
  COF.COFConsensusImplementable (Fin n) ↔ n ≤ 2
-/
#guard_msgs in
#check COF.cofConsensusImplementable_fin_iff

/-! ## Axioms of the headline results -/

/-! Redundant with the project-wide check above, and kept as a readable record. -/

/--
info: 'COF.Paper.theorem6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms COF.Paper.theorem6

/--
info: 'COF.Paper.corollary7' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms COF.Paper.corollary7

/-! ## Objects and progress conditions (§2, §3) -/

/-! Definition 1 is pinned above, through `COF.Paper.definition1`. -/

/--
info: def COF.Object.CommuteAt.{u_1, u_2, u_3} : {S : Type u_1} →
  {O : Type u_2} → {R : Type u_3} → COF.Object S O R → O → O → S → Prop :=
fun {S} {O} {R} obj a b s ↦
  (obj.transition b (obj.transition a s).snd).snd = (obj.transition a (obj.transition b s).snd).snd ∧
    (obj.transition a s).fst = (obj.transition a (obj.transition b s).snd).fst ∧
      (obj.transition b (obj.transition a s).snd).fst = (obj.transition b s).fst
-/
#guard_msgs in
#print COF.Object.CommuteAt

/--
info: def COF.Object.Conflict.{u_1, u_2, u_3} : {S : Type u_1} →
  {O : Type u_2} → {R : Type u_3} → COF.Object S O R → O → O → Prop :=
fun {S} {O} {R} obj a b ↦ ∃ s, ¬obj.CommuteAt a b s
-/
#guard_msgs in
#print COF.Object.Conflict

/--
info: def COF.consensusObject : COF.Object (Option Bool) Bool Bool :=
{ initial := none,
  transition := fun v s ↦
    have d := s.getD v;
    (d, some d) }
-/
#guard_msgs in
#print COF.consensusObject

/--
info: structure COF.Trace.{u_1, u_2} (Instance : Type u_1) (Operation : Type u_2) : Type (max u_1 u_2)
number of parameters: 2
fields:
  COF.Trace.operation : Instance → Operation
  COF.Trace.invoked : Instance → Prop
  COF.Trace.correct : Instance → Prop
  COF.Trace.completed : Instance → Prop
  COF.Trace.step : ℕ → Option Instance
constructor:
  COF.Trace.mk.{u_1, u_2} {Instance : Type u_1} {Operation : Type u_2} (operation : Instance → Operation)
    (invoked correct completed : Instance → Prop) (step : ℕ → Option Instance) : COF.Trace Instance Operation
-/
#guard_msgs in
#print COF.Trace

/--
info: def COF.Trace.EventuallySolo.{u_1, u_2} : {I : Type u_1} → {O : Type u_2} → COF.Trace I O → I → Prop :=
fun {I} {O} t i ↦ t.completed i ∨ ∃ N, ∀ (k : ℕ), k ≥ N → ∀ (j : I), t.step k = some j → j = i
-/
#guard_msgs in
#print COF.Trace.EventuallySolo

/--
info: def COF.ConflictObstructionFree.{u_1, u_2} : {I : Type u_1} →
  {O : Type u_2} → (COF.Trace I O → Prop) → (O → O → Prop) → Prop :=
fun {I} {O} valid conflict ↦
  ∀ (t : COF.Trace I O),
    valid t → ∀ (i : I), t.invoked i → t.correct i → t.EventuallyConflictFree conflict i → t.completed i
-/
#guard_msgs in
#print COF.ConflictObstructionFree

/--
info: def COF.ObstructionFree.{u_1, u_2} : {I : Type u_1} → {O : Type u_2} → (COF.Trace I O → Prop) → Prop :=
fun {I} {O} valid ↦
  ∀ (t : COF.Trace I O), valid t → ∀ (i : I), t.invoked i → t.correct i → t.EventuallySolo i → t.completed i
-/
#guard_msgs in
#print COF.ObstructionFree

/--
info: def COF.WaitFree.{u_1, u_2} : {I : Type u_1} → {O : Type u_2} → (COF.Trace I O → Prop) → Prop :=
fun {I} {O} valid ↦ ∀ (t : COF.Trace I O), valid t → ∀ (i : I), t.invoked i → t.correct i → t.completed i
-/
#guard_msgs in
#print COF.WaitFree

/-! ## Consensus algorithms, COF consensus (§4.1) and valency (§4.2) -/

/-! The recursive definitions `run` and `execution` are left out: `#print` shows their compiled
form, which is not informative. -/

/--
info: structure COF.SharedMemory.Algorithm.{u_1, u_2, u_3, u_4} (P : Type u_1) (R : Type u_2) (V : Type u_3) (S : Type u_4) :
  Type (max (max (max u_1 u_2) u_3) u_4)
number of parameters: 4
fields:
  COF.SharedMemory.Algorithm.initialMemory : R → V
  COF.SharedMemory.Algorithm.initialState : P → Bool → S
  COF.SharedMemory.Algorithm.instruction : P → S → COF.SharedMemory.Instruction R V S
constructor:
  COF.SharedMemory.Algorithm.mk.{u_1, u_2, u_3, u_4} {P : Type u_1} {R : Type u_2} {V : Type u_3} {S : Type u_4}
    (initialMemory : R → V) (initialState : P → Bool → S) (instruction : P → S → COF.SharedMemory.Instruction R V S) :
    COF.SharedMemory.Algorithm P R V S
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm

/--
info: def COF.SharedMemory.Algorithm.initial.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → (P → Bool) → COF.SharedMemory.Config P R V S :=
fun {P} {R} {V} {S} a input ↦
  { memory := a.initialMemory, proc := fun p ↦ { state := a.initialState p (input p), decision := none } }
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.initial

/--
info: def COF.SharedMemory.Algorithm.step.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        COF.SharedMemory.Algorithm P R V S → COF.SharedMemory.Config P R V S → P → COF.SharedMemory.Config P R V S :=
fun {P} {R} {V} {S} a c p ↦
  have old := c.proc p;
  have finish := fun memory next ↦
    { memory := memory,
      proc := Function.update c.proc p { state := next.state, decision := old.decision.or next.decision } };
  match a.instruction p old.state with
  | COF.SharedMemory.Instruction.read r next => finish c.memory (next (c.memory r))
  | COF.SharedMemory.Instruction.write r v next => finish (Function.update c.memory r v) next
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.step

/--
info: def COF.SharedMemory.Algorithm.Reach.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        COF.SharedMemory.Algorithm P R V S →
          Set P → COF.SharedMemory.Config P R V S → COF.SharedMemory.Config P R V S → Prop :=
fun {P} {R} {V} {S} a active c d ↦ ∃ ps, (∀ (p : P), p ∈ ps → p ∈ active) ∧ d = a.run c ps
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Reach

/--
info: def COF.SharedMemory.Algorithm.Reachable.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → (P → Bool) → COF.SharedMemory.Config P R V S → Prop :=
fun {P} {R} {V} {S} a input c ↦ a.Reach Set.univ (a.initial input) c
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Reachable

/--
info: def COF.SharedMemory.Config.Decided.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Config P R V S → Bool → Prop :=
fun {P} {R} {V} {S} c v ↦ ∃ p, (c.proc p).decision = some v
-/
#guard_msgs in
#print COF.SharedMemory.Config.Decided

/--
info: def COF.SharedMemory.Algorithm.Validity.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Prop :=
fun {P} {R} {V} {S} a ↦
  ∀ (input : P → Bool) (c : COF.SharedMemory.Config P R V S),
    a.Reachable input c → ∀ (v : Bool), c.Decided v → ∃ p, input p = v
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Validity

/--
info: def COF.SharedMemory.Algorithm.Agreement.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Prop :=
fun {P} {R} {V} {S} a ↦
  ∀ (input : P → Bool) (c : COF.SharedMemory.Config P R V S),
    a.Reachable input c → ∀ (v w : Bool), c.Decided v → c.Decided w → v = w
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Agreement

/--
info: def COF.SharedMemory.Algorithm.COFTermination.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Prop :=
fun {P} {R} {V} {S} a ↦
  ∀ (input : P → Bool) (σ : ℕ → P),
    (∃ N v, ∀ (k : ℕ), k ≥ N → input (σ k) = v) →
      ∀ (p : P),
        (∀ (N : ℕ), ∃ k, k ≥ N ∧ σ k = p) → ∃ n v, ((a.execution (a.initial input) σ n).proc p).decision = some v
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.COFTermination

/--
info: def COF.SharedMemory.Algorithm.TakesOperationStep.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → (P → Bool) → (ℕ → P) → ℕ → P → Prop :=
fun {P} {R} {V} {S} a input σ k p ↦ σ k = p ∧ ((a.execution (a.initial input) σ k).proc p).decision = none
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.TakesOperationStep

/--
info: def COF.SharedMemory.Algorithm.StrictCOFTermination.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Prop :=
fun {P} {R} {V} {S} a ↦
  ∀ (input : P → Bool) (σ : ℕ → P),
    (∃ N v, ∀ (k : ℕ), k ≥ N → ∀ (p : P), a.TakesOperationStep input σ k p → input p = v) →
      ∀ (p : P),
        (∀ (N : ℕ), ∃ k, k ≥ N ∧ σ k = p) → ∃ n v, ((a.execution (a.initial input) σ n).proc p).decision = some v
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.StrictCOFTermination

/--
info: def COF.SharedMemory.Algorithm.COFConsensus.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} → {V : Type u_3} → {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Prop :=
fun {P} {R} {V} {S} a ↦ a.Validity ∧ a.Agreement ∧ a.COFTermination
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.COFConsensus

/--
info: def COF.SharedMemory.Algorithm.CanDecide.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Set P → COF.SharedMemory.Config P R V S → Bool → Prop :=
fun {P} {R} {V} {S} a active c v ↦ ∃ d, a.Reach active c d ∧ d.Decided v
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.CanDecide

/--
info: def COF.SharedMemory.Algorithm.Valent.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Set P → COF.SharedMemory.Config P R V S → Bool → Prop :=
fun {P} {R} {V} {S} a active c v ↦ ¬a.CanDecide active c !v
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Valent

/--
info: def COF.SharedMemory.Algorithm.Univalent.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Set P → COF.SharedMemory.Config P R V S → Prop :=
fun {P} {R} {V} {S} a active c ↦ a.Valent active c false ∨ a.Valent active c true
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Univalent

/--
info: def COF.SharedMemory.Algorithm.Bivalent.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → COF.SharedMemory.Algorithm P R V S → Set P → COF.SharedMemory.Config P R V S → Prop :=
fun {P} {R} {V} {S} a active c ↦ ¬a.Univalent active c
-/
#guard_msgs in
#print COF.SharedMemory.Algorithm.Bivalent

/-! ## Implementations, histories and linearizability -/

/--
info: structure COF.SharedMemory.Implementation.{u_1, u_2, u_3, u_4, u_5, u_6} (P : Type u_1) (R : Type u_2) (V : Type u_3)
  (S : Type u_4) (O : Type u_5) (Resp : Type u_6) : Type (max (max (max (max (max u_1 u_2) u_3) u_4) u_5) u_6)
number of parameters: 6
fields:
  COF.SharedMemory.Implementation.initialMemory : R → V
  COF.SharedMemory.Implementation.initialState : P → S
  COF.SharedMemory.Implementation.invoke : P → O → S → S
  COF.SharedMemory.Implementation.instruction : P → S → COF.SharedMemory.OpInstruction R V S Resp
constructor:
  COF.SharedMemory.Implementation.mk.{u_1, u_2, u_3, u_4, u_5, u_6} {P : Type u_1} {R : Type u_2} {V : Type u_3}
    {S : Type u_4} {O : Type u_5} {Resp : Type u_6} (initialMemory : R → V) (initialState : P → S)
    (invoke : P → O → S → S) (instruction : P → S → COF.SharedMemory.OpInstruction R V S Resp) :
    COF.SharedMemory.Implementation P R V S O Resp
-/
#guard_msgs in
#print COF.SharedMemory.Implementation

/--
info: def COF.SharedMemory.Implementation.stepResult.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp →
              COF.SharedMemory.ImplConfig P R V S O → P → O → (R → V) × COF.SharedMemory.ProcState S O × Option Resp :=
fun {P} {R} {V} {S} {O} {Resp} I c p o ↦
  match I.instruction p (c.proc p).state with
  | COF.SharedMemory.OpInstruction.read r next =>
    (c.memory, (c.proc p).after o (next (c.memory r)).fst (next (c.memory r)).snd, (next (c.memory r)).snd)
  | COF.SharedMemory.OpInstruction.write r v next =>
    (Function.update c.memory r v, (c.proc p).after o next.fst next.snd, next.snd)
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.stepResult

/--
info: def COF.SharedMemory.Implementation.act.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp →
              COF.SharedMemory.ImplConfig P R V S O →
                COF.SharedMemory.Action P O → COF.SharedMemory.ImplConfig P R V S O :=
fun {P} {R} {V} {S} {O} {Resp} I c x ↦
  match x with
  | COF.SharedMemory.Action.invoke p o =>
    match (c.proc p).pending with
    | none =>
      { memory := c.memory,
        proc :=
          Function.update c.proc p
            { state := I.invoke p o (c.proc p).state, pending := some o, done := (c.proc p).done } }
    | some val => c
  | COF.SharedMemory.Action.step p =>
    match (c.proc p).pending with
    | some o => { memory := (I.stepResult c p o).fst, proc := Function.update c.proc p (I.stepResult c p o).snd.fst }
    | none => c
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.act

/--
info: def COF.SharedMemory.Implementation.event.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp →
              COF.SharedMemory.ImplConfig P R V S O → COF.SharedMemory.Action P O → Option (COF.Event P O Resp) :=
fun {P} {R} {V} {S} {O} {Resp} I c x ↦
  match x with
  | COF.SharedMemory.Action.invoke p o =>
    match (c.proc p).pending with
    | none => some (COF.Event.inv p o)
    | some val => none
  | COF.SharedMemory.Action.step p =>
    match (c.proc p).pending with
    | some o => Option.map (COF.Event.res p) (I.stepResult c p o).snd.snd
    | none => none
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.event

/--
info: def COF.SharedMemory.Implementation.history.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp →
              List (COF.SharedMemory.Action P O) → COF.History P O Resp :=
fun {P} {R} {V} {S} {O} {Resp} I acts ↦ I.recordRun 0 I.initial [] acts
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.history

/--
info: def COF.SharedMemory.Implementation.StepsAt.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp → (ℕ → COF.SharedMemory.Action P O) → ℕ → P → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I α k p ↦
  α k = COF.SharedMemory.Action.step p ∧ ((I.execution I.initial α k).proc p).pending.isSome = true
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.StepsAt

/--
info: def COF.SharedMemory.Implementation.trace.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp →
              (ℕ → COF.SharedMemory.Action P O) → COF.Trace (P × ℕ × O) O :=
fun {P} {R} {V} {S} {O} {Resp} I α ↦
  { operation := fun i ↦ i.snd.snd,
    invoked := fun i ↦
      ∃ t,
        α t = COF.SharedMemory.Action.invoke i.fst i.snd.snd ∧
          ((I.execution I.initial α t).proc i.fst).pending = none ∧
            ((I.execution I.initial α t).proc i.fst).done = i.snd.fst,
    correct := fun i ↦
      (∀ (N : ℕ), ∃ k, k ≥ N ∧ I.StepsAt α k i.fst) ∨
        ∃ N, ∀ (k : ℕ), k ≥ N → ((I.execution I.initial α k).proc i.fst).pending = none,
    completed := fun i ↦ ∃ t, i.snd.fst < ((I.execution I.initial α t).proc i.fst).done,
    step := fun k ↦
      match α k with
      | COF.SharedMemory.Action.step p =>
        Option.map (fun o ↦ (p, ((I.execution I.initial α k).proc p).done, o))
          ((I.execution I.initial α k).proc p).pending
      | COF.SharedMemory.Action.invoke p o => none }
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.trace

/--
info: def COF.SharedMemory.Implementation.ValidTrace.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} → COF.SharedMemory.Implementation P R V S O Resp → COF.Trace (P × ℕ × O) O → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I t ↦ ∃ α, t = I.trace α
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.ValidTrace

/--
info: def COF.SharedMemory.Implementation.ConflictObstructionFree.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} → {Resp : Type u_6} → COF.SharedMemory.Implementation P R V S O Resp → (O → O → Prop) → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I conflict ↦ COF.ConflictObstructionFree I.ValidTrace conflict
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.ConflictObstructionFree

/--
info: def COF.SharedMemory.Implementation.ObstructionFree.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → {O : Type u_5} → {Resp : Type u_6} → COF.SharedMemory.Implementation P R V S O Resp → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I ↦ COF.ObstructionFree I.ValidTrace
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.ObstructionFree

/--
info: def COF.SharedMemory.Implementation.WaitFree.{u_1, u_2, u_3, u_4, u_5, u_6} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} → {O : Type u_5} → {Resp : Type u_6} → COF.SharedMemory.Implementation P R V S O Resp → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I ↦ COF.WaitFree I.ValidTrace
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.WaitFree

/--
info: def COF.SharedMemory.Implementation.Linearizable.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : {P : Type u_1} →
  {R : Type u_2} →
    {V : Type u_3} →
      {S : Type u_4} →
        {O : Type u_5} →
          {Resp : Type u_6} →
            COF.SharedMemory.Implementation P R V S O Resp → {Q : Type u_7} → COF.Object Q O Resp → Prop :=
fun {P} {R} {V} {S} {O} {Resp} I {Q} obj ↦
  ∀ (acts : List (COF.SharedMemory.Action P O)), COF.Linearizable obj (I.history acts)
-/
#guard_msgs in
#print COF.SharedMemory.Implementation.Linearizable

/--
info: def COF.History.record.{u_1, u_2, u_3} : {P : Type u_1} →
  {O : Type u_2} → {Resp : Type u_3} → COF.History P O Resp → ℕ → Option (COF.Event P O Resp) → COF.History P O Resp :=
fun {P} {O} {Resp} H t x ↦
  match x with
  | none => H
  | some (COF.Event.inv p o) => H ++ [{ proc := p, op := o, invokedAt := t, returned := none }]
  | some (COF.Event.res p r) =>
    List.map
      (fun a ↦
        if a.proc = p ∧ a.returned.isNone = true then
          { proc := a.proc, op := a.op, invokedAt := a.invokedAt, returned := some (r, t) }
        else a)
      H
-/
#guard_msgs in
#print COF.History.record

/--
info: structure COF.IsLinearization.{u_1, u_2, u_3, u_4} {P : Type u_1} {Q : Type u_2} {O : Type u_3} {Resp : Type u_4}
  (obj : COF.Object Q O Resp) (H : COF.History P O Resp) (S : List (COF.OpRecord P O Resp × Resp)) : Prop
number of parameters: 7
fields:
  COF.IsLinearization.nodup : (List.map Prod.fst S).Nodup
  COF.IsLinearization.subset : ∀ (x : COF.OpRecord P O Resp × Resp), x ∈ S → x.fst ∈ H
  COF.IsLinearization.complete : ∀ (a : COF.OpRecord P O Resp),
      a ∈ H → ∀ (r : Resp) (t : ℕ), a.returned = some (r, t) → (a, r) ∈ S
  COF.IsLinearization.legal : obj.Legal obj.initial (List.map (fun x ↦ (x.fst.op, x.snd)) S)
  COF.IsLinearization.realTime : ∀ (x y : COF.OpRecord P O Resp × Resp),
      [x, y].Sublist S → ∀ (r : Resp) (t : ℕ), y.fst.returned = some (r, t) → x.fst.invokedAt ≤ t
constructor:
  COF.IsLinearization.mk.{u_1, u_2, u_3, u_4} {P : Type u_1} {Q : Type u_2} {O : Type u_3} {Resp : Type u_4}
    {obj : COF.Object Q O Resp} {H : COF.History P O Resp} {S : List (COF.OpRecord P O Resp × Resp)}
    (nodup : (List.map Prod.fst S).Nodup) (subset : ∀ (x : COF.OpRecord P O Resp × Resp), x ∈ S → x.fst ∈ H)
    (complete : ∀ (a : COF.OpRecord P O Resp), a ∈ H → ∀ (r : Resp) (t : ℕ), a.returned = some (r, t) → (a, r) ∈ S)
    (legal : obj.Legal obj.initial (List.map (fun x ↦ (x.fst.op, x.snd)) S))
    (realTime :
      ∀ (x y : COF.OpRecord P O Resp × Resp),
        [x, y].Sublist S → ∀ (r : Resp) (t : ℕ), y.fst.returned = some (r, t) → x.fst.invokedAt ≤ t) :
    COF.IsLinearization obj H S
-/
#guard_msgs in
#print COF.IsLinearization

/--
info: def COF.Linearizable.{u_1, u_2, u_3, u_4} : {P : Type u_1} →
  {Q : Type u_2} → {O : Type u_3} → {Resp : Type u_4} → COF.Object Q O Resp → COF.History P O Resp → Prop :=
fun {P} {Q} {O} {Resp} obj H ↦ ∃ S, COF.IsLinearization obj H S
-/
#guard_msgs in
#print COF.Linearizable

/-! ## Universal constructions and the cited two-process result -/

/--
info: def COF.COFUniversal.{u_1, u_2, u_3, u_4} : Type u_1 → Prop :=
fun P ↦
  ∀ (Q O Resp : Type) (obj : COF.Object Q O Resp),
    ∃ R V S I, I.Linearizable obj ∧ I.ConflictObstructionFree obj.Conflict
-/
#guard_msgs in
#print COF.COFUniversal

/--
info: def COF.COFConsensusImplementable.{u_1} : Type u_1 → Prop :=
fun P ↦ ∃ R V S a, a.COFConsensus
-/
#guard_msgs in
#print COF.COFConsensusImplementable

/--
info: def COF.TwoProcessCOFConsensus : Prop :=
COF.COFConsensusImplementable (Fin 2)
-/
#guard_msgs in
#print COF.TwoProcessCOFConsensus
