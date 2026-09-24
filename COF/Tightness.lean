import COF.TraceBridge

/-! The three-process bound is tight, relative to one cited result.

The paper remarks (§4.1) that COF consensus *is* implementable in the read–write model for two
processes, but does not prove it. It cites the obstruction-free consensus algorithm of Attiya,
Guerraoui, Hendler and Kuznetsov (*The complexity of obstruction-free implementations*, JACM
56(4), 2009), which terminates in solo runs and whenever all processes propose the same value;
with two processes, that is exactly what COF termination demands. Constructing and verifying
that algorithm is outside the scope of the paper, and of this development.

The result is stated as `TwoProcessCOFConsensus` and assumed as an explicit hypothesis, never as
an axiom. Only a theorem that takes it as an argument depends on it, so the dependency shows in
that theorem's statement, and `#print axioms` is unaffected. The impossibility theorems do not
use it.

From it, `cofConsensusImplementable_fin_iff` derives the exact threshold: COF consensus for `n`
processes is implementable if and only if `n ≤ 2`. The cases `n ≤ 1` are proved outright, by the
trivial algorithm `decideOwnInput`, and `n ≥ 3` is `no_cof_consensus_fin`, so the hypothesis is
used for `n = 2` alone. `twoProcessCOFConsensus_iff_threshold` confirms that it is exactly the
part of the threshold statement not proved here. -/

namespace COF.SharedMemory.Algorithm

/-- The trivial algorithm: at its first step, every process decides its own input without
communicating. It is valid and wait-free for any number of processes, but satisfies agreement
only when there is at most one process. -/
def decideOwnInput (P : Type*) : Algorithm P Unit Unit Bool where
  initialMemory _ := ()
  initialState _ b := b
  instruction _ s := .write () () ⟨s, some s⟩

variable {P : Type*} [DecidableEq P]

/-- A step of `p` keeps `p`'s local state, and decides it unless `p` has already decided. -/
@[simp] theorem decideOwnInput_step_self (c : Config P Unit Unit Bool) (p : P) :
    ((decideOwnInput P).step c p).proc p =
      ⟨(c.proc p).state, (c.proc p).decision.or (some (c.proc p).state)⟩ := by
  simp [step, decideOwnInput]

/-- The invariant: every process holds its own input as local state, and any decision it has
taken is that input. -/
theorem decideOwnInput_reachable {input : P → Bool} {c : Config P Unit Unit Bool}
    (hr : (decideOwnInput P).Reachable input c) (p : P) :
    (c.proc p).state = input p ∧ ∀ v, (c.proc p).decision = some v → v = input p := by
  obtain ⟨ps, -, rfl⟩ := hr
  refine (decideOwnInput P).run_induction (allowed := fun _ => True)
    (Motive := fun c => ∀ p, (c.proc p).state = input p ∧
      ∀ v, (c.proc p).decision = some v → v = input p)
    (fun c t _ _ hc p => ?_) ps _ (Reach.refl _ _ _) (fun p => ?_) (fun _ _ => trivial) p
  · by_cases hpt : p = t
    · subst hpt
      obtain ⟨hs, hd⟩ := hc p
      refine ⟨by simpa using hs, fun v hv => ?_⟩
      cases h : (c.proc p).decision <;> simp_all
    · rw [step_local_other _ _ hpt]
      exact hc p
  · simp [initial, decideOwnInput]

/-- Every scheduled process decides at its first step, whatever the schedule. -/
theorem decideOwnInput_cofTermination : (decideOwnInput P).COFTermination := by
  intro input c _ schedule _ p hinf
  obtain ⟨k, -, hk⟩ := hinf 0
  refine ⟨k + 1, ?_⟩
  change ∃ v, (((decideOwnInput P).step _ (schedule k)).proc p).decision = some v
  rw [hk, decideOwnInput_step_self]
  cases ((decideOwnInput P).execution c schedule k |>.proc p).decision <;> simp

/-- With at most one process there is nobody to disagree with, and a process only ever decides
its own input. -/
theorem decideOwnInput_safe [Subsingleton P] : (decideOwnInput P).Safe := by
  intro input c hr
  have hdec : ∀ v, c.Decided v → ∃ p, v = input p := fun v ⟨p, hp⟩ =>
    ⟨p, (decideOwnInput_reachable hr p).2 v hp⟩
  refine ⟨fun v w hv hw => ?_, fun v hv => ?_⟩
  · obtain ⟨p, rfl⟩ := hdec v hv
    obtain ⟨q, rfl⟩ := hdec w hw
    rw [Subsingleton.elim p q]
  · obtain ⟨p, rfl⟩ := hdec v hv
    exact ⟨p, rfl⟩

/-- Hence `decideOwnInput` solves COF consensus for any system of at most one process. -/
theorem decideOwnInput_consensus [Subsingleton P] : (decideOwnInput P).Consensus :=
  ⟨decideOwnInput_safe, decideOwnInput_cofTermination⟩

end COF.SharedMemory.Algorithm

namespace COF
open SharedMemory

/-- COF consensus is implementable for the process type `P`: some deterministic read/write
algorithm satisfies agreement, validity and COF termination. Register, value and local-state
types are existentially quantified, as in `BinaryUniversal`. -/
def COFConsensusImplementable (P : Type*) [DecidableEq P] : Prop :=
  ∃ (R V S : Type) (_ : DecidableEq R) (a : Algorithm P R V S), a.Consensus

/-- **The paper's cited two-process result. This is a hypothesis, not a theorem.**

COF consensus is implementable in the read–write model for two processes (paper, §4.1, citing
the obstruction-free consensus algorithm of Attiya, Guerraoui, Hendler and Kuznetsov, JACM
2009). Neither the paper nor this development proves it. It is never used as an axiom: a
theorem that relies on it takes it as an explicit argument.

The liveness clause is `COFTermination`, whose homogeneity premise also constrains the steps of
processes that have already decided. That makes it weaker than the paper's clause, so this
assumes no more than the paper claims: `cofConsensusImplementable_of_trace` derives it from the
claim as stated with the paper's own trace-level COF condition. -/
def TwoProcessCOFConsensus : Prop := COFConsensusImplementable (Fin 2)

/-- Implementability in the paper's own terms implies implementability in the sense used here.
The paper's terms are agreement and validity, together with the §3 trace-level COF condition
for the consensus object over the paper's executions, those from an initial configuration.
For two processes, this shows that the cited result, as the paper states it, implies
`TwoProcessCOFConsensus`. -/
theorem cofConsensusImplementable_of_trace {P : Type*} [DecidableEq P]
    (h : ∃ (R V S : Type) (_ : DecidableEq R) (a : Algorithm P R V S),
      a.Safe ∧ ConflictObstructionFree a.InitialTrace consensusObject.Conflict) :
    COFConsensusImplementable P := by
  obtain ⟨R, V, S, _, a, hs, ht⟩ := h
  exact ⟨R, V, S, _, a, hs, a.cofTermination_of_initial_trace_cof ht⟩

/-- With at most one process, the trivial algorithm `decideOwnInput` solves COF consensus. -/
theorem cofConsensusImplementable_of_subsingleton (P : Type*) [DecidableEq P] [Subsingleton P] :
    COFConsensusImplementable P :=
  ⟨Unit, Unit, Bool, inferInstance, Algorithm.decideOwnInput P,
    Algorithm.decideOwnInput_consensus⟩

/-- **The three-process bound is tight**, given the cited two-process result: COF consensus for
`n` processes is implementable exactly when `n ≤ 2`.

The hypothesis is used for `n = 2` only. For `n ≥ 3` this is `no_cof_consensus_fin`, and for
`n ≤ 1` the trivial algorithm `decideOwnInput` is a witness. -/
theorem cofConsensusImplementable_fin_iff (h₂ : TwoProcessCOFConsensus) (n : ℕ) :
    COFConsensusImplementable (Fin n) ↔ n ≤ 2 := by
  constructor
  · rintro ⟨R, V, S, _, a, ha⟩
    by_contra hn
    exact a.no_cof_consensus_fin (by omega) ha
  · intro hn
    rcases (show n ≤ 1 ∨ n = 2 by omega) with hn | rfl
    · have := Fin.subsingleton_iff_le_one.mpr hn
      exact cofConsensusImplementable_of_subsingleton (Fin n)
    · exact h₂

/-- The hypothesis is exactly what the threshold statement needs: the two are equivalent. So
`cofConsensusImplementable_fin_iff` assumes nothing beyond the two-process case of its own
conclusion. -/
theorem twoProcessCOFConsensus_iff_threshold :
    TwoProcessCOFConsensus ↔ ∀ n, (COFConsensusImplementable (Fin n) ↔ n ≤ 2) :=
  ⟨cofConsensusImplementable_fin_iff, fun h => (h 2).mpr le_rfl⟩

end COF
