import COF.Consensus.Impossibility

/-!
# Three processes is the threshold, given the cited two-process result

> Conflict-obstruction-free consensus is implementable in the read–write model for two processes.
> The consensus algorithm in [Attiya, Guerraoui, Hendler and Kuznetsov, JACM 2009] satisfies COF
> termination in this case […]. As we show below, this is no longer the case for more than two
> processes. (paper §4.1)

The paper cites the two-process result rather than proving it, and so does this file: it is the
hypothesis `TwoProcessCOFConsensus`, taken as an explicit argument by the one theorem that uses
it, never as an axiom. From it, `cofConsensusImplementable_fin_iff` shows that COF consensus for
`n` processes is implementable exactly when `n ≤ 2`. The case `n ≥ 3` is Theorem 6, the case
`n ≤ 1` is the trivial algorithm `decideOwnInput`, and the hypothesis is used for `n = 2` only.
Nothing else in the development depends on it.
-/

namespace COF.SharedMemory.Algorithm

/-- The trivial algorithm: at its first step, every process decides its own input. It satisfies
Validity and COF termination for any number of processes, and Agreement for at most one. -/
def decideOwnInput (P : Type*) : Algorithm P Unit Unit Bool where
  initialMemory _ := ()
  initialState _ b := b
  instruction _ s := .write () () ⟨s, some s⟩

variable {P : Type*}

@[simp] theorem decideOwnInput_step_self (c : Config P Unit Unit Bool) (p : P) :
    ((decideOwnInput P).step c p).proc p =
      ⟨(c.proc p).state, (c.proc p).decision.or (some (c.proc p).state)⟩ := by
  cases h : (c.proc p).decision with
  | none => simp [step, decideOwnInput, h]
  | some v => rw [step_of_decided _ h]; exact Local.ext rfl (by simp [h])

/-- In every reachable configuration, every process holds its own input, and any decision it has
taken is that input. -/
theorem decideOwnInput_reachable {input : P → Bool} {c : Config P Unit Unit Bool}
    (hr : (decideOwnInput P).Reachable input c) (p : P) :
    (c.proc p).state = input p ∧ ∀ v, (c.proc p).decision = some v → v = input p := by
  obtain ⟨ps, -, rfl⟩ := hr
  refine (decideOwnInput P).run_induction (allowed := fun _ => True)
    (Motive := fun c => ∀ p, (c.proc p).state = input p ∧
      ∀ v, (c.proc p).decision = some v → v = input p)
    ?step ps _ (Reach.refl _ _ _) ?initial (fun _ _ => trivial) p
  case initial => simp [initial, decideOwnInput]
  case step =>
    intro c t _ _ hc p
    by_cases hpt : p = t
    · subst hpt
      obtain ⟨hs, hd⟩ := hc p
      refine ⟨by simpa using hs, fun v hv => ?_⟩
      cases h : (c.proc p).decision <;> simp_all
    · rw [step_local_other _ _ hpt]
      exact hc p

theorem decideOwnInput_validity : (decideOwnInput P).Validity := fun _ _ hr _ ⟨p, hp⟩ =>
  ⟨p, ((decideOwnInput_reachable hr p).2 _ hp).symm⟩

theorem decideOwnInput_agreement [Subsingleton P] : (decideOwnInput P).Agreement := by
  intro input c hr v w ⟨p, hp⟩ ⟨q, hq⟩
  rw [(decideOwnInput_reachable hr p).2 v hp, (decideOwnInput_reachable hr q).2 w hq,
    Subsingleton.elim p q]

/-- Every process decides at its first step, so it takes only one step. -/
theorem decideOwnInput_cofTermination : (decideOwnInput P).COFTermination := by
  intro input σ hadm _ p hinf
  obtain ⟨k, -, hk⟩ := hinf 0
  set c := (decideOwnInput P).execution ((decideOwnInput P).initial input) σ k
  have hd : (c.proc p).decision = none := hk ▸ hadm k
  refine hadm.finite_of_decided (n := k + 1) (v := (c.proc p).state) ?_ hinf
  rw [execution_succ, hk, decideOwnInput_step_self, hd]
  rfl

/-- With at most one process, `decideOwnInput` is a COF consensus algorithm. -/
theorem decideOwnInput_cofConsensus [Subsingleton P] : (decideOwnInput P).COFConsensus :=
  ⟨decideOwnInput_validity, decideOwnInput_agreement, decideOwnInput_cofTermination⟩

end COF.SharedMemory.Algorithm

namespace COF
open SharedMemory

/-- COF consensus is implementable for the processes `P`: some read/write algorithm satisfies
Validity, Agreement and COF termination. -/
def COFConsensusImplementable (P : Type*) : Prop :=
  ∃ (R V S : Type) (a : Algorithm P R V S), a.COFConsensus

/-- **The cited two-process result, assumed rather than proved**: COF consensus is implementable
for two processes (paper §4.1). -/
def TwoProcessCOFConsensus : Prop := COFConsensusImplementable (Fin 2)

/-- With at most one process, COF consensus is implementable. -/
theorem cofConsensusImplementable_of_subsingleton (P : Type*) [Subsingleton P] :
    COFConsensusImplementable P :=
  ⟨Unit, Unit, Bool, Algorithm.decideOwnInput P, Algorithm.decideOwnInput_cofConsensus⟩

/-- **Three processes is the threshold**, given the cited two-process result: COF consensus for
`n` processes is implementable exactly when `n ≤ 2`. -/
theorem cofConsensusImplementable_fin_iff (h₂ : TwoProcessCOFConsensus) (n : ℕ) :
    COFConsensusImplementable (Fin n) ↔ n ≤ 2 := by
  constructor
  · rintro ⟨R, V, S, a, ha⟩
    by_contra hn
    exact a.no_cof_consensus_fin (by omega) ha
  · intro hn
    rcases (show n ≤ 1 ∨ n = 2 by omega) with hn | rfl
    · have := Fin.subsingleton_iff_le_one.mpr hn
      exact cofConsensusImplementable_of_subsingleton (Fin n)
    · exact h₂

/-- The hypothesis is exactly the part of the threshold statement not proved here. -/
theorem twoProcessCOFConsensus_iff_threshold :
    TwoProcessCOFConsensus ↔ ∀ n, (COFConsensusImplementable (Fin n) ↔ n ≤ 2) :=
  ⟨cofConsensusImplementable_fin_iff, fun h => (h 2).mpr le_rfl⟩

end COF
