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
  simp [step, decideOwnInput]

/-- In every reachable configuration, every process holds its own input, and any decision it has
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

theorem decideOwnInput_validity : (decideOwnInput P).Validity := fun _ _ hr _ ⟨p, hp⟩ =>
  ⟨p, ((decideOwnInput_reachable hr p).2 _ hp).symm⟩

theorem decideOwnInput_agreement [Subsingleton P] : (decideOwnInput P).Agreement := by
  intro input c hr v w ⟨p, hp⟩ ⟨q, hq⟩
  rw [(decideOwnInput_reachable hr p).2 v hp, (decideOwnInput_reachable hr q).2 w hq,
    Subsingleton.elim p q]

/-- Every scheduled process decides at its first step. -/
theorem decideOwnInput_cofTermination : (decideOwnInput P).COFTermination := by
  intro input σ _ p hinf
  obtain ⟨k, -, hk⟩ := hinf 0
  refine ⟨k + 1, ?_⟩
  change ∃ v, (((decideOwnInput P).step _ (σ k)).proc p).decision = some v
  rw [hk, decideOwnInput_step_self]
  cases ((decideOwnInput P).execution _ σ k |>.proc p).decision <;> simp

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
for two processes (paper §4.1).

It is stated with `COFTermination`. Under the strict reading of COF termination the claim is
stronger, and it implies this one (`cofConsensusImplementable_of_strict`), so the hypothesis asks
for no more than the paper claims. -/
def TwoProcessCOFConsensus : Prop := COFConsensusImplementable (Fin 2)

/-- The claim with the strict reading of COF termination implies `COFConsensusImplementable`. -/
theorem cofConsensusImplementable_of_strict {P : Type*}
    (h : ∃ (R V S : Type) (a : Algorithm P R V S),
      a.Validity ∧ a.Agreement ∧ a.StrictCOFTermination) :
    COFConsensusImplementable P := by
  obtain ⟨R, V, S, a, hval, hag, ht⟩ := h
  exact ⟨R, V, S, a, hval, hag, ht.cofTermination⟩

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
