import COF.Universal.Transfer
import COF.Consensus.Impossibility

/-!
# Corollary 7: no COF universal construction for three or more processes

> A COF universal construction is an algorithm that takes as input a sequential object
> specification and produces a linearizable shared-memory implementation satisfying COF
> termination — in particular it implements COF consensus.
>
> **Corollary 7.** No universal construction algorithm is conflict-obstruction-free in the
> read-write shared memory model of three or more processes.

`COFUniversal P` asks, for every sequential object, for *some* implementation with processes `P`
that is linearizable and conflict-obstruction-free for the object's conflict relation. A universal
construction in the paper's sense, one algorithm that takes the specification as input, yields
such an implementation for every object. So `COFUniversal` asks for less, and its impossibility is
the stronger statement.

The proof is the paper's: the implementation of the consensus object, run by the single-shot
client, is a COF consensus algorithm, and Theorem 6 rules that out.
-/

namespace COF
open SharedMemory

namespace SharedMemory.Implementation
variable {P R V S : Type*}

/-- No implementation of binary consensus is both linearizable and conflict-obstruction-free when
there are three distinct processes: its single-shot client would be a COF consensus algorithm. -/
theorem no_linearizable_cof_consensus (I : Implementation P R V S Bool Bool) (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
    ¬ (I.Linearizable consensusObject ∧ I.ConflictObstructionFree consensusObject.Conflict) := by
  rintro ⟨hlin, hcof⟩
  have hdec := linearizes_singleShot hlin
  exact I.singleShot.no_cof_consensus p₀ p₁ p₂ h₀₁ h₀₂ h₁₂
    ⟨I.singleShot.validity_of_linearizes hdec, I.singleShot.agreement_of_linearizes hdec,
      I.singleShot.cofTermination_of_cofTerminationFor (cofTerminationFor_singleShot hcof)⟩

end SharedMemory.Implementation

/-- A **COF universal construction** for the processes `P`: every sequential object has a
linearizable and conflict-obstruction-free implementation from read/write registers. Its register,
value and local-state types may depend on the object, and may live in any universe. -/
def COFUniversal (P : Type*) : Prop :=
  ∀ (Q O Resp : Type) (obj : Object Q O Resp),
    ∃ (R V S : Type*) (I : Implementation P R V S O Resp),
      I.Linearizable obj ∧ I.ConflictObstructionFree obj.Conflict

/-- **Corollary 7**: there is no COF universal construction as soon as there are three distinct
processes. -/
theorem no_cofUniversal {P : Type*} (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) : ¬ COFUniversal P := by
  intro h
  obtain ⟨R, V, S, I, hlin, hcof⟩ := h (Option Bool) Bool Bool consensusObject
  exact I.no_linearizable_cof_consensus p₀ p₁ p₂ h₀₁ h₀₂ h₁₂ ⟨hlin, hcof⟩

/-- **Corollary 7** for `n ≥ 3` processes `0, …, n - 1`. -/
theorem no_cofUniversal_fin {n : ℕ} (hn : 3 ≤ n) : ¬ COFUniversal (Fin n) :=
  no_cofUniversal ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))

end COF
