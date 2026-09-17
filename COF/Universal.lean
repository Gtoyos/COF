import COF.Impossibility
import COF.Objects

/-! Reduction from universal constructions. Only the necessary single-shot,
binary-operation/binary-response fragment of universality is needed. A full
linearizable universal construction must in particular satisfy this fragment.
All invocations are present initially, so their intervals overlap: a linearization
is a sequential ordering including every completed invocation, and optionally
pending invocations. -/
namespace COF

namespace Object
variable {Q P : Type*}

/-- The responses produced by applying the invocations of `ps`, in that order, starting
from state `s`. Each process invokes the operation given by its own input. -/
def responses (obj : Object Q Bool Bool) (input : P → Bool) : Q → List P → List (P × Bool)
  | _, [] => []
  | s, p :: ps =>
    let result := obj.transition (input p) s
    (p, result.1) :: obj.responses input result.2 ps

/-- Once consensus holds a value, every later proposal is answered with it. -/
theorem consensus_responses_decided (input : P → Bool) (b : Bool) (ps : List P) :
    consensusObject.responses input (some b) ps = ps.map (fun p => (p, b)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [responses, consensusObject] using congrArg (List.cons (p, b)) ih

/-- In any sequential ordering of proposals, every response is the input of whichever
process was ordered first. This is what makes a linearization enforce agreement. -/
theorem consensus_responses_initial (input : P → Bool) (p : P) (ps : List P) :
    consensusObject.responses input none (p :: ps) =
      (p :: ps).map (fun q => (q, input p)) := by
  change (p, input p) :: consensusObject.responses input (some (input p)) ps = _
  rw [consensus_responses_decided]
  rfl

end Object

namespace SharedMemory.Algorithm
variable {P R V S Q : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- Necessary safety condition of a single-shot linearizable implementation. The
ordering is shared by *all* decisions in a configuration, not chosen per decision. -/
def Linearizes (obj : Object Q Bool Bool) : Prop :=
  ∀ input c, a.Reachable input c →
    ∃ ps : List P, ps.Nodup ∧ ∀ p v, (c.proc p).decision = some v →
      (p, v) ∈ obj.responses input obj.initial ps

/-- Per-process conflict-free termination. This is only a necessary fragment of
full object COF: quantification here is restricted to single-shot executions. -/
def ObjectCOF (obj : Object Q Bool Bool) : Prop :=
  ∀ input c, a.Reachable input c → ∀ schedule : ℕ → P, ∀ p,
    (∀ N, ∃ k ≥ N, schedule k = p) →
    (∃ N, ∀ k ≥ N, schedule k ≠ p → ¬ obj.Conflict (input p) (input (schedule k))) →
    ∃ n v, ((a.execution c schedule n).proc p).decision = some v

/-- Linearizing the consensus object implies consensus safety. Every decision in a
configuration must appear in the one sequential ordering that explains it; by
`consensus_responses_initial` all responses in that ordering are the first-ordered
process's input, which gives both agreement and validity at once. -/
theorem safe_of_consensus_linearizes (h : a.Linearizes consensusObject) : a.Safe := by
  intro input c hr
  obtain ⟨ps, _, hps⟩ := h input c hr
  cases ps with
  | nil =>
    have hn : ∀ b, ¬ c.Decided b := by
      rintro b ⟨p, hp⟩
      simpa [Object.responses] using hps p b hp
    exact ⟨fun v _ hv _ => (hn v hv).elim, fun v hv => (hn v hv).elim⟩
  | cons q qs =>
    have hall : ∀ b, c.Decided b → b = input q := by
      rintro b ⟨p, hp⟩
      have hm := hps p b hp
      rw [show consensusObject.initial = none from rfl, Object.consensus_responses_initial] at hm
      obtain ⟨r, _, he⟩ := List.mem_map.mp hm
      exact (congrArg Prod.snd he).symm
    exact ⟨fun v w hv hw => (hall v hv).trans (hall w hw).symm,
      fun v hv => ⟨q, (hall v hv).symm⟩⟩

/-- Object-level COF for consensus yields the consensus liveness clause. An eventually
homogeneous schedule is precisely one that is eventually conflict-free for every process
still stepping, since consensus proposals conflict exactly when they differ. -/
theorem termination_of_consensus_objectCOF (h : a.ObjectCOF consensusObject) :
    a.COFTermination := by
  intro input c hr schedule hhom p hinf
  obtain ⟨N, b, hN⟩ := hhom
  obtain ⟨k, hk, he⟩ := hinf N
  have hp : input p = b := by simpa [he] using hN k hk
  apply h input c hr schedule p hinf
  refine ⟨N, ?_⟩
  intro j hj _
  rw [consensus_conflict_iff, hp, hN j hj]
  exact not_not.mpr rfl

end SharedMemory.Algorithm

/-- A deliberately weak necessary fragment of universality. Register, value, and
local-state types may depend on the object. Proving even this fragment impossible
rules out full linearizable COF universal constructions. -/
def BinaryUniversal (P : Type) [DecidableEq P] : Prop :=
  ∀ (Q : Type) (obj : Object Q Bool Bool),
    ∃ (R V S : Type) (_ : DecidableEq R) (a : SharedMemory.Algorithm P R V S),
      a.Linearizes obj ∧ a.ObjectCOF obj

/-- Paper Corollary `cor:no_cof_univ`, for the necessary fragment above: instantiate the
construction at the consensus object and it becomes a COF consensus algorithm, which
cannot exist. -/
theorem no_binaryUniversal {P : Type} [DecidableEq P] (p₀ p₁ p₂ : P)
    (h₀₁ : p₀ ≠ p₁) (h₂₀ : p₂ ≠ p₀) (h₂₁ : p₂ ≠ p₁) : ¬ BinaryUniversal P := by
  intro h
  obtain ⟨R, V, S, inst, a, hs, ht⟩ := h (Option Bool) consensusObject
  -- Register the existentially bound decidability instance for the algorithm's registers.
  let _ : DecidableEq R := inst
  exact a.no_cof_consensus p₀ p₁ p₂ h₀₁ h₂₀ h₂₁
    ⟨a.safe_of_consensus_linearizes hs, a.termination_of_consensus_objectCOF ht⟩

end COF
