import COF.Universal.Client
import COF.Consensus.Specification
import Mathlib.Data.Nat.Find

/-!
# From an implementation to its single-shot client

Linearizability and COF of an implementation `I` of a binary object transfer to its single-shot
client `I.singleShot`, as two single-shot properties:

* `Linearizes obj`: the decisions of every reachable configuration are the responses of one
  sequential execution of `obj` (`linearizes_singleShot`);
* `COFTerminationFor obj`: COF termination, with conflicts between proposals judged by `obj`'s
  conflict relation (`cofTerminationFor_singleShot`).

For the consensus object these are exactly what COF consensus asks for: `Linearizes` gives
Validity and Agreement, and `COFTerminationFor` gives COF termination. This is the paper's remark
(§4.1) "a COF consensus implementation satisfies COF termination", together with the fact that a
linearizable implementation of consensus is safe.
-/

namespace COF

/-- The responses of `obj` when the processes `ps` apply, in order from state `s`, the operation
named by their inputs. -/
def Object.responses {Q P : Type*} (obj : Object Q Bool Bool) (input : P → Bool) :
    Q → List P → List (P × Bool)
  | _, [] => []
  | s, p :: ps =>
    let result := obj.transition (input p) s
    (p, result.1) :: obj.responses input result.2 ps

/-- A legal sequential history of the processes' proposals is the one `responses` computes. -/
theorem Object.responses_of_legal {Q P : Type*} (obj : Object Q Bool Bool) (input : P → Bool) :
    ∀ (L : List (P × Bool)) (q : Q), obj.Legal q (L.map fun y => (input y.1, y.2)) →
      obj.responses input q (L.map Prod.fst) = L
  | [], _, _ => rfl
  | (i, r) :: L, q, h => by
    obtain ⟨hr, hL⟩ := h
    simp only [List.map_cons, Object.responses]
    rw [Object.responses_of_legal obj input L _ hL, hr]

/-- Once consensus holds a value, every later proposal is answered with it. -/
theorem consensus_responses_decided {P : Type*} (input : P → Bool) (b : Bool) (ps : List P) :
    consensusObject.responses input (some b) ps = ps.map (fun p => (p, b)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simpa [Object.responses, consensusObject] using congrArg (List.cons (p, b)) ih

/-- In a sequential execution of consensus, every response is the proposal of the first
process. -/
theorem consensus_responses_initial {P : Type*} (input : P → Bool) (p : P) (ps : List P) :
    consensusObject.responses input none (p :: ps) = (p :: ps).map (fun q => (q, input p)) := by
  change (p, input p) :: consensusObject.responses input (some (input p)) ps = _
  rw [consensus_responses_decided]
  rfl

namespace SharedMemory.Algorithm
variable {P R V S Q : Type*} (a : Algorithm P R V S)

/-! ## The single-shot properties -/

/-- The decisions of `a` are linearizable for `obj`: in every reachable configuration, some
sequence of distinct processes, applying the operations their inputs name, produces every decision
taken so far as its response. -/
def Linearizes (obj : Object Q Bool Bool) : Prop :=
  ∀ input c, a.Reachable input c →
    ∃ ps : List P, ps.Nodup ∧ ∀ p v, (c.proc p).decision = some v →
      (p, v) ∈ obj.responses input obj.initial ps

/-- COF termination with conflicts judged by `obj`: if from some point on every process other
than `p` that takes a step proposed an operation that does not conflict with `p`'s, then `p`
decides in finitely many steps or crashes, that is, `p` does not take infinitely many steps. -/
def COFTerminationFor (obj : Object Q Bool Bool) : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P), a.Admissible (a.initial input) σ → ∀ p,
    (∃ N, ∀ k ≥ N, σ k ≠ p → ¬ obj.Conflict (input p) (input (σ k))) →
    ¬ ∀ N, ∃ k ≥ N, σ k = p

/-! ## For the consensus object -/

/-- If the decisions linearize for consensus, all decisions of a reachable configuration are the
input of one process: the first one in the linearization. -/
theorem decisions_of_linearizes (h : a.Linearizes consensusObject) {input : P → Bool}
    {c : Config P R V S} (hr : a.Reachable input c) {v : Bool} (hv : c.Decided v) :
    ∃ q, ∀ w, c.Decided w → w = input q := by
  obtain ⟨ps, _, hps⟩ := h input c hr
  obtain ⟨p, hp⟩ := hv
  cases ps with
  | nil => simpa [Object.responses] using hps p v hp
  | cons q qs =>
    refine ⟨q, fun w ⟨r, hr⟩ => ?_⟩
    have hm := hps r w hr
    rw [show consensusObject.initial = none from rfl, consensus_responses_initial] at hm
    obtain ⟨_, _, he⟩ := List.mem_map.mp hm
    exact (congrArg Prod.snd he).symm

theorem validity_of_linearizes (h : a.Linearizes consensusObject) : a.Validity :=
  fun _ _ hr v hv => by
    obtain ⟨q, hq⟩ := a.decisions_of_linearizes h hr hv
    exact ⟨q, (hq v hv).symm⟩

theorem agreement_of_linearizes (h : a.Linearizes consensusObject) : a.Agreement :=
  fun _ _ hr v w hv hw => by
    obtain ⟨q, hq⟩ := a.decisions_of_linearizes h hr hv
    exact (hq v hv).trans (hq w hw).symm

/-- For consensus, `COFTerminationFor` implies COF termination: proposals conflict exactly when
they differ, so if eventually only processes that proposed the same value take steps, none of
them meets a conflicting proposal. -/
theorem cofTermination_of_cofTerminationFor (h : a.COFTerminationFor consensusObject) :
    a.COFTermination := by
  intro input σ hadm ⟨N, b, hN⟩ p hinf
  obtain ⟨k, hk, he⟩ := hinf N
  have hp : input p = b := by simpa [he] using hN k hk
  refine h input σ hadm p ⟨N, fun j hj _ => ?_⟩ hinf
  rw [consensus_conflict_iff, hp, hN j hj]
  exact not_not.mpr rfl

end SharedMemory.Algorithm

namespace SharedMemory.Implementation
open Function

variable {P R V S Q : Type*} {I : Implementation P R V S Bool Bool}

/-! ## Linearizability transfers -/

/-- **Linearizability transfers to the client.** A linearization of the history of `I` that a
client run produces orders the proposals of some processes, including every process that has
decided, and its responses are the decisions. -/
theorem linearizes_singleShot {obj : Object Q Bool Bool} (h : I.Linearizable obj) :
    I.singleShot.Linearizes obj := by
  intro input c hr
  obtain ⟨ps, -, rfl⟩ := hr
  have hinit : ClientInv input (I.singleShot.initial input) := clientInv_initial input
  have hc := clientInv_run (I := I) ps hinit
  have hH := historyInv_run (I := I) ps (I.singleShot.initial input) [] 0
    hinit ⟨List.nodup_nil, by simp, fun p hp => by
      simp [Invoked, Algorithm.initial, singleShot] at hp⟩
  rw [embed_initial] at hH
  obtain ⟨hHnd, hrec, hex⟩ := hH
  obtain ⟨S, hnd, hsub, hcomp, hlegal, -⟩ := h (actions I (I.singleShot.initial input) ps)
  refine ⟨S.map fun x => x.1.proc, ?_, ?_⟩
  · -- Distinct linearized instances belong to distinct processes.
    have := hnd.map_on (f := OpRecord.proc) fun a ha b hb hab => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      exact List.inj_on_of_nodup_map hHnd (hsub x hx) (hsub y hy) hab
    simpa [List.map_map, comp_def] using this
  · intro p v hv
    -- The linearized proposals produce the linearization's responses.
    have hresp : obj.responses input obj.initial (S.map fun x => x.1.proc) =
        S.map fun x => (x.1.proc, x.2) := by
      have hlegal' : obj.Legal obj.initial
          ((S.map fun x => (x.1.proc, x.2)).map fun y => (input y.1, y.2)) := by
        convert hlegal using 1
        simp only [List.map_map]
        apply List.map_congr_left
        intro x hx
        simp [(hrec x.1 (hsub x hx)).1]
      simpa [List.map_map, comp_def] using
        Object.responses_of_legal obj input _ obj.initial hlegal'
    rw [hresp]
    -- A decided process has returned, so its instance is linearized, with its decision.
    have hinv : Invoked ((I.singleShot.run (I.singleShot.initial input) ps).proc p).state := by
      rcases (hc p).2 with ⟨-, -, hd⟩ | ⟨-, -, hd⟩ | ⟨-, h1, -⟩
      · rw [hd] at hv; cases hv
      · rw [hd] at hv; cases hv
      · simp [Invoked, h1]
    obtain ⟨a, ha, rfl⟩ := hex p hinv
    obtain ⟨-, har, -⟩ := hrec a ha
    rw [hv] at har
    obtain ⟨⟨v', t⟩, hret, rfl⟩ := Option.map_eq_some_iff.mp har
    exact List.mem_map.mpr ⟨(a, v'), hcomp a ha v' t hret, rfl⟩

/-! ## COF transfers -/

/-- In the trace of `I`, a client step belongs to the pending proposal of the process taking it,
if any. -/
theorem trace_step_infActions (input : P → Bool) (σ : ℕ → P) (k : ℕ) :
    (I.trace (I.infActions (I.singleShot.initial input) σ)).step k =
      ((I.singleShot.execution (I.singleShot.initial input) σ k).proc (σ k)).state.1.pending.map
        fun o => (σ k, ((I.singleShot.execution (I.singleShot.initial input) σ k).proc
          (σ k)).state.1.done, o) := by
  simp only [trace]
  rw [execution_infActions]
  cases hp : ((I.singleShot.execution (I.singleShot.initial input) σ k).proc
      (σ k)).state.1.pending with
  | some o => simp [infActions, actionOf, hp]
  | none =>
    by_cases h0 : ((I.singleShot.execution (I.singleShot.initial input) σ k).proc
        (σ k)).state.1.done = 0 <;>
      simp [infActions, actionOf, hp, h0]

/-- The first time `σ` names a client process, it invokes its proposal: its first operation
instance, `(p, 0, input p)`. -/
theorem trace_invoked_infActions (input : P → Bool) (σ : ℕ → P) {p : P} {t : ℕ}
    (ht : σ t = p) (hfirst : ∀ m < t, σ m ≠ p) :
    (I.trace (I.infActions (I.singleShot.initial input) σ)).invoked (p, 0, input p) := by
  have hfresh := I.singleShot.execution_proc_of_no_steps (I.singleShot.initial input) σ hfirst
  refine ⟨t, ?_, ?_, ?_⟩
  · simp only [infActions]
    rw [ht, hfresh]
    simp [actionOf, Algorithm.initial, singleShot]
  · rw [execution_infActions, embed_proc, hfresh]
    rfl
  · rw [execution_infActions, embed_proc, hfresh]
    rfl

/-- Once it has invoked its proposal, a client process stays invoked. -/
theorem invoked_after (input : P → Bool) (σ : ℕ → P) {p : P} {t : ℕ}
    (ht : σ t = p) (hfirst : ∀ m < t, σ m ≠ p) :
    ∀ m, t < m →
      Invoked ((I.singleShot.execution (I.singleShot.initial input) σ m).proc p).state := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hfresh :=
      I.singleShot.execution_proc_of_no_steps (I.singleShot.initial input) σ hfirst
    rw [Algorithm.execution_succ, ht, step_of_fresh _ p
      (by rw [hfresh]; simp [Algorithm.initial, singleShot])
      (by rw [hfresh]; simp [Algorithm.initial])]
    simp [Invoked]
  | succ m _ ih =>
    exact invoked_step (I.clientInv_initial_execution input σ m) ih (σ m)

/-- A client process that `σ` names infinitely often, and that never decides, keeps taking steps of
its proposal in `I`, so it is correct in the trace. -/
theorem trace_correct_infActions (input : P → Bool) (σ : ℕ → P) {p : P} {t : ℕ}
    (ht : σ t = p) (hfirst : ∀ m < t, σ m ≠ p) (hinf : ∀ N, ∃ k ≥ N, σ k = p)
    (hnd : ∀ m,
      ((I.singleShot.execution (I.singleShot.initial input) σ m).proc p).decision = none) :
    (I.trace (I.infActions (I.singleShot.initial input) σ)).correct (p, 0, input p) := by
  left
  intro N
  obtain ⟨k, hk, hkp⟩ := hinf (N + t + 1)
  have hpend := pending_of_invoked (I.clientInv_initial_execution input σ k)
    (invoked_after input σ ht hfirst k (by omega)) (hnd k)
  refine ⟨k, by omega, ?_, ?_⟩
  · simp [infActions, hkp, actionOf, hpend]
  · rw [execution_infActions, embed_proc, hpend]
    rfl

/-- If eventually only processes whose proposals do not conflict with `p`'s take steps, then `p`'s
proposal is eventually conflict-free in the trace. -/
theorem trace_conflictFree_infActions (input : P → Bool) (σ : ℕ → P)
    {obj : Object Q Bool Bool} {p : P} {N : ℕ}
    (hN : ∀ k ≥ N, σ k ≠ p → ¬ obj.Conflict (input p) (input (σ k))) :
    ∀ k ≥ N, ∀ j, (I.trace (I.infActions (I.singleShot.initial input) σ)).step k = some j →
      j ≠ (p, 0, input p) → ¬ obj.Conflict (input p) j.2.2 := by
  intro k hk j hstep hne
  rw [trace_step_infActions] at hstep
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hstep
  rcases (I.clientInv_initial_execution input σ k (σ k)).2 with
    ⟨hp, -, -⟩ | ⟨hp, h0, -⟩ | ⟨hp, -, -⟩
  · simp [hp] at ho
  · rw [hp] at ho
    obtain rfl := Option.some.inj ho
    refine hN k hk fun hq => hne ?_
    rw [h0, hq]
  · simp [hp] at ho

/-- **COF transfers to the client.** A client process that takes infinitely many steps never
decides. It invokes its proposal at its first step, and is correct. If eventually no process with a
conflicting proposal steps, the proposal is eventually conflict-free, so COF of `I` makes it
return: the process decides after all. -/
theorem cofTerminationFor_singleShot {obj : Object Q Bool Bool}
    (h : I.ConflictObstructionFree obj.Conflict) : I.singleShot.COFTerminationFor obj := by
  classical
  intro input σ hadm p ⟨N, hN⟩ hinf
  have hnd : ∀ m,
      ((I.singleShot.execution (I.singleShot.initial input) σ m).proc p).decision = none := by
    intro m
    cases hd : ((I.singleShot.execution (I.singleShot.initial input) σ m).proc p).decision with
    | none => rfl
    | some v => exact absurd hinf (hadm.finite_of_decided hd)
  have hsched : ∃ t, σ t = p := by
    obtain ⟨k, -, hk⟩ := hinf 0
    exact ⟨k, hk⟩
  have hfirst : ∀ m < Nat.find hsched, σ m ≠ p := fun m hm => Nat.find_min hsched hm
  obtain ⟨t, ht⟩ := h (I.trace (I.infActions (I.singleShot.initial input) σ)) ⟨_, rfl⟩
    (p, 0, input p)
    (trace_invoked_infActions input σ (Nat.find_spec hsched) hfirst)
    (trace_correct_infActions input σ (Nat.find_spec hsched) hfirst hinf hnd)
    (Or.inr ⟨N, trace_conflictFree_infActions input σ hN⟩)
  -- The proposal returned, so the process has decided.
  change 0 < ((I.execution I.initial _ t).proc p).done at ht
  rw [execution_infActions, embed_proc] at ht
  rcases (I.clientInv_initial_execution input σ t p).2 with
    ⟨-, h0, -⟩ | ⟨-, h0, -⟩ | ⟨-, -, hd⟩
  · omega
  · omega
  · simp [hnd t] at hd

end SharedMemory.Implementation
end COF
