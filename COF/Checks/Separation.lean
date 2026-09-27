import COF.Consensus.Specification
import Mathlib.Data.Nat.Find

/-!
# COF termination is strictly weaker than WF termination

The paper calls COF termination a "weaker liveness condition" than wait-free termination, and
`WFTermination.cofTermination` proves that wait-free termination implies it. This file shows that
the converse fails: an algorithm satisfies COF termination but not WF termination
(`cofTermination_strictly_weaker`). So Theorem 6 does not merely restate the impossibility of
wait-free consensus from read/write registers.

The algorithm has two processes and one register `X`, initially empty. A process with input `b`
alternately writes `X := b` and reads `X`, and decides `b` when it reads back `b`.

* If eventually only processes with input `v` take steps, `X` eventually holds `v` for good, and
  every such process decides the next time it reads (`alg_cofTermination`).
* Under strict alternation with inputs `(0,1)`, process `0` always reads `1` back, and never
  decides (`alg_not_wfTermination`).

The algorithm violates Agreement; it is only meant to compare the two liveness conditions.
-/

namespace COF.Checks.Separation
open SharedMemory SharedMemory.Algorithm

/-- The local state is the process's input, and whether its next step is a read. -/
def alg : Algorithm (Fin 2) Unit (Option Bool) (Bool × Bool) where
  initialMemory _ := none
  initialState _ b := (b, false)
  instruction _ s :=
    if s.2 then
      .read () fun x => if x = some s.1 then ⟨(s.1, false), some s.1⟩ else ⟨(s.1, false), none⟩
    else .write () (some s.1) ⟨(s.1, true), none⟩

theorem step_self (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) (p : Fin 2) :
    (alg.step d p).proc p =
      if (d.proc p).state.2 then
        ⟨((d.proc p).state.1, false), (d.proc p).decision.or
          (if d.memory () = some (d.proc p).state.1 then some (d.proc p).state.1 else none)⟩
      else ⟨((d.proc p).state.1, true), (d.proc p).decision⟩ := by
  unfold Algorithm.step
  dsimp only [alg]
  by_cases h : (d.proc p).state.2 <;> simp [h]
  split <;> simp_all

theorem step_memory (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) (p : Fin 2) :
    (alg.step d p).memory () =
      if (d.proc p).state.2 then d.memory () else some (d.proc p).state.1 := by
  unfold Algorithm.step
  dsimp only [alg]
  by_cases h : (d.proc p).state.2 <;> simp [h, Function.update]

/-! ## COF termination holds -/

/-- Every process keeps its input as the first component of its state. -/
theorem input_kept (input : Fin 2 → Bool) (σ : ℕ → Fin 2) :
    ∀ n q, ((alg.execution (alg.initial input) σ n).proc q).state.1 = input q
  | 0, _ => rfl
  | n + 1, q => by
    rw [execution_succ]
    by_cases hq : q = σ n
    · subst hq
      rw [step_self]
      split <;> exact input_kept input σ n _
    · rw [alg.step_local_other _ hq]
      exact input_kept input σ n q

/-- Once a process with input `v` writes after `N`, the register holds `v` for as long as only
processes with input `v` take steps. -/
theorem register_stays (input : Fin 2 → Bool) {σ : ℕ → Fin 2} {N : ℕ} {v : Bool}
    (hN : ∀ k ≥ N, input (σ k) = v) {w : ℕ} (hw : N ≤ w)
    (hmw : (alg.execution (alg.initial input) σ (w + 1)).memory () = some v) :
    ∀ t, w + 1 ≤ t → (alg.execution (alg.initial input) σ t).memory () = some v := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hmw
  | succ t ht ih =>
    rw [execution_succ, step_memory]
    split
    · exact ih
    · rw [input_kept input σ t (σ t), hN t (by omega)]

/-- The next time at or after `t` that `p` is scheduled; `p`'s state is still what it was at
`t`. -/
theorem next_scheduled (input : Fin 2 → Bool) (σ : ℕ → Fin 2) {p : Fin 2}
    (hinf : ∀ N, ∃ k ≥ N, σ k = p) (t : ℕ) :
    ∃ k, t ≤ k ∧ σ k = p ∧
      (alg.execution (alg.initial input) σ k).proc p =
        (alg.execution (alg.initial input) σ t).proc p := by
  have h : ∃ k, t ≤ k ∧ σ k = p := hinf t
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    alg.execution_proc_of_unscheduled_between _ σ (Nat.find_spec h).1
      fun m h₁ h₂ h₃ => Nat.find_min h h₂ ⟨h₁, h₃⟩⟩

theorem alg_cofTermination : alg.COFTermination := by
  intro input σ ⟨N, v, hN⟩ p hinf
  have hin := input_kept input σ
  have hpv : input p = v := by
    obtain ⟨k, hk, hkp⟩ := hinf N
    rw [← hkp]
    exact hN k hk
  -- Some step of `p` at a time `w ≥ N` is a write.
  obtain ⟨w, hwN, hwp, hwphase⟩ : ∃ w, N ≤ w ∧ σ w = p ∧
      ((alg.execution (alg.initial input) σ w).proc p).state.2 = false := by
    obtain ⟨k₁, hk₁, hk₁p, -⟩ := next_scheduled input σ hinf N
    by_cases hph : ((alg.execution (alg.initial input) σ k₁).proc p).state.2
    · -- `p` reads at `k₁`, so its next step writes.
      obtain ⟨k₂, hk₂, hk₂p, hst⟩ := next_scheduled input σ hinf (k₁ + 1)
      refine ⟨k₂, by omega, hk₂p, ?_⟩
      rw [hst, execution_succ, hk₁p, step_self]
      simp [hph]
    · exact ⟨k₁, hk₁, hk₁p, by simpa using hph⟩
  -- From then on, the register holds `v`.
  have hmw : (alg.execution (alg.initial input) σ (w + 1)).memory () = some v := by
    rw [execution_succ, hwp, step_memory, hwphase, hin w p, hpv]
    rfl
  have hmem := register_stays input hN hwN hmw
  -- The next step of `p` reads `v` back, and `p` decides.
  obtain ⟨r, hr, hrp, hst⟩ := next_scheduled input σ hinf (w + 1)
  have hphase : ((alg.execution (alg.initial input) σ r).proc p).state.2 = true := by
    rw [hst, execution_succ, hwp, step_self]
    simp [hwphase]
  refine ⟨r + 1, ?_⟩
  rw [execution_succ, hrp, step_self, hphase, hmem r hr, hin r p, hpv]
  cases ((alg.execution (alg.initial input) σ r).proc p).decision <;> simp

/-! ## WF termination fails -/

/-- Process `0` proposes `0` and process `1` proposes `1`. -/
def inputs : Fin 2 → Bool := fun p => decide (p = 1)

/-- Strict alternation: `0, 1, 0, 1, …`. -/
def alternation : ℕ → Fin 2 := fun t => if t % 2 = 0 then 0 else 1

/-- The configuration at time `t` of the alternating execution, by phase `t % 4`: `0` writes `0`,
`1` writes `1`, `0` reads `1` (and does not decide), `1` reads `1`. Process `0` never decides. -/
def Phase (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) (ph : ℕ) : Prop :=
  (d.proc 0).decision = none ∧ (d.proc 1).state.1 = true ∧ (d.proc 0).state.1 = false ∧
  match ph with
  | 0 => (d.proc 0).state.2 = false ∧ (d.proc 1).state.2 = false
  | 1 => (d.proc 0).state.2 = true ∧ (d.proc 1).state.2 = false
  | 2 => (d.proc 0).state.2 = true ∧ (d.proc 1).state.2 = true ∧ d.memory () = some true
  | _ => (d.proc 0).state.2 = false ∧ (d.proc 1).state.2 = true ∧ d.memory () = some true

theorem alternation_phase :
    ∀ t, Phase (alg.execution (alg.initial inputs) alternation t) (t % 4) := by
  intro t
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    obtain ⟨hd0, hs1, hs0, hph⟩ := ih
    rw [execution_succ]
    have h4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] at hph
    · -- phase 0: process `0` writes `0`
      obtain ⟨hp0, hp1⟩ := hph
      rw [show alternation t = 0 by simp [alternation]; omega, show (t + 1) % 4 = 1 by omega]
      simp [Phase, step_self, hp0, hp1, hd0, hs0, hs1]
    · -- phase 1: process `1` writes `1`
      obtain ⟨hp0, hp1⟩ := hph
      rw [show alternation t = 1 by simp [alternation]; omega, show (t + 1) % 4 = 2 by omega]
      simp [Phase, step_self, step_memory, hp0, hp1, hd0, hs0, hs1]
    · -- phase 2: process `0` reads `1`, and does not decide
      obtain ⟨hp0, hp1, hm⟩ := hph
      rw [show alternation t = 0 by simp [alternation]; omega, show (t + 1) % 4 = 3 by omega]
      simp [Phase, step_self, step_memory, hp0, hp1, hm, hd0, hs0, hs1]
    · -- phase 3: process `1` reads `1` (and decides); process `0` is untouched
      obtain ⟨hp0, hp1, -⟩ := hph
      rw [show alternation t = 1 by simp [alternation]; omega, show (t + 1) % 4 = 0 by omega]
      simp [Phase, step_self, hp0, hp1, hd0, hs0, hs1]

theorem alg_not_wfTermination : ¬ alg.WFTermination := by
  intro h
  obtain ⟨n, v, hv⟩ := h inputs alternation 0 (fun N => ⟨2 * N, by omega, by simp [alternation]⟩)
  rw [(alternation_phase n).1] at hv
  cases hv

/-- **COF termination is strictly weaker than WF termination.** -/
theorem cofTermination_strictly_weaker :
    ∃ a : Algorithm (Fin 2) Unit (Option Bool) (Bool × Bool),
      a.COFTermination ∧ ¬ a.WFTermination :=
  ⟨alg, alg_cofTermination, alg_not_wfTermination⟩

end COF.Checks.Separation
