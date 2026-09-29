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
* With inputs `(0,1)` and the steps `0, 1, 0, 0, 1, 1, 0, 0, …`, each process always reads back
  the other's value, and nobody ever decides (`alg_not_wfTermination`).

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

theorem step_self (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) {p : Fin 2}
    (hd : (d.proc p).decision = none) :
    (alg.step d p).proc p =
      if (d.proc p).state.2 then
        ⟨((d.proc p).state.1, false),
          if d.memory () = some (d.proc p).state.1 then some (d.proc p).state.1 else none⟩
      else ⟨((d.proc p).state.1, true), none⟩ := by
  unfold Algorithm.step
  dsimp only [alg]
  rw [hd]
  by_cases h : (d.proc p).state.2 <;> simp [h]
  split <;> simp_all

theorem step_memory (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) {p : Fin 2}
    (hd : (d.proc p).decision = none) :
    (alg.step d p).memory () =
      if (d.proc p).state.2 then d.memory () else some (d.proc p).state.1 := by
  unfold Algorithm.step
  dsimp only [alg]
  rw [hd]
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
      cases hd : ((alg.execution (alg.initial input) σ n).proc (σ n)).decision with
      | some v => rw [alg.step_of_decided hd]; exact input_kept input σ n _
      | none =>
        rw [step_self _ hd]
        split <;> exact input_kept input σ n _
    · rw [alg.step_local_other _ hq]
      exact input_kept input σ n q

/-- Once a process with input `v` writes after `N`, the register holds `v` for as long as only
processes with input `v` take steps. -/
theorem register_stays (input : Fin 2 → Bool) {σ : ℕ → Fin 2} {N : ℕ} {v : Bool}
    (hadm : alg.Admissible (alg.initial input) σ)
    (hN : ∀ k ≥ N, input (σ k) = v) {w : ℕ} (hw : N ≤ w)
    (hmw : (alg.execution (alg.initial input) σ (w + 1)).memory () = some v) :
    ∀ t, w + 1 ≤ t → (alg.execution (alg.initial input) σ t).memory () = some v := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hmw
  | succ t ht ih =>
    rw [execution_succ, step_memory _ (hadm t)]
    split
    · exact ih
    · rw [input_kept input σ t (σ t), hN t (by omega)]

/-- The next time at or after `t` that `p` takes a step; `p`'s state is still what it was at
`t`. -/
theorem next_step (input : Fin 2 → Bool) (σ : ℕ → Fin 2) {p : Fin 2}
    (hinf : ∀ N, ∃ k ≥ N, σ k = p) (t : ℕ) :
    ∃ k, t ≤ k ∧ σ k = p ∧
      (alg.execution (alg.initial input) σ k).proc p =
        (alg.execution (alg.initial input) σ t).proc p := by
  have h : ∃ k, t ≤ k ∧ σ k = p := hinf t
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    alg.execution_proc_of_no_steps_between _ σ (Nat.find_spec h).1
      fun m h₁ h₂ h₃ => Nat.find_min h h₂ ⟨h₁, h₃⟩⟩

theorem alg_cofTermination : alg.COFTermination := by
  intro input σ hadm ⟨N, v, hN⟩ p hinf
  have hin := input_kept input σ
  have hd : ∀ k, σ k = p → ((alg.execution (alg.initial input) σ k).proc p).decision = none :=
    fun k hk => hk ▸ hadm k
  have hpv : input p = v := by
    obtain ⟨k, hk, hkp⟩ := hinf N
    rw [← hkp]
    exact hN k hk
  -- Some step of `p` at a time `w ≥ N` is a write.
  obtain ⟨w, hwN, hwp, hwphase⟩ : ∃ w, N ≤ w ∧ σ w = p ∧
      ((alg.execution (alg.initial input) σ w).proc p).state.2 = false := by
    obtain ⟨k₁, hk₁, hk₁p, -⟩ := next_step input σ hinf N
    by_cases hph : ((alg.execution (alg.initial input) σ k₁).proc p).state.2
    · -- `p` reads at `k₁`, so its next step writes.
      obtain ⟨k₂, hk₂, hk₂p, hst⟩ := next_step input σ hinf (k₁ + 1)
      refine ⟨k₂, by omega, hk₂p, ?_⟩
      rw [hst, execution_succ, hk₁p, step_self _ (hd k₁ hk₁p)]
      simp [hph]
    · exact ⟨k₁, hk₁, hk₁p, by simpa using hph⟩
  -- From then on, the register holds `v`.
  have hmw : (alg.execution (alg.initial input) σ (w + 1)).memory () = some v := by
    rw [execution_succ, hwp, step_memory _ (hd w hwp), hwphase, hin w p, hpv]
    rfl
  have hmem := register_stays input hadm hN hwN hmw
  -- The next step of `p` reads `v` back, and `p` decides.
  obtain ⟨r, hr, hrp, hst⟩ := next_step input σ hinf (w + 1)
  have hphase : ((alg.execution (alg.initial input) σ r).proc p).state.2 = true := by
    rw [hst, execution_succ, hwp, step_self _ (hd w hwp)]
    simp [hwphase]
  refine hadm.finite_of_decided (n := r + 1) (v := v) ?_ hinf
  rw [execution_succ, hrp, step_self _ (hd r hrp), hphase, hmem r hr, hin r p, hpv]
  simp

/-! ## WF termination fails -/

/-- Process `0` proposes `0` and process `1` proposes `1`. -/
def inputs : Fin 2 → Bool := fun p => decide (p = 1)

/-- The steps `0, 1`, then `0, 0, 1, 1` over and over. -/
def interleaving : ℕ → Fin 2 := fun t => if t = 0 ∨ t % 4 = 2 ∨ t % 4 = 3 then 0 else 1

/-- The configuration after `t ≥ 1` steps of `interleaving`, by phase `t % 4`. Nobody has decided,
both processes keep their inputs, and the next step is: `1` writes `1` (phase `1`); `0` reads `1`
(phase `2`); `0` writes `0` (phase `3`); `1` reads `0` (phase `0`). -/
def Phase (d : Config (Fin 2) Unit (Option Bool) (Bool × Bool)) (ph : ℕ) : Prop :=
  (d.proc 0).decision = none ∧ (d.proc 1).decision = none ∧
  (d.proc 0).state.1 = false ∧ (d.proc 1).state.1 = true ∧
  match ph with
  | 0 => (d.proc 0).state.2 = true ∧ (d.proc 1).state.2 = true ∧ d.memory () = some false
  | 1 => (d.proc 0).state.2 = true ∧ (d.proc 1).state.2 = false ∧ d.memory () = some false
  | 2 => (d.proc 0).state.2 = true ∧ (d.proc 1).state.2 = true ∧ d.memory () = some true
  | _ => (d.proc 0).state.2 = false ∧ (d.proc 1).state.2 = true ∧ d.memory () = some true

theorem interleaving_phase :
    ∀ t, Phase (alg.execution (alg.initial inputs) interleaving (t + 1)) ((t + 1) % 4) := by
  intro t
  induction t with
  | zero =>
    -- process `0` writes `0`
    simp [Phase, execution, interleaving, Algorithm.step, Algorithm.initial, alg, inputs,
      Function.update]
  | succ t ih =>
    obtain ⟨hd0, hd1, hs0, hs1, hph⟩ := ih
    rw [execution_succ]
    have h4 : (t + 1) % 4 = 0 ∨ (t + 1) % 4 = 1 ∨ (t + 1) % 4 = 2 ∨ (t + 1) % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [h] at hph
    · -- phase 0: process `1` reads `0`, and does not decide
      obtain ⟨hp0, hp1, hm⟩ := hph
      rw [show interleaving (t + 1) = 1 by simp [interleaving]; omega,
        show (t + 1 + 1) % 4 = 1 by omega]
      simp [Phase, step_self _ hd1, step_memory _ hd1, hp0, hp1, hm, hd0, hs0, hs1]
    · -- phase 1: process `1` writes `1`
      obtain ⟨hp0, hp1, -⟩ := hph
      rw [show interleaving (t + 1) = 1 by simp [interleaving]; omega,
        show (t + 1 + 1) % 4 = 2 by omega]
      simp [Phase, step_self _ hd1, step_memory _ hd1, hp0, hp1, hd0, hs0, hs1]
    · -- phase 2: process `0` reads `1`, and does not decide
      obtain ⟨hp0, hp1, hm⟩ := hph
      rw [show interleaving (t + 1) = 0 by simp [interleaving]; omega,
        show (t + 1 + 1) % 4 = 3 by omega]
      simp [Phase, step_self _ hd0, step_memory _ hd0, hp0, hp1, hm, hd1, hs0, hs1]
    · -- phase 3: process `0` writes `0`
      obtain ⟨hp0, hp1, -⟩ := hph
      rw [show interleaving (t + 1) = 0 by simp [interleaving]; omega,
        show (t + 1 + 1) % 4 = 0 by omega]
      simp [Phase, step_self _ hd0, step_memory _ hd0, hp0, hp1, hd1, hs0, hs1]

/-- Nobody ever decides, so every entry of `interleaving` is a step. -/
theorem interleaving_admissible : alg.Admissible (alg.initial inputs) interleaving := by
  intro t
  cases t with
  | zero => rfl
  | succ t =>
    obtain ⟨hd0, hd1, -⟩ := interleaving_phase t
    by_cases h : interleaving (t + 1) = 0
    · rw [h]; exact hd0
    · rw [show interleaving (t + 1) = 1 by omega]; exact hd1

/-- Process `0` takes infinitely many steps, and never decides. -/
theorem alg_not_wfTermination : ¬ alg.WFTermination := by
  intro h
  exact h inputs interleaving interleaving_admissible 0
    (fun N => ⟨4 * N + 2, by omega, by simp [interleaving]⟩)

/-- **COF termination is strictly weaker than WF termination.** -/
theorem cofTermination_strictly_weaker :
    ∃ a : Algorithm (Fin 2) Unit (Option Bool) (Bool × Bool),
      a.COFTermination ∧ ¬ a.WFTermination :=
  ⟨alg, alg_cofTermination, alg_not_wfTermination⟩

end COF.Checks.Separation
