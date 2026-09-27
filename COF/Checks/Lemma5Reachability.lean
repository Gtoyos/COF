import COF.Consensus.BivalentSuccessor

/-!
# Lemma 5 needs its reachability hypothesis

Lemma 5 is stated for bivalent configurations `C` with `I ⇝ C`, and so is `bivalent_successor`.
The hypothesis cannot be dropped: here is an algorithm that satisfies COF termination, with an
unreachable bivalent configuration `c₀` neither of whose `{p₁,p₂}`-successors is bivalent. COF
termination only constrains executions, and the proof of Lemma 5 needs processes that run solo to
decide.

Processes `0, 1, 2`; registers `r := false` and `s := true`, both initially `0`. Initial states
`norm b` decide their own input at the first step, so COF termination holds in every execution.
The configuration `c₀` uses states that no execution reaches:

* `p₁` in state `A` reads `s`: on `0` it goes to `A0`, which writes `r := 1` and then spins; on `1`
  it goes to `A1`, which decides `1`.
* `p₂` in state `B` reads `r`: on `0` it goes to `B0`, which writes `s := 1` and then spins; on `1`
  it goes to `B1`, which decides `0`.

From `c₀ = (A, B)`, the schedule `p₁, p₁, p₂, p₂` decides `0` and `p₂, p₂, p₁, p₁` decides `1`. But
once `p₁` has read, `1` can no longer be decided, and once `p₂` has read, `0` cannot.
-/

namespace COF.Checks.Lemma5Reachability
open SharedMemory SharedMemory.Algorithm

inductive St | norm (b : Bool) | A | A0 | A0' | A1 | B | B0 | B0' | B1

def instr : St → Instruction Bool Bool St
  | .norm b => .write false false ⟨.norm b, some b⟩
  | .A => .read true fun v => if v then ⟨.A1, none⟩ else ⟨.A0, none⟩
  | .A0 => .write false true ⟨.A0', none⟩
  | .A0' => .read false fun _ => ⟨.A0', none⟩
  | .A1 => .read false fun _ => ⟨.A1, some true⟩
  | .B => .read false fun v => if v then ⟨.B1, none⟩ else ⟨.B0, none⟩
  | .B0 => .write true true ⟨.B0', none⟩
  | .B0' => .read false fun _ => ⟨.B0', none⟩
  | .B1 => .read false fun _ => ⟨.B1, some false⟩

def alg : Algorithm (Fin 3) Bool Bool St where
  initialMemory _ := false
  initialState _ b := .norm b
  instruction _ s := instr s

/-- The scheduled process's new local state. -/
theorem step_self (d : Config (Fin 3) Bool Bool St) (p : Fin 3) :
    (alg.step d p).proc p =
      match instr (d.proc p).state with
      | .read r next =>
        ⟨(next (d.memory r)).state, (d.proc p).decision.or (next (d.memory r)).decision⟩
      | .write _ _ next => ⟨next.state, (d.proc p).decision.or next.decision⟩ := by
  unfold Algorithm.step
  dsimp only [alg]
  split <;> simp_all

/-! ## COF termination holds: every process of an execution is in a `norm` state -/

def NormInv (d : Config (Fin 3) Bool Bool St) : Prop := ∀ p, ∃ b, (d.proc p).state = .norm b

theorem normInv_step {d : Config (Fin 3) Bool Bool St} (hd : NormInv d) (p : Fin 3) :
    NormInv (alg.step d p) := by
  intro q
  by_cases hq : q = p
  · subst hq
    obtain ⟨b, hb⟩ := hd q
    exact ⟨b, by rw [step_self, hb]; rfl⟩
  · rw [alg.step_local_other d hq]; exact hd q

theorem normInv_execution {d : Config (Fin 3) Bool Bool St} (hd : NormInv d) (σ : ℕ → Fin 3) :
    ∀ k, NormInv (alg.execution d σ k)
  | 0 => hd
  | k + 1 => normInv_step (normInv_execution hd σ k) (σ k)

theorem alg_cofTermination : alg.COFTermination := by
  intro input σ _ p hinf
  obtain ⟨k, -, hk⟩ := hinf 0
  obtain ⟨b, hb⟩ := normInv_execution (d := alg.initial input) (fun q => ⟨input q, rfl⟩) σ k p
  refine ⟨k + 1, ?_⟩
  rw [execution_succ, hk, step_self, hb]
  cases ((alg.execution _ σ k).proc p).decision <;> simp [instr]

/-! ## The unreachable bivalent configuration -/

def c₀ : Config (Fin 3) Bool Bool St where
  memory _ := false
  proc
    | ⟨0, _⟩ => ⟨.norm true, none⟩
    | ⟨1, _⟩ => ⟨.A, none⟩
    | ⟨2, _⟩ => ⟨.B, none⟩

theorem fin3 (p : Fin 3) : p = 0 ∨ p = 1 ∨ p = 2 := by
  match p with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)

theorem mem12 {p : Fin 3} : p ∈ ({1, 2} : Set (Fin 3)) ↔ p = 1 ∨ p = 2 := by simp

/-- After `p₁`'s first step, `1` can never be decided. -/
def Inv1 (d : Config (Fin 3) Bool Bool St) : Prop :=
  d.proc 0 = ⟨.norm true, none⟩ ∧
  (d.proc 1 = ⟨.A0, none⟩ ∨ d.proc 1 = ⟨.A0', none⟩) ∧
  ((d.proc 2).state = .B ∨ (d.proc 2).state = .B0 ∨ (d.proc 2).state = .B0' ∨
    (d.proc 2).state = .B1) ∧
  (d.proc 2).decision ≠ some true

/-- After `p₂`'s first step, `0` can never be decided. -/
def Inv2 (d : Config (Fin 3) Bool Bool St) : Prop :=
  d.proc 0 = ⟨.norm true, none⟩ ∧
  (d.proc 2 = ⟨.B0, none⟩ ∨ d.proc 2 = ⟨.B0', none⟩) ∧
  ((d.proc 1).state = .A ∨ (d.proc 1).state = .A0 ∨ (d.proc 1).state = .A0' ∨
    (d.proc 1).state = .A1) ∧
  (d.proc 1).decision ≠ some false

theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide

theorem or_ne {o n : Option Bool} {v : Bool} (ho : o ≠ some v) (hn : n ≠ some v) :
    o.or n ≠ some v := by
  cases o with
  | none => simpa using hn
  | some w => simpa using ho

theorem inv1_step {d : Config (Fin 3) Bool Bool St} (hd : Inv1 d) {p : Fin 3}
    (hp : p = 1 ∨ p = 2) : Inv1 (alg.step d p) := by
  obtain ⟨h0, h1, h2, h2d⟩ := hd
  rcases hp with rfl | rfl
  · refine ⟨by rw [alg.step_local_other d ne01]; exact h0, ?_, ?_, ?_⟩
    · rw [step_self]
      rcases h1 with h1 | h1 <;> rw [h1] <;> simp [instr]
    · rw [alg.step_local_other d ne21]; exact h2
    · rw [alg.step_local_other d ne21]; exact h2d
  · refine ⟨by rw [alg.step_local_other d ne02]; exact h0,
      by rw [alg.step_local_other d ne12]; exact h1, ?_, ?_⟩
    · rw [step_self]
      rcases h2 with h | h | h | h <;> rw [h] <;> simp only [instr] <;>
        (try split) <;> simp
    · rw [step_self]
      rcases h2 with h | h | h | h <;> rw [h] <;> simp only [instr] <;>
        (try split) <;> exact or_ne h2d (by simp)

theorem inv2_step {d : Config (Fin 3) Bool Bool St} (hd : Inv2 d) {p : Fin 3}
    (hp : p = 1 ∨ p = 2) : Inv2 (alg.step d p) := by
  obtain ⟨h0, h2, h1, h1d⟩ := hd
  rcases hp with rfl | rfl
  · refine ⟨by rw [alg.step_local_other d ne01]; exact h0,
      by rw [alg.step_local_other d ne21]; exact h2, ?_, ?_⟩
    · rw [step_self]
      rcases h1 with h | h | h | h <;> rw [h] <;> simp only [instr] <;>
        (try split) <;> simp
    · rw [step_self]
      rcases h1 with h | h | h | h <;> rw [h] <;> simp only [instr] <;>
        (try split) <;> exact or_ne h1d (by simp)
  · refine ⟨by rw [alg.step_local_other d ne02]; exact h0, ?_, ?_, ?_⟩
    · rw [step_self]
      rcases h2 with h2 | h2 <;> rw [h2] <;> simp [instr]
    · rw [alg.step_local_other d ne12]; exact h1
    · rw [alg.step_local_other d ne12]; exact h1d

theorem inv_run {Inv : Config (Fin 3) Bool Bool St → Prop}
    (hstep : ∀ d, Inv d → ∀ p, (p = 1 ∨ p = 2) → Inv (alg.step d p)) :
    ∀ (ps : List (Fin 3)) (d : Config (Fin 3) Bool Bool St), Inv d →
      (∀ p ∈ ps, p ∈ ({1, 2} : Set (Fin 3))) → Inv (alg.run d ps)
  | [], _, h, _ => h
  | p :: ps, d, h, hps =>
    inv_run hstep ps _ (hstep d h p (mem12.mp (hps p (by simp))))
      (fun q hq => hps q (by simp [hq]))

theorem succ1_valent : alg.Valent {1, 2} (alg.step c₀ 1) false := by
  have hstart : Inv1 (alg.step c₀ 1) := by
    refine ⟨by rw [alg.step_local_other c₀ ne01]; rfl, ?_, ?_, ?_⟩
    · left; rw [step_self]; simp [c₀, instr]
    · left; rw [alg.step_local_other c₀ ne21]; rfl
    · rw [alg.step_local_other c₀ ne21]; simp [c₀]
  rintro ⟨d, ⟨ps, hps, rfl⟩, q, hq⟩
  obtain ⟨h0, h1, -, h2d⟩ := inv_run (Inv := Inv1) (fun _ h _ hp => inv1_step h hp) ps _ hstart hps
  rcases fin3 q with rfl | rfl | rfl
  · rw [h0] at hq; simp at hq
  · rcases h1 with h1 | h1 <;> rw [h1] at hq <;> simp at hq
  · exact h2d hq

theorem succ2_valent : alg.Valent {1, 2} (alg.step c₀ 2) true := by
  have hstart : Inv2 (alg.step c₀ 2) := by
    refine ⟨by rw [alg.step_local_other c₀ ne02]; rfl, ?_, ?_, ?_⟩
    · left; rw [step_self]; simp [c₀, instr]
    · left; rw [alg.step_local_other c₀ ne12]; rfl
    · rw [alg.step_local_other c₀ ne12]; simp [c₀]
  rintro ⟨d, ⟨ps, hps, rfl⟩, q, hq⟩
  obtain ⟨h0, h2, -, h1d⟩ := inv_run (Inv := Inv2) (fun _ h _ hp => inv2_step h hp) ps _ hstart hps
  rcases fin3 q with rfl | rfl | rfl
  · rw [h0] at hq; simp at hq
  · exact h1d hq
  · rcases h2 with h2 | h2 <;> rw [h2] at hq <;> simp at hq

/-- The four-step runs that decide `0` and `1` from `c₀`. -/
theorem c₀_decides_false : ((alg.run c₀ [1, 1, 2, 2]).proc 2).decision = some false := by
  simp [Algorithm.run, Algorithm.step, alg, instr, c₀, Function.update]

theorem c₀_decides_true : ((alg.run c₀ [2, 2, 1, 1]).proc 1).decision = some true := by
  simp [Algorithm.run, Algorithm.step, alg, instr, c₀, Function.update]

theorem c₀_bivalent : alg.Bivalent {1, 2} c₀ := by
  rw [Algorithm.bivalent_iff]
  exact ⟨⟨_, ⟨[1, 1, 2, 2], by simp, rfl⟩, 2, c₀_decides_false⟩,
    ⟨_, ⟨[2, 2, 1, 1], by simp, rfl⟩, 1, c₀_decides_true⟩⟩

/-- **Lemma 5 needs reachability**: without it, the statement of `bivalent_successor` is false,
even though COF termination holds. -/
theorem bivalent_successor_needs_reachability :
    ¬ ∀ (a : Algorithm (Fin 3) Bool Bool St), a.COFTermination →
      ∀ c, a.Bivalent {1, 2} c →
        a.Bivalent {1, 2} (a.step c 1) ∨ a.Bivalent {1, 2} (a.step c 2) := by
  intro h
  rcases h alg alg_cofTermination c₀ c₀_bivalent with h1 | h2
  · exact h1 (Or.inl succ1_valent)
  · exact h2 (Or.inr succ2_valent)

end COF.Checks.Lemma5Reachability
