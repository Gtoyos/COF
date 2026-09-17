import COF.Valency
import COF.SharedMemory.Executions

/-! Consensus liveness under eventually homogeneous schedules. Quantifying over
reachable starting configurations makes closure under finite execution prefixes explicit.
No scheduler fairness is imposed: only infinitely scheduled processes must terminate. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- The COF termination clause in Section 4.1. -/
def COFTermination : Prop :=
  ∀ input c, a.Reachable input c → ∀ schedule : ℕ → P,
    (∃ N v, ∀ k ≥ N, input (schedule k) = v) →
    ∀ p, (∀ N, ∃ k ≥ N, schedule k = p) →
      ∃ n v, ((a.execution c schedule n).proc p).decision = some v

def Consensus : Prop := a.Safe ∧ a.COFTermination

/-- The same liveness clause, quantified only over executions from initial states. -/
def InitialCOFTermination : Prop :=
  ∀ input schedule,
    (∃ N v, ∀ k ≥ N, input (schedule k) = v) →
    ∀ p, (∀ N, ∃ k ≥ N, schedule k = p) →
      ∃ n v, ((a.execution (a.initial input) schedule n).proc p).decision = some v

/-- Quantifying over reachable starting states imposes no extra liveness assumption. -/
theorem cofTermination_iff_initial : a.COFTermination ↔ a.InitialCOFTermination := by
  constructor
  · intro h input schedule hhom p hinf
    exact h input _ (Reach.refl a _ _) schedule hhom p hinf
  · intro h input c hr schedule hhom p hinf
    obtain ⟨ps, _, rfl⟩ := hr
    obtain ⟨N, b, hN⟩ := hhom
    have hpref : ∃ N b, ∀ k ≥ N, input (prepend ps schedule k) = b := by
      refine ⟨ps.length + N, b, ?_⟩
      intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show ps.length ≤ k by omega)
      rw [prepend_add]
      exact hN j (by omega)
    have hinf' : ∀ N, ∃ k ≥ N, prepend ps schedule k = p := by
      intro M
      obtain ⟨k, hk, he⟩ := hinf M
      exact ⟨ps.length + k, by omega, by simpa using he⟩
    obtain ⟨n, v, hd⟩ := h input (prepend ps schedule) hpref p hinf'
    have hd' := a.execution_decision (show n ≤ ps.length + n by omega) hd
    exact ⟨n, v, by simpa [a.execution_prepend] using hd'⟩

theorem execution_solo (c : Config P R V S) (p : P) (n : ℕ) :
    a.execution c (fun _ => p) n = a.run c (List.replicate n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [execution, ih, List.replicate_succ', run_append]
    rfl

/-- A reachable configuration admits a finite deciding solo continuation. -/
theorem solo_terminates (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} (hr : a.Reachable input c) (p : P) :
    ∃ ps, (∀ q ∈ ps, q = p) ∧ ∃ v, ((a.run c ps).proc p).decision = some v := by
  obtain ⟨n, v, hd⟩ := ht input c hr (fun _ => p)
    ⟨0, input p, by simp⟩ p (fun N => ⟨N, le_rfl, rfl⟩)
  exact ⟨List.replicate n p, by simp, v, by simpa [a.execution_solo] using hd⟩

theorem valent_decision {active : Set P} {c d : Config P R V S} {v w : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) (hd : d.Decided w) : v = w := by
  cases v <;> cases w
  · rfl
  · exact (hv ⟨d, hr, hd⟩).elim
  · exact (hv ⟨d, hr, hd⟩).elim
  · rfl

/-- Opposite valencies are distinguishable by each active process, using solo termination. -/
theorem indist_valent_eq (ht : a.COFTermination) {input : P → Bool}
    {active : Set P} {c d : Config P R V S} {p : P} {v w : Bool}
    (hr : a.Reachable input c) (hp : p ∈ active)
    (hi : Indist {p} c d) (hc : a.Valent active c v) (hd : a.Valent active d w) :
    v = w := by
  obtain ⟨ps, hps, b, hb⟩ := a.solo_terminates ht hr p
  have hactive : ∀ q ∈ ps, q ∈ active := by
    intro q hq
    simpa [hps q hq] using hp
  have he := a.indist_run hi (ps := ps) (by simpa using hps)
  have hb' : ((a.run d ps).proc p).decision = some b := by
    rw [← he.2 p (by simp)]
    exact hb
  exact (a.valent_decision hc ⟨ps, hactive, rfl⟩ ⟨p, hb⟩).trans
    (a.valent_decision hd ⟨ps, hactive, rfl⟩ ⟨p, hb'⟩).symm

end COF.SharedMemory.Algorithm
