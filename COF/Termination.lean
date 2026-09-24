import COF.Valency
import COF.SharedMemory.Executions

/-! Consensus liveness under eventually homogeneous schedules. Quantifying over
reachable starting configurations makes closure under finite execution prefixes explicit.
No scheduler fairness is imposed: only infinitely scheduled processes must terminate. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*}
variable (a : Algorithm P R V S)

/-- The COF termination clause in Section 4.1: if eventually only processes that proposed
the same value take steps, then every correct process decides after finitely many steps.

"Correct" is the paper's notion — takes infinitely many steps — so a process that stops
being scheduled is owed nothing. The homogeneity premise constrains *every* step past `N`,
including steps of processes that have already decided; that makes this liveness clause
weaker than the paper's, hence the impossibility stronger. `TraceBridge.lean` derives it
from the paper-faithful trace-level condition. -/
def COFTermination : Prop :=
  ∀ input c, a.Reachable input c → ∀ schedule : ℕ → P,
    (∃ N v, ∀ k ≥ N, input (schedule k) = v) →
    ∀ p, (∀ N, ∃ k ≥ N, schedule k = p) →
      ∃ n v, ((a.execution c schedule n).proc p).decision = some v

/-- What the impossibility theorem refutes: safety together with COF termination. -/
def Consensus : Prop := a.Safe ∧ a.COFTermination

/-- The same liveness clause, quantified only over executions from initial states. -/
def InitialCOFTermination : Prop :=
  ∀ input schedule,
    (∃ N v, ∀ k ≥ N, input (schedule k) = v) →
    ∀ p, (∀ N, ∃ k ≥ N, schedule k = p) →
      ∃ n v, ((a.execution (a.initial input) schedule n).proc p).decision = some v

/-- Quantifying over reachable starting states imposes no extra liveness assumption: a
finite prefix can be prepended to the infinite schedule without disturbing either the
homogeneity premise or the set of infinitely scheduled processes. So the convenient form
used throughout is exactly the paper's requirement on whole executions. -/
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

/-- The constant schedule executes the same configurations as a finite solo run, which is
what turns the liveness clause into a finite deciding continuation. -/
theorem execution_solo (c : Config P R V S) (p : P) (n : ℕ) :
    a.execution c (fun _ => p) n = a.run c (List.replicate n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [execution, ih, List.replicate_succ', run_append]
    rfl

/-- Every reachable configuration admits a finite solo continuation in which `p` decides.
A solo schedule is trivially homogeneous and schedules `p` infinitely often, so COF
termination applies to it. This is the sole source of actual decisions in the argument,
and hence what keeps the negative `Valent` from being vacuous. -/
theorem solo_terminates (ht : a.COFTermination) {input : P → Bool}
    {c : Config P R V S} (hr : a.Reachable input c) (p : P) :
    ∃ ps, (∀ q ∈ ps, q = p) ∧ ∃ v, ((a.run c ps).proc p).decision = some v := by
  obtain ⟨n, v, hd⟩ := ht input c hr (fun _ => p)
    ⟨0, input p, by simp⟩ p (fun N => ⟨N, le_rfl, rfl⟩)
  exact ⟨List.replicate n p, by simp, v, by simpa [a.execution_solo] using hd⟩

/-- A decision taken by an `active`-only continuation must agree with the valency. -/
theorem valent_decision {active : Set P} {c d : Config P R V S} {v w : Bool}
    (hv : a.Valent active c v) (hr : a.Reach active c d) (hd : d.Decided w) : v = w := by
  cases v <;> cases w
  · rfl
  · exact (hv ⟨d, hr, hd⟩).elim
  · exact (hv ⟨d, hr, hd⟩).elim
  · rfl

/-- Two configurations that some active process `p` cannot tell apart have the same
valency. Running `p` solo from each decides the same value in both — `p` sees the same
thing either way — and a valency must agree with any decision reachable from it.

This is the engine of every critical-configuration argument: it converts
indistinguishability into equality of valencies, and it is where solo termination is
needed to rule out the vacuous case where nothing is ever decided. -/
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
