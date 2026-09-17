import COF

/-! Non-vacuity checks for the impossibility result.

These make precise two claims that the impossibility theorem would be empty
without:

1. `consensus_satisfiable` — `Safe ∧ COFTermination` is satisfiable, so
   `no_cof_consensus` is not vacuously true because its hypotheses contradict
   each other. The witness is a one-process system in which the process decides
   its own input.

2. `alt_not_homogeneous` — the COF liveness hypothesis genuinely exempts some
   schedules, so `COFTermination` is strictly weaker than wait-free termination
   and the impossibility is not a restatement of FLP.

See `MODEL.md`. -/

namespace COF.NonVacuity
open COF COF.SharedMemory

/-- One process, one register, trivial values, local state = own proposal. -/
def solo : Algorithm Unit Unit Unit Bool where
  initialMemory := fun _ => ()
  initialState _ b := b
  instruction _ s := .write () () ⟨s, some s⟩

/-- Every step leaves a decision in place. -/
theorem solo_step_decides (d : Config Unit Unit Unit Bool) (p : Unit) :
    ∃ v, ((solo.step d p).proc p).decision = some v := by
  refine ⟨(d.proc p).decision.getD (d.proc p).state, ?_⟩
  cases h : (d.proc p).decision <;>
    simp [Algorithm.step, solo, Function.update, h]

/-- The invariant: local state is always the process's own input, and any
decision is its own input. -/
def Inv (input : Unit → Bool) (d : Config Unit Unit Unit Bool) : Prop :=
  ∀ r, (d.proc r).state = input r ∧
    ((d.proc r).decision = none ∨ (d.proc r).decision = some (input r))

theorem solo_step_inv {input : Unit → Bool} {d : Config Unit Unit Unit Bool}
    (h : Inv input d) (t : Unit) : Inv input (solo.step d t) := by
  intro r
  obtain ⟨hs, hdec⟩ := h r
  obtain rfl : r = t := Subsingleton.elim r t
  rcases hdec with hn | hn <;>
    simp [Algorithm.step, solo, Function.update, hs, hn]

theorem solo_run_inv {input : Unit → Bool} :
    ∀ (ps : List Unit) {d : Config Unit Unit Unit Bool}, Inv input d →
      Inv input (solo.run d ps)
  | [], _, h => h
  | t :: ts, _, h => solo_run_inv ts (solo_step_inv h t)

theorem solo_inv {input : Unit → Bool} {c : Config Unit Unit Unit Bool}
    (h : solo.Reachable input c) : Inv input c := by
  obtain ⟨ps, -, rfl⟩ := h
  exact solo_run_inv ps (fun r => ⟨rfl, Or.inl rfl⟩)

theorem solo_safe : solo.Safe := by
  intro input c hr
  have hinv := solo_inv hr
  have hdec : ∀ v, c.Decided v → v = input () := by
    rintro v ⟨p, hp⟩
    obtain rfl : p = () := Subsingleton.elim p ()
    rcases (hinv ()).2 with h | h
    · rw [h] at hp; cases hp
    · rw [h] at hp; exact (Option.some.inj hp).symm
  exact ⟨fun v w hv hw => (hdec v hv).trans (hdec w hw).symm,
    fun v hv => ⟨(), (hdec v hv).symm⟩⟩

theorem solo_termination : solo.COFTermination := by
  intro input c _ schedule _ p hinf
  obtain ⟨k, -, hk⟩ := hinf 0
  obtain ⟨v, hv⟩ := solo_step_decides (solo.execution c schedule k) p
  refine ⟨k + 1, v, ?_⟩
  change ((solo.step (solo.execution c schedule k) (schedule k)).proc p).decision = _
  rw [hk]; exact hv

/-- **The hypotheses of the impossibility theorem are jointly satisfiable.** -/
theorem consensus_satisfiable : ∃ a : Algorithm Unit Unit Unit Bool, a.Consensus :=
  ⟨solo, solo_safe, solo_termination⟩

/-- Sanity check that decisions really are reachable in this witness, i.e. `Safe`
is not satisfied merely because nothing ever decides. -/
theorem solo_decides :
    ((solo.run (solo.initial (fun _ => true)) [()]).proc ()).decision = some true := by
  simp [Algorithm.run, Algorithm.step, Algorithm.initial, solo, Function.update]


/-- Two processes with opposite proposals. -/
def two : Bool → Bool := id

/-- The alternating schedule. -/
def alt : ℕ → Bool := fun k => k % 2 == 0

/-- The alternating schedule is *not* eventually homogeneous, hence
`COFTermination` imposes no requirement whatsoever on it, while wait-free
termination would. -/
theorem alt_not_homogeneous : ¬ ∃ N v, ∀ k ≥ N, two (alt k) = v := by
  rintro ⟨N, v, h⟩
  have h1 := h (2 * N) (by omega)
  have h2 := h (2 * N + 1) (by omega)
  have m1 : (2 * N) % 2 = 0 := by omega
  have m2 : (2 * N + 1) % 2 = 1 := by omega
  rw [show alt (2 * N) = true by simp [alt, m1]] at h1
  rw [show alt (2 * N + 1) = false by simp [alt, m2]] at h2
  cases v <;> simp [two] at h1 h2

/-- Restated: for every algorithm, `COFTermination` says nothing about the
alternating schedule, so it cannot entail termination under all schedules. -/
theorem cofTermination_silent_on_alt
    {R V S : Type} [DecidableEq R] (a : Algorithm Bool R V S)
    (_ : a.COFTermination) :
    ¬ ∃ N v, ∀ k ≥ N, two (alt k) = v := alt_not_homogeneous

end COF.NonVacuity
