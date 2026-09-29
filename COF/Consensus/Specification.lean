import COF.SharedMemory.Algorithm

/-!
# Conflict-obstruction-free consensus (paper §4.1)

> A consensus algorithm satisfies the following properties:
> **Validity:** If a process decides a value `v`, then some process proposed `v`;
> **Agreement:** No two processes decide differently;
> **WF termination:** Every correct process decides in finitely many steps.
>
> Conflict-obstruction-free consensus retains Validity and Agreement, but replaces wait-free
> termination with the following weaker liveness condition:
> **COF termination:** If eventually only processes that proposed the same value take steps,
> then every correct process decides in finitely many steps.

`Validity`, `Agreement` and `COFTermination` state these properties of an `Algorithm`, and
`COFConsensus` is their conjunction. The processes' inputs are their proposals. `WFTermination`
is wait-free termination, which implies COF termination (`WFTermination.cofTermination`).

The termination properties are about infinite executions, in which every entry is a step
(`Admissible`). A process that has decided takes no further steps. A process that stops taking
steps before deciding has crashed, and a correct process that has not decided keeps taking steps.
So "every correct process decides in finitely many steps" says that no process takes infinitely
many steps.
-/

namespace COF.SharedMemory

variable {P R V S : Type*}

/-- Some process has decided `v` in `c`: `c` is "`v`-deciding" (paper §4.2). -/
def Config.Decided (c : Config P R V S) (v : Bool) : Prop :=
  ∃ p, (c.proc p).decision = some v

namespace Algorithm
variable (a : Algorithm P R V S)

/-! ## The specification -/

/-- **Validity**: in every configuration of every execution, a decided value is the input of some
process. -/
def Validity : Prop :=
  ∀ input c, a.Reachable input c → ∀ v, c.Decided v → ∃ p, input p = v

/-- **Agreement**: in every configuration of every execution, all decided values are equal.
Decisions are never revised, so this says that no two processes of an execution decide
differently. -/
def Agreement : Prop :=
  ∀ input c, a.Reachable input c → ∀ v w, c.Decided v → c.Decided w → v = w

/-- **COF termination**, for the executions from every initial configuration: if from some point
on only processes that proposed the same value `v` take steps, then every correct process decides
in finitely many steps, that is, no process takes infinitely many steps. -/
def COFTermination : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P), a.Admissible (a.initial input) σ →
    (∃ N v, ∀ k ≥ N, input (σ k) = v) →
    ∀ p, ¬ ∀ N, ∃ k ≥ N, σ k = p

/-- A **conflict-obstruction-free consensus** algorithm: Validity, Agreement and COF
termination. -/
def COFConsensus : Prop :=
  a.Validity ∧ a.Agreement ∧ a.COFTermination

/-! ## COF termination from reachable configurations -/

/-- COF termination also holds for executions from any reachable configuration: an admissible run
that reaches it (`exists_runAdmissible`) can be prepended without affecting either premise. So
quantifying over reachable starting points, as the proofs do, asks for nothing more. -/
theorem COFTermination.from_reachable {a : Algorithm P R V S} (h : a.COFTermination)
    {input : P → Bool} {c : Config P R V S} (hr : a.Reachable input c) {σ : ℕ → P}
    (hadm : a.Admissible c σ) (hhom : ∃ N v, ∀ k ≥ N, input (σ k) = v) (p : P) :
    ¬ ∀ N, ∃ k ≥ N, σ k = p := by
  obtain ⟨ps', _, rfl⟩ := hr
  obtain ⟨ps, -, hps, hrun⟩ := a.exists_runAdmissible (a.initial input) ps'
  rw [← hrun] at hadm
  obtain ⟨N, b, hN⟩ := hhom
  -- The execution from the initial configuration that first runs `ps`, then `σ`.
  have hhom' : ∃ N b, ∀ k ≥ N, input (prepend ps σ k) = b := by
    refine ⟨ps.length + N, b, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show ps.length ≤ k by omega)
    rw [prepend_add]
    exact hN j (by omega)
  intro hinf
  refine h input _ (a.admissible_prepend hps hadm) hhom' p fun M => ?_
  obtain ⟨k, hk, he⟩ := hinf M
  exact ⟨ps.length + k, by omega, by simpa using he⟩

/-- From a reachable configuration, if from some point on `σ` names only processes that proposed
the same value, and names `p` infinitely often, then not all of its entries are steps: at some
time, the process it names has already decided. This is how the proofs use COF termination. -/
theorem COFTermination.exists_decided {a : Algorithm P R V S} (h : a.COFTermination)
    {input : P → Bool} {c : Config P R V S} (hr : a.Reachable input c) (σ : ℕ → P)
    (hhom : ∃ N v, ∀ k ≥ N, input (σ k) = v) {p : P} (hinf : ∀ N, ∃ k ≥ N, σ k = p) :
    ∃ n, ((a.execution c σ n).proc (σ n)).decision ≠ none := by
  by_contra hne
  push Not at hne
  exact h.from_reachable hr hne hhom p hinf

/-! ## Related liveness conditions -/

/-- **WF termination**: every correct process decides in finitely many steps, whoever takes
steps, that is, no process takes infinitely many steps. -/
def WFTermination : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P), a.Admissible (a.initial input) σ →
    ∀ p, ¬ ∀ N, ∃ k ≥ N, σ k = p

/-- COF termination is "weaker" than WF termination: it is implied by it. It is also strictly
weaker, as `COF/Checks/Separation.lean` shows. -/
theorem WFTermination.cofTermination {a : Algorithm P R V S} (h : a.WFTermination) :
    a.COFTermination :=
  fun input σ hadm _ => h input σ hadm

end Algorithm
end COF.SharedMemory
