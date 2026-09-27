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

The phrase "take steps" admits two readings, because a process that has decided may still be
scheduled. `COFTermination` counts all scheduled steps. `StrictCOFTermination` counts only steps
of pending operations, as the paper's §2 does ("Φ takes a step … when the process p that invoked
Φ takes a step and Φ has not yet returned a response"). The strict reading demands termination in
more executions and implies the other (`StrictCOFTermination.cofTermination`), so the
impossibility theorem, which assumes `COFTermination`, covers both.
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
on every scheduled process proposed the same value `v`, then every process that is scheduled
infinitely often decides.

A process scheduled infinitely often is correct. A correct process scheduled only finitely often
has no pending operation, so it has already decided. -/
def COFTermination : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P),
    (∃ N v, ∀ k ≥ N, input (σ k) = v) →
    ∀ p, (∀ N, ∃ k ≥ N, σ k = p) →
      ∃ n v, ((a.execution (a.initial input) σ n).proc p).decision = some v

/-- A **conflict-obstruction-free consensus** algorithm: Validity, Agreement and COF
termination. -/
def COFConsensus : Prop :=
  a.Validity ∧ a.Agreement ∧ a.COFTermination

/-! ## COF termination from reachable configurations -/

/-- COF termination also holds for executions from any reachable configuration: the finite
schedule that reached it can be prepended without affecting either premise. So quantifying over
reachable starting points, as the proofs do, asks for nothing more. -/
theorem COFTermination.from_reachable {a : Algorithm P R V S} (h : a.COFTermination)
    {input : P → Bool} {c : Config P R V S} (hr : a.Reachable input c) (σ : ℕ → P)
    (hhom : ∃ N v, ∀ k ≥ N, input (σ k) = v) (p : P) (hinf : ∀ N, ∃ k ≥ N, σ k = p) :
    ∃ n v, ((a.execution c σ n).proc p).decision = some v := by
  obtain ⟨ps, _, rfl⟩ := hr
  obtain ⟨N, b, hN⟩ := hhom
  -- The execution from the initial configuration that first runs `ps`, then `σ`.
  have hhom' : ∃ N b, ∀ k ≥ N, input (prepend ps σ k) = b := by
    refine ⟨ps.length + N, b, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show ps.length ≤ k by omega)
    rw [prepend_add]
    exact hN j (by omega)
  have hinf' : ∀ M, ∃ k ≥ M, prepend ps σ k = p := by
    intro M
    obtain ⟨k, hk, he⟩ := hinf M
    exact ⟨ps.length + k, by omega, by simpa using he⟩
  obtain ⟨n, v, hd⟩ := h input _ hhom' p hinf'
  have hd' := a.execution_decision (show n ≤ ps.length + n by omega) hd
  exact ⟨n, v, by simpa [a.execution_prepend] using hd'⟩

/-! ## Related liveness conditions -/

/-- **WF termination**: every process that is scheduled infinitely often decides, whatever the
schedule. -/
def WFTermination : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P) (p : P), (∀ N, ∃ k ≥ N, σ k = p) →
    ∃ n v, ((a.execution (a.initial input) σ n).proc p).decision = some v

/-- COF termination is "weaker" than WF termination: it is implied by it. It is also strictly
weaker, as `COF/Checks/Separation.lean` shows. -/
theorem WFTermination.cofTermination {a : Algorithm P R V S} (h : a.WFTermination) :
    a.COFTermination :=
  fun input σ _ p hinf => h input σ p hinf

/-- `p` takes a step of its operation at time `k` of the execution from `initial input` under `σ`:
it is scheduled, and it has not decided yet. -/
def TakesOperationStep (input : P → Bool) (σ : ℕ → P) (k : ℕ) (p : P) : Prop :=
  σ k = p ∧ ((a.execution (a.initial input) σ k).proc p).decision = none

/-- **COF termination, strict reading**: as `COFTermination`, but a scheduled process that has
already decided takes no step of an operation, so it does not count in the premise. -/
def StrictCOFTermination : Prop :=
  ∀ (input : P → Bool) (σ : ℕ → P),
    (∃ N v, ∀ k ≥ N, ∀ p, a.TakesOperationStep input σ k p → input p = v) →
    ∀ p, (∀ N, ∃ k ≥ N, σ k = p) →
      ∃ n v, ((a.execution (a.initial input) σ n).proc p).decision = some v

/-- The strict reading demands termination in more executions, so it implies `COFTermination`. -/
theorem StrictCOFTermination.cofTermination {a : Algorithm P R V S}
    (h : a.StrictCOFTermination) : a.COFTermination :=
  fun input σ ⟨N, v, hN⟩ => h input σ ⟨N, v, fun k hk _ ⟨hp, _⟩ => hp ▸ hN k hk⟩

end Algorithm
end COF.SharedMemory
