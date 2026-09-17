import COF.SharedMemory.Model

/-! Prefixing and suffixing infinite schedules. These lemmas relate termination
from arbitrary reachable configurations to termination from initial configurations. -/
namespace COF.SharedMemory.Algorithm
variable {P R V S : Type*} [DecidableEq P] [DecidableEq R]
variable (a : Algorithm P R V S)

/-- Shift the initial step from the schedule into the starting configuration. -/
theorem execution_shift (c : Config P R V S) (schedule : ℕ → P) (n : ℕ) :
    a.execution c schedule (n + 1) =
      a.execution (a.step c (schedule 0)) (fun k => schedule (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.step (a.execution c schedule (n + 1)) (schedule (n + 1)) = _
    rw [ih]
    rfl

/-- Decisions persist along an infinite execution. -/
theorem execution_decision {c : Config P R V S} {schedule : ℕ → P}
    {n m : ℕ} {p : P} {v : Bool} (hn : n ≤ m)
    (hd : ((a.execution c schedule n).proc p).decision = some v) :
    ((a.execution c schedule m).proc p).decision = some v := by
  induction m, hn using Nat.le_induction with
  | base => exact hd
  | succ m _ ih => exact a.step_decision _ _ _ _ ih

/-- Prepend a finite schedule to an infinite one. -/
def prepend (ps : List P) (schedule : ℕ → P) : ℕ → P :=
  match ps with
  | [] => schedule
  | p :: ps => fun n => match n with
    | 0 => p
    | n + 1 => prepend ps schedule n

omit [DecidableEq P] in
@[simp] theorem prepend_add (ps : List P) (schedule : ℕ → P) (n : ℕ) :
    prepend ps schedule (ps.length + n) = schedule n := by
  induction ps with
  | nil => simp [prepend]
  | cons p ps ih => simpa [prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem execution_prepend (c : Config P R V S) (ps : List P) (schedule : ℕ → P) (n : ℕ) :
    a.execution c (prepend ps schedule) (ps.length + n) = a.execution (a.run c ps) schedule n := by
  induction ps generalizing c with
  | nil => simp [prepend]
  | cons p ps ih =>
    rw [List.length_cons, Nat.succ_add, a.execution_shift]
    exact ih (a.step c p)

end COF.SharedMemory.Algorithm
