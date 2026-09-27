import COF.Objects

/-!
# Histories and linearizability

Herlihy and Wing's linearizability, independently of any implementation. A history lists the
operation instances of a finite execution, each as an interval: the process that invoked it, the
operation, when it was invoked, and, once it has returned, its response and when. Times are
positions in the execution. Processes are sequential, so every response belongs to the unique
pending instance of its process, and the history can record instances directly instead of
matching invocation and response events.
-/

namespace COF

/-- An event of a history: an invocation of `o` by `p`, or a response `r` to `p`. -/
inductive Event (P O Resp : Type*) where
  | inv (p : P) (o : O)
  | res (p : P) (r : Resp)

/-- An operation instance of a history, as an interval. -/
structure OpRecord (P O Resp : Type*) where
  /-- The process that invoked it. -/
  proc : P
  /-- The operation invoked. -/
  op : O
  /-- When it was invoked. -/
  invokedAt : ℕ
  /-- Its response and when it was returned, once it has returned. -/
  returned : Option (Resp × ℕ)

/-- A finite history: its operation instances, in order of invocation. -/
abbrev History (P O Resp : Type*) := List (OpRecord P O Resp)

namespace History
variable {P O Resp : Type*}

open scoped Classical in
/-- Record an event that happens at time `t`. An invocation opens a new instance; a response
closes the pending instance of its process. -/
noncomputable def record (H : History P O Resp) (t : ℕ) :
    Option (Event P O Resp) → History P O Resp
  | none => H
  | some (.inv p o) => H ++ [⟨p, o, t, none⟩]
  | some (.res p r) => H.map fun a =>
      if a.proc = p ∧ a.returned.isNone then { a with returned := some (r, t) } else a

end History

namespace Object
variable {Q O Resp : Type*}

/-- A sequence of operations with responses is legal from state `q`: applying the operations in
order, the object returns exactly the recorded responses. -/
def Legal (obj : Object Q O Resp) : Q → List (O × Resp) → Prop
  | _, [] => True
  | q, (o, r) :: rest => (obj.transition o q).1 = r ∧ obj.Legal (obj.transition o q).2 rest

end Object

variable {P Q O Resp : Type*}

/-- `S` linearizes the history `H` for `obj`: it orders some instances of `H`, each paired with a
response, as a legal sequential execution that respects real-time order. Completed instances must
appear with their actual responses; a pending instance may be included, with a response chosen
for it, or left out. -/
structure IsLinearization (obj : Object Q O Resp) (H : History P O Resp)
    (S : List (OpRecord P O Resp × Resp)) : Prop where
  /-- No instance appears twice. -/
  nodup : (S.map Prod.fst).Nodup
  /-- Only instances of `H` appear. -/
  subset : ∀ x ∈ S, x.1 ∈ H
  /-- Every completed instance appears, with the response it returned. -/
  complete : ∀ a ∈ H, ∀ r t, a.returned = some (r, t) → (a, r) ∈ S
  /-- The sequential execution is legal for the object, from its initial state. -/
  legal : obj.Legal obj.initial (S.map fun x => (x.1.op, x.2))
  /-- Real-time order: if `y` returned before `x` was invoked, `x` does not come before `y`. -/
  realTime : ∀ x y, [x, y].Sublist S → ∀ r t, y.1.returned = some (r, t) → x.1.invokedAt ≤ t

/-- The history `H` is linearizable for `obj` (Herlihy and Wing). -/
def Linearizable (obj : Object Q O Resp) (H : History P O Resp) : Prop :=
  ∃ S, IsLinearization obj H S

end COF
