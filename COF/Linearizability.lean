import COF.Objects

/-! Histories and linearizability, independently of any implementation.

A history is presented by its operation instances. Each one is an interval: the process that
invoked it, the operation, when it was invoked, and, once it has returned, its response and
when. Times are positions in the execution that produced the history. This is Herlihy and
Wing's model with each invocation already matched to its response, which sequential processes
make unambiguous. -/
namespace COF

/-- An event of a history: an invocation of `o` by `p`, or a response `r` to `p`'s pending
operation. -/
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
  /-- The response and when it was returned, once the instance has returned. -/
  returned : Option (Resp × ℕ)

/-- A finite history: its operation instances, in order of invocation. -/
abbrev History (P O Resp : Type*) := List (OpRecord P O Resp)

namespace History
variable {P O Resp : Type*}

open scoped Classical in
/-- Record an event that happened at time `t`. An invocation opens a new instance; a response
closes the pending instance of its process, which is unique because processes are
sequential. Which instance that is gets decided classically, so nothing is assumed of the
process type. -/
noncomputable def record (H : History P O Resp) (t : ℕ) : Option (Event P O Resp) → History P O Resp
  | none => H
  | some (.inv p o) => H ++ [⟨p, o, t, none⟩]
  | some (.res p r) => H.map fun a =>
      if a.proc = p ∧ a.returned.isNone then { a with returned := some (r, t) } else a

end History

namespace Object
variable {Q O Resp : Type*}

/-- A sequential history is legal from state `q`: applying its operations in order, the
specification returns exactly the recorded responses. -/
def Legal (obj : Object Q O Resp) : Q → List (O × Resp) → Prop
  | _, [] => True
  | q, (o, r) :: rest => (obj.transition o q).1 = r ∧ obj.Legal (obj.transition o q).2 rest

end Object

variable {P Q O Resp : Type*}

/-- Herlihy and Wing's linearizability. The witness `S` is the linearization: a sequence of
distinct instances of `H`, each paired with a response, that

* contains every completed instance with its actual response, while a pending instance may be
  included with a response chosen for it, or dropped;
* is legal for the sequential specification; and
* respects real-time order: no instance is placed after one that returned before it was
  invoked. -/
def Linearizable (obj : Object Q O Resp) (H : History P O Resp) : Prop :=
  ∃ S : List (OpRecord P O Resp × Resp),
    (S.map Prod.fst).Nodup ∧ (∀ x ∈ S, x.1 ∈ H) ∧
    (∀ a ∈ H, ∀ r t, a.returned = some (r, t) → (a, r) ∈ S) ∧
    obj.Legal obj.initial (S.map fun x => (x.1.op, x.2)) ∧
    ∀ x y, [x, y].Sublist S → ∀ r t, y.1.returned = some (r, t) → x.1.invokedAt ≤ t

end COF
