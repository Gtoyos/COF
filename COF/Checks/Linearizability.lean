import COF.Linearizability

/-!
# Linearizability behaves as Herlihy and Wing's

`IsLinearization` is the one definition of the development that the paper does not spell out, so
this file tests it on small histories, where the answer is known.

* A read that starts after a `write(1)` has returned, and returns `0`, is **rejected**. Only
  real-time order rules it out: ordering the read first would be legal (`stale_read_rejected`).
* Two completed proposals to consensus that return different values are **rejected**
  (`disagreement_rejected`).
* A pending `write(1)` may take effect, so a concurrent read may return `1`
  (`pending_write_takes_effect`), or be dropped, so the read may return `0`
  (`pending_write_dropped`). Both are **accepted**.
-/

namespace COF.Checks.LinearizabilityExamples

/-- A read/write register holding a natural number, initially `0`. -/
inductive RegOp | read | write (v : ℕ)

def reg : Object ℕ RegOp (Option ℕ) where
  initial := 0
  transition
    | .read, q => (some q, q)
    | .write v, _ => (none, v)

/-- If every write writes `1`, then after a write every later read returns `1`. -/
theorem reg_reads_one : ∀ (q : ℕ) (L : List (RegOp × Option ℕ)),
    (∀ x ∈ L, x.1 = .read ∨ x.1 = .write 1) → reg.Legal q L →
    q = 1 → ∀ x ∈ L, x.1 = .read → x.2 = some 1
  | _, [], _, _, _, x, hx, _ => by simp at hx
  | q, (o, r) :: L, hops, ⟨hr, hL⟩, hq, x, hx, hread => by
    subst hq
    rcases hops (o, r) (by simp) with rfl | rfl
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr.symm
      · exact reg_reads_one _ L (fun y hy => hops y (by simp [hy])) hL rfl x hx hread
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp at hread
      · exact reg_reads_one _ L (fun y hy => hops y (by simp [hy])) hL rfl x hx hread

theorem reg_read_after_write : ∀ (q : ℕ) (L₁ L₂ : List (RegOp × Option ℕ)) (r : Option ℕ),
    (∀ x ∈ L₁ ++ (RegOp.write 1, r) :: L₂, x.1 = .read ∨ x.1 = .write 1) →
    reg.Legal q (L₁ ++ (RegOp.write 1, r) :: L₂) →
    ∀ x ∈ L₂, x.1 = .read → x.2 = some 1
  | q, [], L₂, r, hops, ⟨_, hL⟩, x, hx, hread =>
    reg_reads_one _ L₂ (fun y hy => hops y (by simp [hy])) hL rfl x hx hread
  | q, y :: L₁, L₂, r, hops, ⟨_, hL⟩, x, hx, hread =>
    reg_read_after_write _ L₁ L₂ r (fun z hz => hops z (List.mem_cons_of_mem _ hz)) hL x hx hread

/-- `write(1)` by `p₀` over `[0,1]`, then `read` by `p₁` over `[2,3]` returning the stale `0`. -/
def w1 : OpRecord (Fin 2) RegOp (Option ℕ) := ⟨0, .write 1, 0, some (none, 1)⟩
def r0 : OpRecord (Fin 2) RegOp (Option ℕ) := ⟨1, .read, 2, some (some 0, 3)⟩

/-- **Rejected**: real-time order forbids ordering the read before the completed write. -/
theorem stale_read_rejected : ¬ COF.Linearizable reg [w1, r0] := by
  rintro ⟨S, -, hsub, hcomp, hlegal, hrt⟩
  have hw : (w1, (none : Option ℕ)) ∈ S := hcomp w1 (by simp) none 1 rfl
  have hr : (r0, some 0) ∈ S := hcomp r0 (by simp) (some 0) 3 rfl
  have hops : ∀ x ∈ S.map (fun x => (x.1.op, x.2)), x.1 = .read ∨ x.1 = .write 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_cons.mp (hsub y hy) with h | h
    · right; rw [h]; rfl
    · left; rw [List.mem_singleton.mp h]; rfl
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hr
  rcases List.mem_append.mp hw with hA | hB
  · obtain ⟨A₁, A₂, rfl⟩ := List.mem_iff_append.mp hA
    have := reg_read_after_write 0 (A₁.map fun x => (x.1.op, x.2))
      (A₂.map (fun x => (x.1.op, x.2)) ++ (RegOp.read, some 0) :: B.map fun x => (x.1.op, x.2))
      none (by simpa [w1, r0] using hops) (by simpa [reg, w1, r0] using hlegal)
      (RegOp.read, some 0) (by simp) rfl
    simp at this
  · rcases List.mem_cons.mp hB with h | hB
    · simp [w1, r0] at h
    · have hsl : [(r0, some 0), (w1, none)].Sublist (A ++ (r0, some 0) :: B) :=
        (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hB)).trans
          (List.sublist_append_right A _)
      have := hrt _ _ hsl none 1 rfl
      simp [r0] at this

/-- Pending `write(1)` over `[0,∞)`, `read` over `[1,2]` returning `1`. -/
def w1p : OpRecord (Fin 2) RegOp (Option ℕ) := ⟨0, .write 1, 0, none⟩
def r1 : OpRecord (Fin 2) RegOp (Option ℕ) := ⟨1, .read, 1, some (some 1, 2)⟩
def r0' : OpRecord (Fin 2) RegOp (Option ℕ) := ⟨1, .read, 1, some (some 0, 2)⟩

theorem pair_sublist {α : Type*} {x y a b : α} (h : [x, y].Sublist [a, b]) : x = a ∧ y = b := by
  have := h.eq_of_length (by simp)
  simp_all

theorem single_no_pair {α : Type*} {x y a : α} (h : [x, y].Sublist [a]) : False := by
  have := h.length_le; simp at this

/-- **Accepted**: a pending write may be linearized (take effect) before a later read. -/
theorem pending_write_takes_effect : COF.Linearizable reg [w1p, r1] := by
  refine ⟨[(w1p, none), (r1, some 1)], ?_, ?_, ?_, ?_, ?_⟩
  · simp [w1p, r1]
  · simp
  · simp [w1p, r1]
  · simp [Object.Legal, reg, w1p, r1]
  · intro x y hxy r t _
    obtain ⟨rfl, rfl⟩ := pair_sublist hxy
    simp [w1p]

/-- **Accepted**: a pending write may be dropped, so the read may still return `0`. -/
theorem pending_write_dropped : COF.Linearizable reg [w1p, r0'] := by
  refine ⟨[(r0', some 0)], by simp, by simp, by simp [w1p, r0'], ?_, ?_⟩
  · simp [Object.Legal, reg, r0']
  · intro x y hxy; exact (single_no_pair hxy).elim

/-- Every response in a legal consensus history from a decided state is the decided value. -/
theorem consensus_legal_some (b : Bool) : ∀ L : List (Bool × Bool),
    consensusObject.Legal (some b) L → ∀ x ∈ L, x.2 = b
  | [], _, x, hx => by simp at hx
  | (o, r) :: L, ⟨hr, hL⟩, x, hx => by
    simp only [consensusObject, Option.getD_some] at hr hL
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hr.symm
    · exact consensus_legal_some b L hL x hx

/-- `propose(0)` by `p₀` over `[0,2]` returning `0`, and `propose(1)` by `p₁` over `[1,3]`
returning `1`. -/
def pa : OpRecord (Fin 2) Bool Bool := ⟨0, false, 0, some (false, 2)⟩
def pb : OpRecord (Fin 2) Bool Bool := ⟨1, true, 1, some (true, 3)⟩

/-- **Rejected**: two completed proposals that returned different values. -/
theorem disagreement_rejected : ¬ COF.Linearizable consensusObject [pa, pb] := by
  rintro ⟨S, -, -, hcomp, hlegal, -⟩
  have ha := List.mem_map_of_mem (f := fun x => (x.1.op, x.2)) (hcomp pa (by simp) false 2 rfl)
  have hb := List.mem_map_of_mem (f := fun x => (x.1.op, x.2)) (hcomp pb (by simp) true 3 rfl)
  generalize S.map (fun x => (x.1.op, x.2)) = L at ha hb hlegal
  cases L with
  | nil => simp at ha
  | cons y L =>
    obtain ⟨hy, hL⟩ := hlegal
    simp only [consensusObject, Option.getD_none] at hy hL
    have key : ∀ x ∈ y :: L, x.2 = y.1 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy.symm
      · exact consensus_legal_some _ L hL x hx
    have h1 : false = y.1 := key _ ha
    have h2 : true = y.1 := key _ hb
    exact absurd (h1.trans h2.symm) (by decide)

end COF.Checks.LinearizabilityExamples
