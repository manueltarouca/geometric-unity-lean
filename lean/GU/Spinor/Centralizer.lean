import GU.Spinor.Reductions

/-!
# The centraliser of `J` in `spin(6,4)` has dimension exactly 25 (`= dim u(3,2)`)

`u32c` lists, for each pair of planes, the two combinations that do *not* commute with `J`.
`allU = u32 ++ u32c` has 45 elements (`= dim so(6,4)`), each a sum of at most two bivectors of
the (6,4) block, linearly independent by a diagonal trace-Gram matrix (`allU_linIndep`). Inside
their span `V`:

`centralizer_eq`: `X ∈ V` commutes with `J` iff `X ∈ span(u32)`.

Together with `u32_linIndep` this pins the centraliser at dimension 25, upgrading the lower
bound of `Reductions.lean` (review-3 item 7). That `V` is all of `spin(6,4)` follows from the
dimension count 45; the explicit span equality with the bivector list is not formalised.
-/

namespace GU.Spinor

open Matrix CSum

def u32c : List CSum :=
  ((List.finRange 5).flatMap fun i => (List.finRange 5).filterMap fun j =>
    if i < j then some (i, j) else none).flatMap fun ij =>
      let p := planes.get ⟨ij.1, by simp [planes]⟩
      let q := planes.get ⟨ij.2, by simp [planes]⟩
      if sameType p q then
        [biv p.1 q.1 ++ neg (biv p.2 q.2), biv p.1 q.2 ++ biv p.2 q.1]
      else
        [biv p.1 q.1 ++ biv p.2 q.2, biv p.1 q.2 ++ neg (biv p.2 q.1)]

def allU : List CSum := u32 ++ u32c

theorem allU_length : allU.length = 45 := by decide
theorem u32c_length : u32c.length = 20 := by decide

def U (i : Fin 45) : CSum := allU.get (Fin.cast allU_length.symm i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allU_gram_offdiag : ∀ i j : Fin 45, i ≠ j → trPair (U i) (U j) = 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allU_gram_diag : ∀ i : Fin 45, trPair (U i) (U i) ≠ 0 := by decide +kernel

/-- The 45 elements are linearly independent (`= dim so(6,4)`). -/
theorem allU_linIndep : LinearIndependent ℝ (fun i => toMat (U i)) :=
  linIndep_of_gram _ allU_gram_offdiag allU_gram_diag

def U25 (i : Fin 25) : CSum := u32.get (Fin.cast u32_length.symm i)
def Uc (j : Fin 20) : CSum := u32c.get (Fin.cast u32c_length.symm j)
def V (j : Fin 20) : CSum := comm (Uc j) Jc

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem U25_comm : ∀ i : Fin 25, isZero (comm (U25 i) Jc) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem V_gram_offdiag : ∀ i j : Fin 20, i ≠ j → trPair (V i) (V j) = 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem V_gram_diag : ∀ i : Fin 20, trPair (V i) (V i) ≠ 0 := by decide +kernel

theorem V_linIndep : LinearIndependent ℝ (fun j => toMat (V j)) :=
  linIndep_of_gram _ V_gram_offdiag V_gram_diag

/-- **Centraliser of `J`**: `X = Σ aᵢ u32ᵢ + Σ bⱼ u32cⱼ` commutes with `J` iff `b = 0`. -/
theorem centralizer_iff (a : Fin 25 → ℝ) (b : Fin 20 → ℝ) :
    ((∑ i, a i • toMat (U25 i)) + ∑ j, b j • toMat (Uc j)) * toMat Jc =
      toMat Jc * ((∑ i, a i • toMat (U25 i)) + ∑ j, b j • toMat (Uc j)) ↔ b = 0 := by
  have h1 : ∀ i, toMat (U25 i) * toMat Jc = toMat Jc * toMat (U25 i) := fun i => by
    have := toMat_eq_zero (U25_comm i); rwa [toMat_comm, sub_eq_zero] at this
  have key : ((∑ i, a i • toMat (U25 i)) + ∑ j, b j • toMat (Uc j)) * toMat Jc -
      toMat Jc * ((∑ i, a i • toMat (U25 i)) + ∑ j, b j • toMat (Uc j)) =
      ∑ j, b j • toMat (V j) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, h1, V, toMat_comm, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [← sub_eq_zero, key]
  constructor
  · intro h
    funext j
    exact (Fintype.linearIndependent_iff.mp V_linIndep) b h j
  · rintro rfl; simp

end GU.Spinor
