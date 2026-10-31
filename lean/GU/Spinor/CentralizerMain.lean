import GU.Spinor.CZ.R00
import GU.Spinor.CZ.R01
import GU.Spinor.CZ.R02
import GU.Spinor.CZ.R03
import GU.Spinor.CZ.R04
import GU.Spinor.CZ.R05
import GU.Spinor.CZ.R06
import GU.Spinor.CZ.R07
import GU.Spinor.CZ.R08
import GU.Spinor.CZ.R09
import GU.Spinor.CZ.Diag

/-!
# The centraliser of `J` in `span(u32 ∪ u32c)` is exactly `span(u32)` (dimension 25)

Assembled from the row-wise Gram checks in `GU/Spinor/CZ/` (compiled one file at a time).
`centralizer_iff`: `Σ aᵢ u32ᵢ + Σ bⱼ u32cⱼ` commutes with `J` iff `b = 0`. With `u32_linIndep`,
the centraliser within this 45-dimensional space (`= dim so(6,4)`) has dimension exactly 25 =
`dim u(3,2)`. That this 45-dimensional span is all of the bivector algebra follows from the
dimension count; the explicit span equality is not formalised.
-/

namespace GU.Spinor

open Matrix CSum

theorem V_gram_offdiag (i j : Fin 20) (h : i ≠ j) : trPair (V i) (V j) = 0 := by
  fin_cases i
  exacts [Vrow0 j h, Vrow1 j h, Vrow2 j h, Vrow3 j h, Vrow4 j h, Vrow5 j h, Vrow6 j h, Vrow7 j h, Vrow8 j h, Vrow9 j h, Vrow10 j h, Vrow11 j h, Vrow12 j h, Vrow13 j h, Vrow14 j h, Vrow15 j h, Vrow16 j h, Vrow17 j h, Vrow18 j h, Vrow19 j h]

theorem V_linIndep : LinearIndependent ℝ (fun j => toMat (V j)) :=
  linIndep_of_gram _ V_gram_offdiag V_gram_diag

theorem U25_comm (i : Fin 25) : isZero (comm (U25 i) Jc) = true :=
  List.all_eq_true.mp u32_commutes_J _ (List.get_mem _ _)

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
