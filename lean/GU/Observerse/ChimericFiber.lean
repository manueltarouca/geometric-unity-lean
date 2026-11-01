/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Observerse.Chimeric

/-!
# The chimeric metric has signature (7,7) at *every* Lorentzian point of type (1,3)

For `g = Pᵀ η P` (`P` invertible), the chimeric form at `g` is
`F_g((A,p),(B,q)) = tr(g⁻¹Ag⁻¹B) − λ tr(g⁻¹A)tr(g⁻¹B) + pᵀ g⁻¹ q`.
The map `Φ_P(A, p) = (PᵀAP, Pᵀp)` is an isometry `C_η → C_g` (`chimForm_transport`), so the
explicit orthogonal basis at `η` (`GU.Chimeric.chimBasis_gram`) is carried to an orthogonal
basis at `g` with the same norms: 7 positive and 7 negative (`chim_signature_everywhere`).
-/

namespace GU.Chimeric

open Matrix

variable (lam : ℝ)

/-- Chimeric form at a point with inverse metric `gi`. -/
def chimFormR (gi : Matrix (Fin 4) (Fin 4) ℝ) (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) : ℝ :=
  trace (gi * x.1 * gi * y.1) - lam * trace (gi * x.1) * trace (gi * y.1) + x.2 ⬝ᵥ (gi *ᵥ y.2)

/-- Transport `C_η → C_g` for `g = Pᵀ η P`. -/
def transport (P : Matrix (Fin 4) (Fin 4) ℝ) (x : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) :
    Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ) :=
  (Pᵀ * x.1 * P, Pᵀ *ᵥ x.2)

/-- `ηR` over the reals. -/
def ηR : Matrix (Fin 4) (Fin 4) ℝ := ηZ.map (Int.castRingHom ℝ)

theorem chimForm_transport (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) :
    chimFormR lam (P⁻¹ * ηR * Pᵀ⁻¹) (transport P x) (transport P y) = chimFormR lam ηR x y := by
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
  have h1 : Pᵀ⁻¹ * Pᵀ = 1 := nonsing_inv_mul _ hPt
  have h2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hPd
  -- g⁻¹ (PᵀAP) = P⁻¹ (η A) P
  have key : ∀ A : Matrix (Fin 4) (Fin 4) ℝ,
      P⁻¹ * ηR * Pᵀ⁻¹ * (Pᵀ * A * P) = P⁻¹ * (ηR * A) * P := by
    intro A
    calc P⁻¹ * ηR * Pᵀ⁻¹ * (Pᵀ * A * P) = P⁻¹ * ηR * (Pᵀ⁻¹ * Pᵀ) * A * P := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (ηR * A) * P := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [chimFormR, transport]
  have e1 : P⁻¹ * ηR * Pᵀ⁻¹ * (Pᵀ * x.1 * P) * (P⁻¹ * ηR * Pᵀ⁻¹) * (Pᵀ * y.1 * P)
      = P⁻¹ * (ηR * x.1 * ηR * y.1) * P := by
    rw [key, Matrix.mul_assoc (P⁻¹ * (ηR * x.1) * P), key]
    calc P⁻¹ * (ηR * x.1) * P * (P⁻¹ * (ηR * y.1) * P)
        = P⁻¹ * (ηR * x.1) * (P * P⁻¹) * (ηR * y.1) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have tr_conj : ∀ M : Matrix (Fin 4) (Fin 4) ℝ, trace (P⁻¹ * M * P) = trace M := by
    intro M; rw [trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [e1, tr_conj, key, key, tr_conj, tr_conj]
  congr 1
  have hv : (P⁻¹ * ηR * Pᵀ⁻¹) *ᵥ (Pᵀ *ᵥ y.2) = P⁻¹ *ᵥ (ηR *ᵥ y.2) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hx : Pᵀ *ᵥ x.2 = x.2 ᵥ* P := by rw [← vecMul_transpose, transpose_transpose]
  rw [hv, hx, ← dotProduct_mulVec, mulVec_mulVec, h2, one_mulVec]

lemma chimFormR_cast (x y : Cvec) :
    chimFormR 1 ηR (x.1.map (Int.castRingHom ℝ), fun k => (x.2 k : ℝ))
      (y.1.map (Int.castRingHom ℝ), fun k => (y.2 k : ℝ)) = ((chimForm 1 x y : ℤ) : ℝ) := by
  have hm : ∀ M N : Matrix (Fin 4) (Fin 4) ℤ,
      M.map (Int.castRingHom ℝ) * N.map (Int.castRingHom ℝ) = (M * N).map (Int.castRingHom ℝ) :=
    fun M N => (Matrix.map_mul).symm
  have ht : ∀ M : Matrix (Fin 4) (Fin 4) ℤ, trace (M.map (Int.castRingHom ℝ)) = ((trace M : ℤ) : ℝ) := by
    intro M; simp [trace, Fin.sum_univ_four]
  simp only [chimFormR, chimForm, deWittZ, ηR, hm, ht]
  push_cast
  congr 1
  simp [dotProduct, mulVec, ηZ, Fin.sum_univ_four, diagonal]

/-- The transported basis is orthogonal at `g = PᵀηP` with the norms of `chimNorms`
(at `λ = 1`): the chimeric metric has signature (7,7) at every (1,3) point. -/
theorem chim_signature_everywhere (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (i j : Fin 14) :
    chimFormR 1 (P⁻¹ * ηR * Pᵀ⁻¹)
        (transport P ((chimBasis i).1.map (Int.castRingHom ℝ), fun k => ((chimBasis i).2 k : ℝ)))
        (transport P ((chimBasis j).1.map (Int.castRingHom ℝ), fun k => ((chimBasis j).2 k : ℝ)))
      = if i = j then (chimNorms i : ℝ) else 0 := by
  rw [chimForm_transport 1 P hP, chimFormR_cast, chimBasis_gram]
  split_ifs <;> simp

end GU.Chimeric
