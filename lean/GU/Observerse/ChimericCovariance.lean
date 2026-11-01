/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.OrthoFrames

/-!
# Chart covariance of the chimeric fiber metric

Under a change of chart with Jacobian matrix `P` (invertible), contravariant points transform by
`G ↦ P G Pᵀ` and fiber coordinates by `TP P`. `chimY_covariant` / `Bmod_covariant`: for every
invertible `G`, `Bmod (P G Pᵀ) (TP P u) (TP P v) = Bmod G u v`. So the fiber metric is a
chart-independent geometric object, not just a coordinate formula (review-6 item 2).
-/

namespace GU

open Matrix GU.Observerse GU.Chimeric

theorem chimY_covariant (P G : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) :
    chimY (P * G * Pᵀ) (transportY P x) (transportY P y) = chimY G x y := by
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
  have hinv : (P * G * Pᵀ)⁻¹ = Pᵀ⁻¹ * G⁻¹ * P⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have h1 : P⁻¹ * P = 1 := nonsing_inv_mul _ hPd
  have h2 : Pᵀ * Pᵀ⁻¹ = 1 := mul_nonsing_inv _ hPt
  have key : ∀ A : Matrix (Fin 4) (Fin 4) ℝ,
      Pᵀ⁻¹ * G⁻¹ * P⁻¹ * (P * A * Pᵀ) = Pᵀ⁻¹ * (G⁻¹ * A) * Pᵀ := by
    intro A
    calc Pᵀ⁻¹ * G⁻¹ * P⁻¹ * (P * A * Pᵀ) = Pᵀ⁻¹ * G⁻¹ * (P⁻¹ * P) * A * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have tr_conj : ∀ M : Matrix (Fin 4) (Fin 4) ℝ, trace (Pᵀ⁻¹ * M * Pᵀ) = trace M := by
    intro M; rw [trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [chimY, transportY, hinv]
  have e1 : Pᵀ⁻¹ * G⁻¹ * P⁻¹ * (P * x.1 * Pᵀ) * (Pᵀ⁻¹ * G⁻¹ * P⁻¹) * (P * y.1 * Pᵀ)
      = Pᵀ⁻¹ * (G⁻¹ * x.1 * G⁻¹ * y.1) * Pᵀ := by
    rw [key, Matrix.mul_assoc (Pᵀ⁻¹ * (G⁻¹ * x.1) * Pᵀ), key]
    calc Pᵀ⁻¹ * (G⁻¹ * x.1) * Pᵀ * (Pᵀ⁻¹ * (G⁻¹ * y.1) * Pᵀ)
        = Pᵀ⁻¹ * (G⁻¹ * x.1) * (Pᵀ * Pᵀ⁻¹) * (G⁻¹ * y.1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, tr_conj, key, key, tr_conj, tr_conj]
  congr 1
  rw [mulVec_mulVec, show P * G * Pᵀ * Pᵀ⁻¹ = P * G by rw [Matrix.mul_assoc, h2, Matrix.mul_one],
    ← mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, transpose_nonsing_inv, transpose_transpose,
    vecMul_vecMul, nonsing_inv_mul _ hPd, vecMul_one]

theorem Bmod_covariant (P G : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (u v : CFib) :
    Bmod (P * G * Pᵀ) (TP P hP u) (TP P hP v) = Bmod G u v := by
  have hsym : ∀ w : CFib, (P * symMat w.1 * Pᵀ).IsSymm := fun w => by
    unfold Matrix.IsSymm; rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm _).eq,
      Matrix.mul_assoc]
  have h1 : ∀ w : CFib, (symMat (TP P hP w).1, covec (TP P hP w).2)
      = transportY P (symMat w.1, covec w.2) := fun w => by
    simp only [TP, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, transportY]
    rw [symMat_symCoords _ (hsym w), covec_comp, transpose_nonsing_inv]
  unfold Bmod
  rw [h1, h1, chimY_covariant P G hP]

end GU
