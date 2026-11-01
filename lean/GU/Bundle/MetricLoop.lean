/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TimeOrientation
import GU.Bundle.AdaptedSection

/-!
# Phase 4, item 4: a loop of Lorentzian metrics in one fibre of `Y13`

`Rθ` rotates the `(0,1)`-plane. Over a point `x ∈ X`, `yLoop x θ` is the point of `Y` with metric
`Rθ ηR Rθᵀ` in the raw coordinates at `x`; `yLoop x π = yLoop x 0`. `qLoop x θ = (yLoop x θ, TP_{Rθ} ∘ Φ)`
is a continuous path of orthonormal frames (`continuous_qLoop`) whose endpoints differ by the holonomy:
`qLoop x π = qLoop x 0 · gHol` (`qLoop_pi`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Rotation in the `(0,1)`-plane. -/
def Rθ (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0, 0; Real.sin θ, Real.cos θ, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

lemma Rθ_mul_neg (θ : ℝ) : Rθ θ * Rθ (-θ) = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rθ, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith

lemma isUnit_Rθ (θ : ℝ) : IsUnit (Rθ θ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one _ (by
    rw [← Matrix.det_mul, Rθ_mul_neg, Matrix.det_one]))

lemma Rθ_inv (θ : ℝ) : (Rθ θ)⁻¹ = Rθ (-θ) := Matrix.inv_eq_right_inv (Rθ_mul_neg θ)

lemma continuous_Rθ : Continuous Rθ := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [Rθ] <;> fun_prop

lemma Rθ_zero : Rθ 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rθ]

/-- The loop of metrics. -/
def Gθ (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Rθ θ * ηR * (Rθ θ)ᵀ

lemma Gθ_symm (θ : ℝ) : (Gθ θ).IsSymm := by
  unfold Matrix.IsSymm Gθ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, Matrix.diagonal]

lemma Gθ_det (θ : ℝ) : (Gθ θ).det < 0 := by
  have hd : (Rθ θ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_Rθ θ)).ne_zero
  have he : (ηR : Matrix (Fin 4) (Fin 4) ℝ).det = -1 := by
    rw [GU.Iso77.ηR_eq]
    simp [ηr, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [Gθ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, he]
  nlinarith [mul_self_pos.mpr hd]

/-- Fibre coordinates of the loop. -/
def sθ (θ : ℝ) : Fin 10 → ℝ := symCoords (Gθ θ)

lemma symMat_sθ (θ : ℝ) : symMat (sθ θ) = Gθ θ := symMat_symCoords _ (Gθ_symm θ)

/-- The point of `Y` at parameter `θ`. -/
def yLoop (x : X) (θ : ℝ) : Yobs X :=
  ⟨⟨x, sθ θ⟩, by
    show (symMat (sθ θ)).det < 0
    rw [symMat_sθ]; exact Gθ_det θ⟩

lemma Gpt_yLoop (x : X) (θ : ℝ) : Gpt (yLoop x θ) = Gθ θ := symMat_sθ θ

lemma continuous_sθ : Continuous sθ := by
  have hG : Continuous Gθ :=
    (continuous_Rθ.matrix_mul continuous_const).matrix_mul continuous_Rθ.matrix_transpose
  refine continuous_pi fun k => ?_
  exact (continuous_apply_apply _ _).comp hG

lemma continuous_yLoop (x : X) : Continuous (yLoop x) :=
  ((FiberBundle.continuous_totalSpaceMk (Fin 10 → ℝ) (symCore (Zt X)).Fiber x).comp
    continuous_sθ).subtype_mk _

/-- Frames `TP_P ∘ Φ` are adapted orthonormal frames. -/
lemma tpFrame_mem (y : Yobs X) (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (hG : Gpt y = P * ηR * Pᵀ) : (⟨y, tpFrame P hP⟩ : HomTotM X) ∈ AFr X := by
  refine ⟨?_, tpFrame_adapted P hP⟩
  show _ ∈ levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩
  rw [levelSet_Fframe]
  intro x x'
  show Bmod (Gpt y) (tpFrame P hP x) (tpFrame P hP x') = _
  rw [hG, tpFrame_apply, tpFrame_apply, TP_isometry, Bη_Φ]

/-- The frame along the loop. -/
def hLoop (θ : ℝ) : HomF := tpFrame (Rθ θ) (isUnit_Rθ θ)

lemma continuous_hLoop : Continuous hLoop := by
  refine continuous_clm_apply.mpr fun v => ?_
  have hT : ∀ u : CFib, Continuous fun θ => TP (Rθ θ) (isUnit_Rθ θ) u := by
    intro u
    refine Continuous.prodMk ?_ ?_
    · have hM : Continuous fun θ => Rθ θ * symMat u.1 * (Rθ θ)ᵀ :=
        (continuous_Rθ.matrix_mul continuous_const).matrix_mul continuous_Rθ.matrix_transpose
      exact continuous_pi fun k => (continuous_apply_apply _ _).comp hM
    · refine continuous_clm_apply.mpr fun w => ?_
      show Continuous fun θ => u.2 ((Rθ θ)⁻¹ *ᵥ w)
      simp only [Rθ_inv]
      have hR : Continuous fun θ : ℝ => Rθ (-θ) := continuous_Rθ.comp continuous_neg
      exact u.2.continuous.comp (hR.matrix_mulVec continuous_const)
  exact hT (ΦL v)

/-- **The frame path.** -/
def qLoop (x : X) (θ : ℝ) : HomTotM X := ⟨yLoop x θ, hLoop θ⟩

lemma qLoop_mem (x : X) (θ : ℝ) : qLoop x θ ∈ AFr X :=
  tpFrame_mem _ _ _ (Gpt_yLoop x θ)

lemma yLoop_mem_baseSet (x : X) (θ θ₀ : ℝ) :
    yLoop x θ ∈ (trivializationAt CFib (Cb (X := X)) (yLoop x θ₀)).baseSet := by
  rw [Cb_baseSet]
  exact (Zt X).mem_baseSet_at x

/-- The `V`-trivialisation is pulled back from `X`. -/
lemma Vb_triv_apply (y0 z : Yobs X) (u : Fin 10 → ℝ) :
    ((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y0) ⟨z, u⟩).2 =
      ((trivializationAt (Fin 10 → ℝ) (symCore (Zt X)).Fiber (πY y0)) ⟨πY z, u⟩).2 := rfl

/-- The `H*`-trivialisation is pulled back from `X`. -/
lemma Hb_triv_apply (y0 z : Yobs X) (u : (Fin 4 → ℝ) →L[ℝ] ℝ) :
    ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ) (Hb (X := X)) y0) ⟨z, u⟩).2 =
      ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ)
        (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ) (πY y0))
        ⟨πY z, u⟩).2 := rfl

lemma Tz_fst' (y0 z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) (u : CFib) :
    (Tz y0 z hz u).1 =
      ((trivializationAt (Fin 10 → ℝ) (symCore (Zt X)).Fiber (πY y0)) ⟨πY z, u.1⟩).2 := by
  show (((trivializationAt CFib (Cb (X := X)) y0).continuousLinearEquivAt ℝ z hz
      (show Cb (X := X) z from u) : CFib)).1 = _
  rw [Trivialization.continuousLinearEquivAt_apply]
  show (((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y0).prod (trivializationAt _ (Hb (X := X)) y0))
    ⟨z, ((u.1 : Vb (X := X) z), (u.2 : Hb (X := X) z))⟩).2.1 = _
  erw [Trivialization.prod_apply]
  exact Vb_triv_apply y0 z u.1

lemma Tz_snd' (y0 z : Yobs X) (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y0).baseSet) (u : CFib) :
    (Tz y0 z hz u).2 =
      ((trivializationAt ((Fin 4 → ℝ) →L[ℝ] ℝ)
        (fun x : X => TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ)) x →L[ℝ] ℝ) (πY y0))
        ⟨πY z, u.2⟩).2 := by
  show (((trivializationAt CFib (Cb (X := X)) y0).continuousLinearEquivAt ℝ z hz
      (show Cb (X := X) z from u) : CFib)).2 = _
  rw [Trivialization.continuousLinearEquivAt_apply]
  show (((trivializationAt (Fin 10 → ℝ) (Vb (X := X)) y0).prod (trivializationAt _ (Hb (X := X)) y0))
    ⟨z, ((u.1 : Vb (X := X) z), (u.2 : Hb (X := X) z))⟩).2.2 = _
  erw [Trivialization.prod_apply]
  exact Hb_triv_apply y0 z u.2

/-- The trivialisation of `C` does not depend on the point of the fibre over `x`. -/
lemma Tz_yLoop (x : X) (θ θ₀ θ₁ : ℝ) (u : CFib) :
    Tz (yLoop x θ₀) (yLoop x θ) (yLoop_mem_baseSet x θ θ₀) u =
      Tz (yLoop x θ₀) (yLoop x θ₁) (yLoop_mem_baseSet x θ₁ θ₀) u :=
  Prod.ext ((Tz_fst' _ _ (yLoop_mem_baseSet x θ θ₀) u).trans
      (Tz_fst' _ _ (yLoop_mem_baseSet x θ₁ θ₀) u).symm)
    ((Tz_snd' _ _ (yLoop_mem_baseSet x θ θ₀) u).trans
      (Tz_snd' _ _ (yLoop_mem_baseSet x θ₁ θ₀) u).symm)

/-- **The frame path is continuous.** -/
theorem continuous_qLoop (x : X) : Continuous (qLoop x) := by
  refine continuous_iff_continuousAt.mpr fun θ₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_yLoop x).continuousAt, ?_⟩
  set T := Tz (yLoop x θ₀) (yLoop x θ₀) (yLoop_mem_baseSet x θ₀ θ₀)
  have hform : (fun θ => ((trivializationAt HomF (HomCb (X := X)) (yLoop x θ₀)) (qLoop x θ)).2) =
      fun θ => (T : CFib →L[ℝ] CFib).comp (hLoop θ) := by
    funext θ
    rw [triv_apply (yLoop x θ₀) (qLoop x θ) (yLoop_mem_baseSet x θ θ₀)]
    refine ContinuousLinearMap.ext fun v => ?_
    exact Tz_yLoop x θ θ₀ θ₀ (hLoop θ v)
  show ContinuousAt (fun θ => ((trivializationAt HomF (HomCb (X := X)) (yLoop x θ₀)) (qLoop x θ)).2) θ₀
  rw [hform]
  exact (continuous_const.clm_comp continuous_hLoop).continuousAt

end

end GU.Library
