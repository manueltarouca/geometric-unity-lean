/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.FrameBundle
import GU.Observerse.ChimericMetricY

/-!
# Orthonormal frames of the chimeric bundle: an `O(7,7)` reduction over the (1,3) part of `Y`

* `covec p = (p(e₁), …, p(e₄))`, `Bmod G`: the chimeric metric in fiber coordinates at a
  contravariant point `G`; `Bη = Bmod η` is the model (7,7) form on `CFib = ℝ¹⁰ × (ℝ⁴)*`.
* `OG`: the isometry group `O(Bη)`, as a subgroup of `GL(CFib)`.
* `TP P`: the linear isomorphism `(a, p) ↦ (coords(P·a·Pᵀ), p ∘ P⁻¹)`, with
  `Bmod (P η Pᵀ) (TP u) (TP v) = Bη u v` (`TP_isometry`).
* `orthoFrameBundle`: orthonormal frames of `C` over the (1,3) part `Y13` of the global `Y` form a
  principal `O(Bη)`-bundle (set level). `O(Bη) ≅ O(7,7)` since `Bη` has signature (7,7)
  (`chimB_basis`). Frames are stored in fiber coordinates (`C_y` is `CFib` in its chart).

As with `frameBundle`, the set-level statement has the shape `B × G`; its real content is that an
orthonormal frame exists at every (1,3) point (`TP_isometry`). Chart covariance of the metric is
`ChimericCovariance.lean`. The identification `Bη ≅ Q77` is `Φiso_isometry` (`Isometry77.lean`);
orthonormal frames in the smooth frame bundle are closed and exist over (1,3) points
(`SmoothOrtho.lean`, `OrthoGlue.lean`); the sub-bundle (submanifold) structure is not proved.
Still open: the global spin double cover `P̃_Fr(C)`.
-/

namespace GU

open Matrix GU.Observerse GU.Chimeric

/-- Covector components. -/
def covec (p : (Fin 4 → ℝ) →L[ℝ] ℝ) : Fin 4 → ℝ := fun i => p (Pi.single i 1)

/-- Chimeric metric in fiber coordinates at the contravariant point `G`. -/
noncomputable def Bmod (G : Matrix (Fin 4) (Fin 4) ℝ) (u v : CFib) : ℝ :=
  chimY G (symMat u.1, covec u.2) (symMat v.1, covec v.2)

/-- Model (7,7) form. -/
noncomputable def Bη (u v : CFib) : ℝ := Bmod ηR u v

/-- Matrix as a continuous linear map. -/
noncomputable def toCLM (M : Matrix (Fin 4) (Fin 4) ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

lemma toCLM_apply (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : toCLM M v = M *ᵥ v := rfl

lemma covec_comp (p : (Fin 4 → ℝ) →L[ℝ] ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    covec (p.comp (toCLM M)) = Mᵀ *ᵥ covec p := by
  ext i
  simp only [covec, ContinuousLinearMap.comp_apply, toCLM_apply, mulVec, dotProduct, transpose_apply]
  have : M *ᵥ Pi.single i 1 = ∑ j, M j i • Pi.single j (1 : ℝ) := by
    ext k; simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
  rw [this, map_sum]
  simp [map_smul]

/-- The transport isomorphism. -/
noncomputable def TP (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) : CFib ≃ₗ[ℝ] CFib where
  toFun u := (symCoords (P * symMat u.1 * Pᵀ), u.2.comp (toCLM P⁻¹))
  invFun u := (symCoords (P⁻¹ * symMat u.1 * P⁻¹ᵀ), u.2.comp (toCLM P))
  map_add' u v := by
    have hs : symMat (u.1 + v.1) = symMat u.1 + symMat v.1 := by ext i j; simp [symMat]
    ext k <;> simp [hs, Matrix.mul_add, Matrix.add_mul, symCoords]
  map_smul' c u := by
    have hs : symMat (c • u.1) = c • symMat u.1 := by ext i j; simp [symMat]
    ext k <;> simp [hs, symCoords]
  left_inv u := by
    have hd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
    have hsym : (P * symMat u.1 * Pᵀ).IsSymm := by
      unfold Matrix.IsSymm; rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm _).eq,
        Matrix.mul_assoc]
    ext k
    · simp only
      rw [symMat_symCoords _ hsym, transpose_nonsing_inv]
      rw [show P⁻¹ * (P * symMat u.1 * Pᵀ) * Pᵀ⁻¹ = (P⁻¹ * P) * symMat u.1 * (Pᵀ * Pᵀ⁻¹) by
        simp only [Matrix.mul_assoc]]
      rw [nonsing_inv_mul _ hd, mul_nonsing_inv _ (by rwa [det_transpose]), Matrix.one_mul,
        Matrix.mul_one, symCoords_symMat]
    · simp only [ContinuousLinearMap.comp_apply, toCLM_apply, mulVec_mulVec, nonsing_inv_mul _ hd,
        one_mulVec]
  right_inv u := by
    have hd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
    have hsym : (P⁻¹ * symMat u.1 * P⁻¹ᵀ).IsSymm := by
      unfold Matrix.IsSymm; rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm _).eq,
        Matrix.mul_assoc]
    ext k
    · simp only
      rw [symMat_symCoords _ hsym, transpose_nonsing_inv]
      rw [show P * (P⁻¹ * symMat u.1 * Pᵀ⁻¹) * Pᵀ = (P * P⁻¹) * symMat u.1 * (Pᵀ⁻¹ * Pᵀ) by
        simp only [Matrix.mul_assoc]]
      rw [mul_nonsing_inv _ hd, nonsing_inv_mul _ (by rwa [det_transpose]), Matrix.one_mul,
        Matrix.mul_one, symCoords_symMat]
    · simp only [ContinuousLinearMap.comp_apply, toCLM_apply, mulVec_mulVec, mul_nonsing_inv _ hd,
        one_mulVec]

lemma chimY_eta (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) : chimY ηR x y = chimFormR 1 ηR x y := by
  simp [chimY, chimFormR, ηR_inv]

theorem TP_isometry (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (u v : CFib) :
    Bmod (P * ηR * Pᵀ) (TP P hP u) (TP P hP v) = Bη u v := by
  have hsym : ∀ w : CFib, (P * symMat w.1 * Pᵀ).IsSymm := fun w => by
    unfold Matrix.IsSymm; rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm _).eq,
      Matrix.mul_assoc]
  have h1 : ∀ w : CFib, (symMat (TP P hP w).1, covec (TP P hP w).2)
      = transportY P (symMat w.1, covec w.2) := fun w => by
    simp only [TP, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, transportY]
    rw [symMat_symCoords _ (hsym w), covec_comp, transpose_nonsing_inv]
  unfold Bmod Bη
  rw [h1, h1, chimY_transport P hP, Bmod, chimY_eta]

/-- The structure group `O(Bη) ≅ O(7,7)`. -/
def OG : Subgroup GLC where
  carrier := {A | ∀ u v, Bη (A u) (A v) = Bη u v}
  one_mem' u v := rfl
  mul_mem' {A B} hA hB u v := by
    show Bη (A (B u)) (A (B v)) = Bη u v
    rw [hA, hB]
  inv_mem' {A} hA u v := by
    show Bη (A.symm u) (A.symm v) = Bη u v
    rw [← hA, A.apply_symm_apply, A.apply_symm_apply]

open Bundle Manifold MulOpposite
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Contravariant point of `y`. -/
def Gpt (y : Yobs X) : Matrix (Fin 4) (Fin 4) ℝ := symMat ((y : Sym2TX X).2)

/-- The (1,3) part of `Y`. -/
def Y13 (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Type :=
  {y : Yobs X // ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ}

/-- Orthonormal frames: isomorphisms `CFib ≃ C_y` carrying `Bη` to the chimeric metric. -/
def OFrames (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Type :=
  Σ y : Y13 X, {f : CFib ≃ₗ[ℝ] CFib // ∀ u v, Bmod (Gpt y.1) (f u) (f v) = Bη u v}

instance : MulAction (↥OG)ᵐᵒᵖ (OFrames X) where
  smul g f := ⟨f.1, ⟨g.unop.1.trans f.2.1, fun u v => by
    show Bmod (Gpt f.1.1) (f.2.1 (g.unop.1 u)) (f.2.1 (g.unop.1 v)) = Bη u v
    rw [f.2.2, g.unop.2 u v]⟩⟩
  one_smul f := by cases f; rfl
  mul_smul a b f := by cases f; rfl

/-- **Orthonormal frame bundle: a principal `O(7,7)`-bundle over the (1,3) part of `Y`.** -/
noncomputable def orthoFrameBundle : PrincipalBundle (↥OG) (OFrames X) (Y13 X) where
  proj := Sigma.fst
  proj_surjective y := by
    obtain ⟨P, hP, hG⟩ := y.2
    exact ⟨⟨y, ⟨TP P hP, fun u v => by rw [hG]; exact TP_isometry P hP u v⟩⟩, rfl⟩
  proj_smul _ _ := rfl
  free f g h := by
    obtain ⟨y, e, he⟩ := f
    have h2 : g.1.trans e = e := by
      have := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact congrArg Subtype.val this
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply e.injective
    simpa using LinearEquiv.congr_fun h2 v
  transitive f f' h := by
    obtain ⟨y, e, he⟩ := f; obtain ⟨y', e', he'⟩ := f'
    simp only at h; subst h
    refine ⟨⟨e'.trans e.symm, fun u v => ?_⟩, ?_⟩
    · show Bη (e.symm (e' u)) (e.symm (e' v)) = Bη u v
      rw [← he, e.apply_symm_apply, e.apply_symm_apply, he']
    · show (⟨y, ⟨(e'.trans e.symm).trans e, _⟩⟩ : OFrames X) = ⟨y, ⟨e', he'⟩⟩
      congr 2
      exact LinearEquiv.ext fun v => e.apply_symm_apply (e' v)

end GU
