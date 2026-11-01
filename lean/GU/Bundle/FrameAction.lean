/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.FrameRegular

/-!
# The right `O(7,7)`-action on chimeric orthonormal frames (algebra)

`ractM q g = (y, q ∘ g)` (precomposition with the matrix `g` on `ℝ¹⁴`). In matrix form
`homMat⁻¹ (q ∘ g) = (homMat⁻¹ q) · g` (`homMat_symm_comp`), so the Gram matrix transforms as
`gᵀ (qᵀ G q) g` (`bil_mulM`). Hence `O77` preserves the orthonormal frames (`ractM_mem`), acts
freely (`ractM_free`), and transitively on each fibre (`ractM_transitive`); it is a right action
(`ractM_one`, `ractM_mul`). This is the `HomTotM`/matrix-group version of the set-level
`orthoFrameBundle` (group `OG ≃* O77` via `orthOGEquiv`), needed for the smooth structure.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold Matrix

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The matrix `g` as an endomorphism of `ℝ¹⁴`. -/
noncomputable def matCLM (g : Mat 14) : R14 →L[ℝ] R14 :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.of g))

lemma matCLM_apply (g : Mat 14) (x : R14) : matCLM g x = Matrix.of g *ᵥ x := rfl

/-- Right action by matrices on frames. -/
noncomputable def ractM (q : HomTotM X) (g : Mat 14) : HomTotM X :=
  ⟨q.proj, (show HomF from q.2).comp (matCLM g)⟩

lemma homMat_symm_comp (h : HomF) (g : Mat 14) :
    homMat.symm (h.comp (matCLM g)) = mulM (homMat.symm h) g := by
  apply homMat.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ContinuousLinearMap.ext fun x => ?_
  rw [homMat_apply, ContinuousLinearMap.comp_apply, matCLM_apply]
  show _ = ΦL ((Matrix.of (homMat.symm h) * Matrix.of g) *ᵥ x)
  rw [← mulVec_mulVec, ← homMat_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma bil_mulM (G M g : Mat 14) :
    Matrix.of (bil G (mulM M g) (mulM M g)) =
      (Matrix.of g)ᵀ * Matrix.of (bil G M M) * Matrix.of g := by
  rw [bil_eq_mat, bil_eq_mat]
  show (Matrix.of M * Matrix.of g)ᵀ * _ * (Matrix.of M * Matrix.of g) = _
  rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

/-- **`O77` preserves orthonormal frames.** -/
theorem ractM_mem {q : HomTotM X} (hq : q ∈ orthoSetM) (g : O77) : ractM q g ∈ orthoSetM := by
  rw [mem_orthoSetM_iff_mat] at hq ⊢
  show bil (Gchim (((q.proj : Sym2TX X).2 : Fin 10 → ℝ)))
      (homMat.symm ((show HomF from q.2).comp (matCLM g)))
      (homMat.symm ((show HomF from q.2).comp (matCLM g))) = η77
  rw [homMat_symm_comp]
  apply Matrix.of.injective
  rw [bil_mulM]
  have hq' := congrArg Matrix.of hq
  erw [hq']
  exact (mem_Orth_iff_mat _ (ηSig_mem 7 7) _).mp g.2

lemma isUnit_frame {G M : Matrix (Fin 14) (Fin 14) ℝ}
    (h : Mᵀ * G * M = Matrix.of η77) : IsUnit M.det := by
  have hE : (Matrix.of η77).det ≠ 0 := by
    have := congrArg Matrix.det (ηSig_sq 7 7)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [show Matrix.of (ηSig 7 7) = Matrix.of η77 from rfl, h0, zero_mul] at this
    exact zero_ne_one this
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
  refine isUnit_iff_ne_zero.mpr fun h0 => hE ?_
  rw [← this, h0]; ring

/-- **Fibre transitivity**: two orthonormal frames over the same point differ by `O77`. -/
theorem ractM_transitive {q : HomTotM X} (hq : q ∈ orthoSetM) (h' : HomF)
    (hq' : (⟨q.proj, h'⟩ : HomTotM X) ∈ orthoSetM) :
    ∃ g : O77, ractM q g = ⟨q.proj, h'⟩ := by
  rw [mem_orthoSetM_iff_mat] at hq hq'
  set s := (((q.proj : Sym2TX X).2 : Fin 10 → ℝ))
  set M := Matrix.of (homMat.symm (show HomF from q.2))
  set M' := Matrix.of (homMat.symm h')
  set G := Matrix.of (Gchim s)
  set E := Matrix.of η77
  have hM : Mᵀ * G * M = E := by rw [← bil_eq_mat]; exact congrArg Matrix.of hq
  have hM' : M'ᵀ * G * M' = E := by rw [← bil_eq_mat]; exact congrArg Matrix.of hq'
  have hu : IsUnit M.det := isUnit_frame hM
  have hinvR : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have hinvL : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  let g : Mat 14 := Matrix.of.symm (M⁻¹ * M')
  have hgO : g ∈ O77 := by
    rw [mem_Orth_iff_mat]
    show (M⁻¹ * M')ᵀ * E * (M⁻¹ * M') = E
    have hG : (M⁻¹)ᵀ * E * M⁻¹ = G := by
      rw [← hM]
      calc (M⁻¹)ᵀ * (Mᵀ * G * M) * M⁻¹ = (M * M⁻¹)ᵀ * G * (M * M⁻¹) := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = G := by rw [hinvR, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.transpose_mul]
    calc M'ᵀ * (M⁻¹)ᵀ * E * (M⁻¹ * M') = M'ᵀ * ((M⁻¹)ᵀ * E * M⁻¹) * M' := by
          simp only [Matrix.mul_assoc]
      _ = E := by rw [hG, hM']
  refine ⟨⟨g, hgO⟩, ?_⟩
  have hcomp : (show HomF from q.2).comp (matCLM g) = h' := by
    apply homMat.symm.injective
    rw [homMat_symm_comp]
    apply Matrix.of.injective
    show M * (M⁻¹ * M') = M'
    rw [← Matrix.mul_assoc, hinvR, Matrix.one_mul]
  show (⟨q.proj, (show HomF from q.2).comp (matCLM g)⟩ : HomTotM X) = ⟨q.proj, h'⟩
  rw [hcomp]

/-- **Freeness**: only the identity fixes an orthonormal frame. -/
theorem ractM_free {q : HomTotM X} (hq : q ∈ orthoSetM) (g : O77) (hg : ractM q g = q) :
    g = 1 := by
  rw [mem_orthoSetM_iff_mat] at hq
  set M := Matrix.of (homMat.symm (show HomF from q.2))
  have hM : Mᵀ * Matrix.of (Gchim (((q.proj : Sym2TX X).2 : Fin 10 → ℝ))) * M = Matrix.of η77 := by
    rw [← bil_eq_mat]; exact congrArg Matrix.of hq
  have hu : IsUnit M.det := isUnit_frame hM
  have h2 : (show HomF from q.2).comp (matCLM g) = (show HomF from q.2) := by
    have := congrArg (fun r : HomTotM X => (show HomF from r.2)) hg
    exact this
  have h3 : M * Matrix.of (g : Mat 14) = M := by
    have h4 := homMat_symm_comp (show HomF from q.2) g
    rw [h2] at h4
    exact (congrArg Matrix.of h4).symm
  apply Subtype.ext
  apply Matrix.of.injective
  show Matrix.of (g : Mat 14) = 1
  calc Matrix.of (g : Mat 14) = M⁻¹ * (M * Matrix.of (g : Mat 14)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hu, Matrix.one_mul]
    _ = 1 := by rw [h3, Matrix.nonsing_inv_mul M hu]

@[simp] lemma ractM_proj (q : HomTotM X) (g : Mat 14) : (ractM q g).proj = q.proj := rfl

lemma matCLM_one : matCLM (Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)) = ContinuousLinearMap.id ℝ R14 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matCLM_apply]; simp

lemma matCLM_mulM (g g' : Mat 14) : matCLM (mulM g g') = (matCLM g).comp (matCLM g') := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [matCLM_apply, ContinuousLinearMap.comp_apply, matCLM_apply, matCLM_apply]
  show (Matrix.of g * Matrix.of g') *ᵥ x = _
  rw [← mulVec_mulVec]

/-- **Action axioms** (right action): `q · 1 = q`, `(q · g) · g' = q · (g g')`. -/
lemma ractM_one (q : HomTotM X) : ractM q (1 : O77) = q := by
  show (⟨q.proj, (show HomF from q.2).comp (matCLM (Matrix.of.symm 1))⟩ : HomTotM X) = q
  rw [matCLM_one, ContinuousLinearMap.comp_id]

lemma ractM_mul (q : HomTotM X) (g g' : O77) :
    ractM (ractM q g) g' = ractM q (g * g' : O77) := by
  show (⟨q.proj, ((show HomF from q.2).comp (matCLM g)).comp (matCLM g')⟩ : HomTotM X) =
    ⟨q.proj, (show HomF from q.2).comp (matCLM (mulM g g'))⟩
  rw [matCLM_mulM, ContinuousLinearMap.comp_assoc]

end GU.Library
