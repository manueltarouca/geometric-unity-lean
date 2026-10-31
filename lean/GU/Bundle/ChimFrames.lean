import GU.Bundle.ChimGram

/-!
# L4e step 2: frames as matrices, `Mat 14 ≃L HomF`

`homMat q = Φ ∘ q` identifies a `14 × 14` matrix with a frame `ℝ¹⁴ →L CFib` of the hom bundle
(`HomF`, the fibre of `HomTotM`). Under it, the `orthoSetM` condition at a point with metric
`symMat s` is the matrix condition of `isManifold_chimFrames` (`orthoM_cond_iff`).
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Chimeric

/-- **`Mat 14 ≃L HomF`**, `q ↦ Φ ∘ q`. -/
noncomputable def homMat : Mat 14 ≃L[ℝ] HomF :=
  (((LinearEquiv.refl ℝ (Matrix (Fin 14) (Fin 14) ℝ)).trans Matrix.toLin').trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ R14).arrowCongr ΦL)

lemma homMat_apply (q : Mat 14) (x : R14) : homMat q x = ΦL (Matrix.of q *ᵥ x) := rfl

/-- **The `orthoSetM` condition is the matrix condition.** At a point whose metric is `symMat s`,
a frame `h : HomF` is `Q77`-orthonormal iff `qᵀ Gchim(s) q = η₇₇` for `q = homMat⁻¹ h`. -/
theorem orthoM_cond_iff (s : Fin 10 → ℝ) (h : HomF) :
    (∀ x x' : R14, Bmod (symMat s) (h x) (h x') = QuadraticMap.polar Q77 x x' / 2) ↔
      bil (Gchim s) (homMat.symm h) (homMat.symm h) = η77 := by
  rw [bil_Gchim_iff]
  have hq : ∀ x, ΦL (Matrix.of (homMat.symm h) *ᵥ x) = h x := fun x => by
    rw [← homMat_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [hq, Bm_eq_polar]

section Global

open Bundle
open scoped ContDiff

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **`orthoSetM` in matrix form**: a frame `q` over `y` is orthonormal iff its matrix satisfies
`qᵀ Gchim(s) q = η₇₇` at the fibre coordinate `s = y.2` (with `Gpt y = symMat s`). -/
theorem mem_orthoSetM_iff_mat (q : HomTotM X) :
    q ∈ orthoSetM ↔
      bil (Gchim ((q.proj : Sym2TX X).2)) (homMat.symm q.2) (homMat.symm q.2) = η77 :=
  orthoM_cond_iff _ q.2

end Global

end GU.Library
