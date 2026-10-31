import GU.Bundle.ChimFrames
import GU.Library.RegularValue

/-!
# L4e (i)–(ii): the orthonormal frame bundle as a level set in `HomTotM`

(i) The charted-space model of `HomTotM X` is `ModelProd (ModelProd ℝ⁴ ℝ¹⁰) HomF`; we give it the
product normed structure and transfer `IsManifold` to `𝓘(ℝ, ModelProd …)`.
(ii) `Fframe q = sym(qᵀ Gchim(s) q)` (matrix form, `s` the fibre coordinate of the base point)
has `levelSet Fframe η₇₇ = orthoSetM` (`levelSet_Fframe`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- The model space of `HomTotM`. -/
abbrev HomModel := ModelProd (ModelProd (Fin 4 → ℝ) (Fin 10 → ℝ)) HomF

noncomputable instance : NormedAddCommGroup HomModel :=
  inferInstanceAs (NormedAddCommGroup (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF))
noncomputable instance : NormedSpace ℝ HomModel :=
  inferInstanceAs (NormedSpace ℝ (((Fin 4 → ℝ) × (Fin 10 → ℝ)) × HomF))
instance finDim_HomF : FiniteDimensional ℝ HomF :=
  LinearEquiv.finiteDimensional homMat.toLinearEquiv

instance : FiniteDimensional ℝ HomModel :=
  Module.Finite.prod (R := ℝ) (M := (Fin 4 → ℝ) × (Fin 10 → ℝ)) (N := HomF)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **`HomTotM` is a smooth manifold over the self-model** `𝓘(ℝ, HomModel)`. -/
instance homTot_isManifold : IsManifold 𝓘(ℝ, HomModel) ∞ (HomTotM X) := by
  have h : IsManifold (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
      (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod (modelWithCornersSelf ℝ HomF)) ∞ (HomTotM X) :=
    inferInstance
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  have hc := (HasGroupoid.compatible (G := contDiffGroupoid ∞ (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
      (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod (modelWithCornersSelf ℝ HomF))) he he').1
  simpa [contDiffPregroupoid, Function.comp_def] using hc

/-- The frame map `HomTotM → Sym(14)`. -/
noncomputable def Fframe (q : HomTotM X) : symS 14 :=
  orthF (Gchim ((q.proj : Sym2TX X).2)) (homMat.symm q.2)

/-- **`orthoSetM` is the level set `Fframe⁻¹{η₇₇}`.** -/
theorem levelSet_Fframe :
    levelSet (Fframe (X := X)) ⟨η77, ηSig_mem 7 7⟩ = orthoSetM := by
  ext q
  rw [mem_orthoSetM_iff_mat]
  show orthF _ _ = _ ↔ _
  constructor
  · intro h; exact bil_of_orthF_eq (Gchim_mem _) (ηSig_mem 7 7) h
  · intro h
    apply Subtype.ext
    show (symP 14 (bil _ _ _) : Mat 14) = η77
    rw [symP_of_mem (bil_mem (Gchim ((q.proj : Sym2TX X).2)) (Gchim_mem _) (homMat.symm q.2)), h]

end GU.Library
