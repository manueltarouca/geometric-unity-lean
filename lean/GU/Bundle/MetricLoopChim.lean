/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.MetricLoop

/-!
# The endpoint of the metric loop on the chimeric basis (leaf: a slow `simp` over 140 cases)

`TP_chim`: the endpoint rotation `diag(−1,−1,1,1)` acts on the unscaled chimeric basis by the signs
`sgnK`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The endpoint rotation. -/
lemma Rθ_pi : Rθ Real.pi = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rθ, Matrix.diagonal]

/-- Eigenvalues of the endpoint on the unscaled chimeric basis. -/
def sgnK : Fin 14 → ℝ := ![1, -1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1]

lemma TP_chim (k : Fin 14) :
    TP (Rθ Real.pi) (isUnit_Rθ _) (GU.Iso77.toCF (chimVec k)) = sgnK k • GU.Iso77.toCF (chimVec k) := by
  have hinv : (Rθ Real.pi)⁻¹ = Matrix.diagonal ![-1, -1, 1, 1] := by
    rw [Rθ_inv]; ext i j; fin_cases i <;> fin_cases j <;> simp [Rθ, Matrix.diagonal]
  refine Prod.ext ?_ ?_
  · show symCoords (Rθ Real.pi * symMat _ * (Rθ Real.pi)ᵀ) = _
    rw [Rθ_pi]
    funext m
    fin_cases k <;> fin_cases m <;>
      simp [symCoords, symMat, GU.Iso77.toCF, chimVec, chimCoord, sgnK, symIdx, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.diagonal, Pi.single_apply]
  · show (GU.Iso77.dotCLM (chimVec k).1).comp (toCLM (Rθ Real.pi)⁻¹) =
      sgnK k • GU.Iso77.dotCLM (chimVec k).1
    have hc : covec ((GU.Iso77.dotCLM (chimVec k).1).comp (toCLM (Rθ Real.pi)⁻¹)) =
        covec (sgnK k • GU.Iso77.dotCLM (chimVec k).1) := by
      rw [covec_comp, GU.Iso77.covec_dotCLM, hinv]
      have hs : covec (sgnK k • GU.Iso77.dotCLM (chimVec k).1) = sgnK k • (chimVec k).1 := by
        funext m
        have := congrFun (GU.Iso77.covec_dotCLM (chimVec k).1) m
        simp only [covec, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
      rw [hs]
      funext m
      fin_cases k <;> fin_cases m <;>
        simp [chimVec, chimCoord, sgnK, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
          Matrix.diagonal, Pi.single_apply]
    rw [← GU.Iso77.dotCLM_covec ((GU.Iso77.dotCLM (chimVec k).1).comp (toCLM (Rθ Real.pi)⁻¹)), hc,
      GU.Iso77.dotCLM_covec]

end

end GU.Library
