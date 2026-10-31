import GU.Bundle.AdaptedFrames

/-!
# Phase 3, item 1: the inverse of the local trivialisation is smooth

In chart coordinates the inverse of `Ψ(e, g) = σ(e)·g` is `q ↦ ((c q).1, Mσ(e)⁻¹ · Mq)`, with
`Mq = homMat⁻¹ (c q).2` and `Mσ(e) = homMat⁻¹ (c (σ e)).2`. Smoothness follows from: `homMat⁻¹`
is linear (`contDiff_homMat_symm`, entrywise), matrix inversion is smooth where `det ≠ 0`
(`EntCDn.inv`), and the chart and `σ` are smooth.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- Entries of `homMat⁻¹ h`. -/
lemma homMat_symm_apply (h : HomF) (i j : Fin 14) :
    homMat.symm h i j = (ΦL.symm (h (Pi.single j 1))) i := by
  have hq := homMat_apply (homMat.symm h) (Pi.single j 1)
  rw [ContinuousLinearEquiv.apply_symm_apply, mulVec_single_one] at hq
  rw [hq, ContinuousLinearEquiv.symm_apply_apply]; rfl

/-- **`homMat⁻¹` is smooth** (entrywise: evaluation, `Φ⁻¹`, coordinate). -/
lemma contDiff_homMat_symm : ContDiff ℝ ∞ (fun h : HomF => homMat.symm h) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp_rw [homMat_symm_apply]
  have hev : ContDiff ℝ ∞ (fun h : HomF => h (Pi.single j 1)) :=
    contDiff_id.clm_apply contDiff_const
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 14 => ℝ) i).contDiff.comp
    ((ΦL.symm : CFib →L[ℝ] R14).contDiff.comp hev))

end GU.Library
