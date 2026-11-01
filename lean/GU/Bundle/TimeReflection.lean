import GU.Bundle.TimeCoverSpin

/-!
# Phase 5, item 5, general `X`: a partial result on orientability

Over the cover, the only part of a chart change that could obstruct an `SO₀`-reduction for a general `X`
is a time-preserving Lorentz transformation. Reversing the orientation of `X` in a chart acts on a
Lorentz frame through `rR = diag(1, −1, 1, 1)`, which preserves time.

**`TP_rR`**: `rR` acts on the frames of `C` by the diagonal element `gRefl` of `O(7,7)`, and
**`tdet_gRefl`**, **`det_gRefl`**: both of its block determinants are positive (`tdet_gRefl`, `ndet_gRefl`; also `det_gRefl`).
Contrast `gHol`, the time-reversing holonomy, where `tdet = −1` (`tdet_gHol`).

So reflection does not reverse the orientation of the positive part of `C`, and orientability of `X`
is expected not to be needed (informal; see the log). Not formalised: the general-`X` reduction, the
chart transition of frames, that `gRefl ∈ SO₀`, that every time-preserving Lorentz transformation
has positive block determinants, and that the identity component of `O(1,3)` maps into `SO₀` (by
connectedness and continuity of `TP`).
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The reflection of the axis `1`. -/
def rR : M4 := Matrix.diagonal ![1, -1, 1, 1]

lemma rR_mul_self : rR * rR = 1 := by
  rw [rR, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; fin_cases i <;> simp

lemma isUnit_rR : IsUnit rR := IsUnit.of_mul_eq_one _ rR_mul_self

lemma rR_inv : rR⁻¹ = rR := Matrix.inv_eq_right_inv rR_mul_self

/-- `rR` preserves `ηR`: it is a Lorentz transformation. -/
lemma rR_eta : rR * ηR * rRᵀ = ηR := by
  rw [GU.Iso77.ηR_eq, ηr, rR, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext i; fin_cases i <;> simp

/-- Eigenvalues of `rR` on the unscaled chimeric basis. -/
def sgnR : Fin 14 → ℝ := ![-1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1]

lemma TP_rR_chim (k : Fin 14) :
    TP rR isUnit_rR (GU.Iso77.toCF (chimVec k)) = sgnR k • GU.Iso77.toCF (chimVec k) := by
  refine Prod.ext ?_ ?_
  · show symCoords (rR * symMat _ * rRᵀ) = _
    funext m
    fin_cases k <;> fin_cases m <;>
      simp [symCoords, symMat, GU.Iso77.toCF, chimVec, chimCoord, sgnR, symIdx, rR, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.diagonal, Pi.single_apply]
  · show (GU.Iso77.dotCLM (chimVec k).1).comp (toCLM rR⁻¹) = sgnR k • GU.Iso77.dotCLM (chimVec k).1
    have hc : covec ((GU.Iso77.dotCLM (chimVec k).1).comp (toCLM rR⁻¹)) =
        covec (sgnR k • GU.Iso77.dotCLM (chimVec k).1) := by
      rw [covec_comp, GU.Iso77.covec_dotCLM, rR_inv]
      have hs : covec (sgnR k • GU.Iso77.dotCLM (chimVec k).1) = sgnR k • (chimVec k).1 := by
        funext m
        have := congrFun (GU.Iso77.covec_dotCLM (chimVec k).1) m
        simp only [covec, _root_.smul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
      rw [hs]
      funext m
      fin_cases k <;> fin_cases m <;>
        simp [chimVec, chimCoord, sgnR, rR, Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
    rw [← GU.Iso77.dotCLM_covec ((GU.Iso77.dotCLM (chimVec k).1).comp (toCLM rR⁻¹)), hc,
      GU.Iso77.dotCLM_covec]

/-- The diagonal of the element of `O(7,7)` given by `rR`. -/
def dRefl : Fin 14 → ℝ := ![-1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1]

lemma dRefl_eq (i : Fin 14) : dRefl i = sgnR (GU.Iso77.σl i) := by
  fin_cases i <;> simp [dRefl, sgnR, GU.Iso77.σl]

/-- The matrix of the reflection on frames. -/
def gReflM : Mat 14 := Matrix.of.symm (Matrix.diagonal dRefl)

lemma gReflM_mem : gReflM ∈ O77 := by
  rw [mem_Orth_iff_mat]
  show (Matrix.diagonal dRefl)ᵀ * Matrix.of η77 * Matrix.diagonal dRefl = Matrix.of η77
  have : Matrix.of η77 = Matrix.diagonal fun i : Fin 14 => if (i : ℕ) < 7 then (1 : ℝ) else -1 := rfl
  rw [this, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  have h : dRefl i * dRefl i = 1 := by fin_cases i <;> simp [dRefl]
  calc dRefl i * _ * dRefl i = (dRefl i * dRefl i) * (if (i : ℕ) < 7 then (1 : ℝ) else -1) := by ring
    _ = _ := by rw [h, one_mul]

/-- **The reflection on frames.** -/
def gRefl : O77 := ⟨gReflM, gReflM_mem⟩

/-- **`rR` acts on the frames of `C` by `gRefl`.** -/
theorem TP_rR (v : Fin 14 → ℝ) : TP rR isUnit_rR (ΦL v) = ΦL (matCLM gReflM v) := by
  have hb : ∀ i : Fin 14, TP rR isUnit_rR (ΦL (Pi.single i 1)) =
      ΦL (matCLM gReflM (Pi.single i 1)) := by
    intro i
    have e : matCLM gReflM (Pi.single i 1) = dRefl i • (Pi.single i 1 : Fin 14 → ℝ) := by
      show (Matrix.diagonal dRefl) *ᵥ Pi.single i 1 = _
      rw [Matrix.mulVec_single_one]
      ext k; by_cases h : k = i
      · subst h; simp
      · simp [h]
    rw [e, map_smul, ΦL_single, map_smul, TP_rR_chim, dRefl_eq, smul_comm]
  have hsum : v = ∑ k, v k • (Pi.single k 1 : Fin 14 → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  simp only [map_sum, map_smul, hb]

/-- **The reflection preserves the orientation of the positive part of `C`.** -/
theorem tdet_gRefl : tdet (gRefl : Mat 14) = 1 := by
  have : posBlock (gRefl : Mat 14) = Matrix.diagonal fun a : Fin 7 => dRefl (Fin.castAdd 7 a) := by
    ext a b
    show (Matrix.diagonal dRefl) (Fin.castAdd 7 a) (Fin.castAdd 7 b) = _
    by_cases h : a = b
    · subst h; simp
    · have h' : (Fin.castAdd 7 a : Fin (7 + 7)) ≠ Fin.castAdd 7 b := fun e => h (Fin.castAdd_injective _ _ e)
      rw [Matrix.diagonal_apply_ne _ h', Matrix.diagonal_apply_ne _ h]
  unfold tdet
  rw [this, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, dRefl, Fin.castAdd]

/-- **The negative block of the reflection has determinant one.** -/
theorem ndet_gRefl :
    (Matrix.of fun a b : Fin 7 => (gRefl : Mat 14) (Fin.natAdd 7 a) (Fin.natAdd 7 b)).det = 1 := by
  have : (Matrix.of fun a b : Fin 7 => (gRefl : Mat 14) (Fin.natAdd 7 a) (Fin.natAdd 7 b)) =
      Matrix.diagonal fun a : Fin 7 => dRefl (Fin.natAdd 7 a) := by
    ext a b
    show (Matrix.diagonal dRefl) (Fin.natAdd 7 a) (Fin.natAdd 7 b) = _
    by_cases h : a = b
    · subst h; simp
    · have h' : (Fin.natAdd 7 a : Fin (7 + 7)) ≠ Fin.natAdd 7 b := fun e => h (Fin.natAdd_injective _ _ e)
      rw [Matrix.diagonal_apply_ne _ h', Matrix.diagonal_apply_ne _ h]
  rw [this, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, dRefl, Fin.natAdd]

/-- **The reflection has determinant one**, so it preserves both orientations. -/
theorem det_gRefl : (Matrix.of (gRefl : Mat 14)).det = 1 := by
  show (Matrix.diagonal dRefl).det = 1
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, dRefl]

end

end GU.Library
