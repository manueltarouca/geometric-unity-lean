/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.TimeGaugeLargest
import GU.Bundle.SmoothSpin

/-!
# Phase 5, item 1: the reduction-level obstruction

**`no_SO0_reduction_univ`**: for nonempty `X` there is no clopen `SO₀`-reduction of `OFr` over all of
`Y13`: no clopen subset that is `SO₀`-stable and meets every fibre in exactly one `SO₀`-coset. This
statement involves no spin group. Stability is not used in the proof, so the theorem is stronger than
stated; it is kept to match the definition of a reduction. Clopenness is the only regularity assumed.
Informally, a locally trivial reduction is clopen because `SO₀` is clopen in `O77`; this implication is
not formalised for general reductions, only for the image of a spin structure below.

**Not vacuous**: the hypotheses hold over a smaller base. `reduction_of_spinLiftData` shows that the
image of `Φ` of any `SpinLiftData` is open, relatively closed over `W`, stable, and one coset per fibre
of `W`, and `exists_reduction_timeGaugeLocus` gives such a set over the nonempty locus `{G₀₀ > 0}` of
`Y13(ℝ⁴)`. `no_spinLiftData_of_univ` recovers the spin statement from the reduction statement.

Also: **`no_spinStructure_of_neg_fibre`** (over `ℝ⁴`, a spin structure cannot have a base containing
all of `{G₀₀ < 0}` in a fibre), `timeGaugeLocus_nonempty`, and **`det_gHol`** (`det gHol = 1`, while
`gHol ∉ SO₀`; "`gHol ∈ SO(7,7)`" is informal notation, since the repo defines no `SO(7,7)`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **The holonomy has determinant one.** -/
theorem det_gHol : (Matrix.of (gHol : Mat 14)).det = 1 := by
  show (Matrix.diagonal dHol).det = 1
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, dHol]

/-- **There is no clopen `SO₀`-reduction of the frame bundle over all of `Y13`.** -/
theorem no_SO0_reduction_univ (Q : Set (OFr X)) (hQ : IsClopen Q)
    (_hstable : ∀ q ∈ Q, ∀ g ∈ SO0, actOFr' q g ∈ Q)
    (hmeet : ∀ y : Y13o X, ∃ q ∈ Q, projOFr q = y)
    (hcoset : ∀ q ∈ Q, ∀ q' ∈ Q, projOFr q = projOFr q' → ∃ g ∈ SO0, actOFr' q g = q')
    (x : X) : False := by
  obtain ⟨r, hrQ, hr⟩ := hmeet (projOFr (pLoop x 0))
  obtain ⟨h, hh⟩ := exists_act_eq (pLoop x 0) r hr.symm
  have hf : Continuous fun θ => actOFr' (pLoop x θ) h :=
    continuous_actOFr'.comp ((continuous_pLoop x).prodMk continuous_const)
  have hcl := hQ.preimage hf
  have huniv := hcl.eq_univ ⟨0, by show actOFr' (pLoop x 0) h ∈ Q; rw [hh]; exact hrQ⟩
  have hpi : actOFr' (pLoop x Real.pi) h ∈ Q := by
    have : Real.pi ∈ (fun θ => actOFr' (pLoop x θ) h) ⁻¹' Q := by rw [huniv]; exact Set.mem_univ _
    exact this
  have hact : actOFr' (pLoop x Real.pi) h = actOFr' r (h⁻¹ * gHol * h) := by
    rw [pLoop_pi, ← hh, actOFr'_mul, actOFr'_mul]
    congr 1; group
  rw [hact] at hpi
  obtain ⟨g, hg, hge⟩ := hcoset r hrQ _ hpi (projOFr_act r _).symm
  have : g = h⁻¹ * gHol * h := actOFr'_cancel hge
  exact gHol_not_mem_SO0 (conj_mem_SO0 h (this ▸ hg))

/-- **Non-vacuity.** The image of `Φ` satisfies every hypothesis of `no_SO0_reduction_univ` relative
to the base `W`: it is open, relatively closed over `W`, lies over `W`, is stable, meets every fibre of
`W`, and is one `SO₀`-coset per fibre. -/
theorem reduction_of_spinLiftData (D : SpinLiftData X) :
    IsOpen (Set.range D.Φ) ∧
    (∀ q, q ∉ Set.range D.Φ → projOFr q ∈ D.W →
      ∃ N : Set (OFr X), IsOpen N ∧ q ∈ N ∧ Disjoint N (Set.range D.Φ)) ∧
    (∀ q ∈ Set.range D.Φ, projOFr q ∈ D.W) ∧
    (∀ q ∈ Set.range D.Φ, ∀ g ∈ SO0, actOFr' q g ∈ Set.range D.Φ) ∧
    (∀ y ∈ D.W, ∃ q ∈ Set.range D.Φ, projOFr q = y) ∧
    (∀ q ∈ Set.range D.Φ, ∀ q' ∈ Set.range D.Φ, projOFr q = projOFr q' →
      ∃ g ∈ SO0, actOFr' q g = q') := by
  refine ⟨D.isOpen_range_Φ, fun q hq hW => D.exists_nhds_disjoint hq hW, ?_,
    fun q hq g hg => D.range_Φ_act_mem hq hg, fun y hy => ?_,
    fun q hq q' hq' h => D.range_Φ_transitive hq hq' h⟩
  · rintro q ⟨p, rfl⟩
    rw [D.proj_Φ]
    exact p.proj.2
  · obtain ⟨i, hi⟩ := D.cover y hy
    exact ⟨_, D.σ_mem_range i hi, D.proj_σ i y hi⟩

/-- Over all of `Y13` the image of `Φ` would be clopen. -/
lemma isClopen_range_Φ (D : SpinLiftData X) (hW : D.W = Set.univ) : IsClopen (Set.range D.Φ) := by
  refine ⟨?_, D.isOpen_range_Φ⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨N, hN, hqN, hd⟩ := D.exists_nhds_disjoint (q := q) hq (by rw [hW]; exact Set.mem_univ _)
  exact ⟨N, fun r hr hrQ => Set.disjoint_left.mp hd hr hrQ, hN, hqN⟩

/-- The spin statement follows from the reduction statement. -/
theorem no_spinLiftData_of_univ (D : SpinLiftData X) (hW : D.W = Set.univ) (x : X) : False := by
  obtain ⟨-, -, -, hst, hm, hc⟩ := reduction_of_spinLiftData D
  exact no_SO0_reduction_univ _ (isClopen_range_Φ D hW) hst
    (fun y => hm y (by rw [hW]; exact Set.mem_univ _)) hc x

/-- The swap of the axes `0` and `2`. -/
def Qswap : M4 := !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

lemma Qswap_sq : Qswap * Qswap = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qswap, Matrix.mul_apply, Fin.sum_univ_four]

lemma isUnit_Qswap : IsUnit Qswap := IsUnit.of_mul_eq_one _ Qswap_sq

lemma G00_yQ_swap (x : R4) (θ : ℝ) : Gpt (yQ x Qswap isUnit_Qswap θ : Yobs R4) 0 0 = -1 := by
  have hrow : ∀ j, (Qswap * Rθ θ) 0 j = if j = 2 then 1 else 0 := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases j <;> simp [Qswap, Rθ]
  show Gpt (mkY x _ _ : Yobs R4) 0 0 = -1
  rw [Gpt_mkY, GU.Iso77.ηR_eq, ηr, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, hrow]
  simp

/-- **A spin structure over `ℝ⁴` cannot contain all of `{G₀₀ < 0}` in a fibre.** -/
theorem no_spinStructure_of_neg_fibre (S : SpinStructure R4) (x : R4)
    (hW : ∀ y : Y13o R4, ((y : Yobs R4) : Sym2TX R4).proj = x → Gpt (y : Yobs R4) 0 0 < 0 → y ∈ S.W) :
    False := by
  refine no_spinLiftData_of_path S.toData (p := pQ x Qswap isUnit_Qswap)
    ((continuous_qQ x Qswap isUnit_Qswap).subtype_mk _) (fun θ => ?_) (pQ_pi x Qswap isUnit_Qswap)
  refine hW (yQ x Qswap isUnit_Qswap θ) rfl ?_
  rw [G00_yQ_swap]; norm_num

/-- **The time-gauge locus is nonempty.** -/
theorem timeGaugeLocus_nonempty : timeGaugeLocus.Nonempty := by
  refine ⟨mkY 0 1 isUnit_one, ?_⟩
  show 0 < Gpt (mkY 0 1 isUnit_one : Yobs R4) 0 0
  rw [Gpt_mkY, GU.Iso77.ηR_eq, ηr]
  simp

/-- **Non-vacuity, concretely.** Over the nonempty locus `{G₀₀ > 0}` of `Y13(ℝ⁴)` the hypotheses of
`no_SO0_reduction_univ` hold, relative to that locus. -/
theorem exists_reduction_timeGaugeLocus :
    ∃ Q : Set (OFr R4), IsOpen Q ∧
      (∀ q, q ∉ Q → projOFr q ∈ timeGaugeLocus →
        ∃ N : Set (OFr R4), IsOpen N ∧ q ∈ N ∧ Disjoint N Q) ∧
      (∀ q ∈ Q, projOFr q ∈ timeGaugeLocus) ∧
      (∀ q ∈ Q, ∀ g ∈ SO0, actOFr' q g ∈ Q) ∧
      (∀ y ∈ timeGaugeLocus, ∃ q ∈ Q, projOFr q = y) ∧
      (∀ q ∈ Q, ∀ q' ∈ Q, projOFr q = projOFr q' → ∃ g ∈ SO0, actOFr' q g = q') := by
  obtain ⟨D, hD⟩ := exists_spinLiftData_R4
  have hD' : D.W = timeGaugeLocus := hD
  refine ⟨Set.range D.Φ, ?_⟩
  simpa only [hD'] using reduction_of_spinLiftData D

end

end GU.Library
