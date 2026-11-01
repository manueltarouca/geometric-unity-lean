/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinTop
import GU.Spinor.SpinKernel

/-!
# `Spin(7,7)` is closed in `Cl(7,7)`

Mathlib's `spinGroup` is built from the *generated* Lipschitz group, so closedness is not visible.
We describe it by closed conditions (`spin_eq_S`):

  `Spin77 = {x | x* x = 1, x ι(e_j) x* ∈ ι(ℝ¹⁴) ∀ j, Mfun x ∈ (identity component of O77)}`,

where `Mfun x i j = tr(ρ(x) γ_j ρ(x*) γ_i)/(128 w_i)` is the matrix of `v ↦ ι⁻¹(x ι(v) x*)`.
`⊆` is immediate. For `⊇`, `cc_O77_iff_spin` gives `y ∈ Spin77` with the same conjugation
matrix; then `y* x` commutes with every `ι(v)`, so it is a scalar `c` with `c² = 1`, and
`x = ±y ∈ Spin77`. Each condition is closed, so **`isClosed_spin`**.
-/

namespace GU.Spinor

open Matrix CliffordAlgebra GU.Library

lemma continuous_star_cl : Continuous (star : Cl77 → Cl77) := by
  rw [isInducing_rep.continuous_iff, Function.comp_def]
  simp_rw [cliffordRep_star]
  exact (continuous_const.mul isInducing_rep.continuous.matrix_transpose).mul continuous_const

lemma isClosed_connectedComponentIn {α : Type*} [TopologicalSpace α] {F : Set α} (hF : IsClosed F)
    (x : α) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.mp ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF)
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

lemma isClosed_O77 : IsClosed (O77 : Set (Mat 14)) :=
  isClosed_eq (orthF_contDiff η77).continuous continuous_const

/-- The conjugation matrix, defined on all of `Cl(7,7)`. -/
noncomputable def Mfun (x : Cl77) : Mat 14 := fun i j =>
  trace (cliffordRep x * gammaMap (Pi.single j 1) * cliffordRep (star x) * gamma (gen i)) / (128 * w i)

lemma continuous_Mfun : Continuous Mfun := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.div_const (Continuous.matrix_trace ?_) _
  exact ((isInducing_rep.continuous.mul continuous_const).mul
    (isInducing_rep.continuous.comp continuous_star_cl)).mul continuous_const

lemma Mfun_spin (y : Spin77) : Mfun y = spinMat y := by
  funext i j; rw [spinMat_apply_trace, Mfun, cliffordRep_star]

/-- The closed description of `Spin(7,7)`. -/
def SpinS : Set Cl77 :=
  {x | star x * x = 1 ∧ (∀ j : Fin 14, x * ι Q77 (Pi.single j 1) * star x ∈ LinearMap.range (ι Q77)) ∧
    Mfun x ∈ connectedComponentIn (O77 : Set (Mat 14)) (Matrix.of.symm 1)}

lemma spin_subset_S : (Spin77 : Set Cl77) ⊆ SpinS := by
  intro x hx
  let y : Spin77 := ⟨x, hx⟩
  refine ⟨spinGroup.star_mul_self_of_mem hx, fun j => ⟨vecL y (Pi.single j 1), ι_vecL y _⟩, ?_⟩
  rw [show Mfun x = spinMat y from Mfun_spin y]
  exact (cc_O77_iff_spin _).mpr ⟨y, rfl⟩

lemma mul_star_of_star_mul {x : Cl77} (h : star x * x = 1) : x * star x = 1 := by
  apply cliffordRep_bijective.1
  rw [map_mul, map_one]
  have : cliffordRep (star x) * cliffordRep x = 1 := by rw [← map_mul, h, map_one]
  exact mul_eq_one_comm.mp this

lemma single_eq_smul (v : Fin 14 → ℝ) (i : Fin 14) :
    Pi.single i (v i) = v i • (Pi.single i 1 : Fin 14 → ℝ) := by
  ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]

/-- An element commuting with all `ι(v)` is a scalar. -/
lemma scalar_of_comm_ι (z : Cl77) (hz : ∀ v, z * ι Q77 v = ι Q77 v * z) :
    ∃ c : ℝ, z = algebraMap ℝ Cl77 c := by
  have hcen : ∀ y : Cl77, z * y = y * z := fun y => by
    have hy : y ∈ Algebra.adjoin ℝ (Set.range (ι Q77)) := by rw [adjoin_range_ι]; trivial
    induction hy using Algebra.adjoin_induction with
    | mem t ht => obtain ⟨v, rfl⟩ := ht; exact hz v
    | algebraMap r => exact (Algebra.commutes r _).symm
    | add a b _ _ ha hb => rw [mul_add, add_mul, ha, hb]
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  have hc : cl77Equiv z ∈ Set.center M128 := by
    rw [Semigroup.mem_center_iff]
    intro m
    obtain ⟨y, rfl⟩ := cl77Equiv.surjective m
    rw [← map_mul, ← map_mul, hcen y]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, cl77Equiv.injective (by rw [← hc, AlgEquiv.commutes]; rfl)⟩

lemma S_subset_spin : SpinS ⊆ (Spin77 : Set Cl77) := by
  rintro x ⟨h1, h2, h3⟩
  obtain ⟨y, hy⟩ := (cc_O77_iff_spin (Mfun x)).mp h3
  have hy' : spinMat y = Mfun x := hy
  have hx1 : x * star x = 1 := mul_star_of_star_mul h1
  have hys : star (y : Cl77) * y = 1 := spinGroup.star_mul_self_of_mem y.2
  have hys' : (y : Cl77) * star (y : Cl77) = 1 := spinGroup.mul_star_self_of_mem y.2
  -- same conjugation on basis vectors
  have hj : ∀ j, x * ι Q77 (Pi.single j 1) * star x =
      (y : Cl77) * ι Q77 (Pi.single j 1) * star (y : Cl77) := fun j => by
    obtain ⟨wj, hwj⟩ := h2 j
    rw [← ι_vecL, ← hwj]
    congr 1
    funext i
    rw [coord_trace wj i, ← cliffordRep_ι, hwj, map_mul, map_mul]
    have := congrFun (congrFun hy' i) j
    have h' : spinMat y i j = vecRep y (Pi.single j 1) i := by
      have := congrFun (of_spinMat_mulVec y (Pi.single j 1)) i
      rw [mulVec_single_one] at this; exact this
    rw [cliffordRep_ι]
    change _ = vecRep y (Pi.single j 1) i
    rw [← h', this]; rfl
  -- and on all vectors, by linearity
  have hv : ∀ v, x * ι Q77 v * star x = (y : Cl77) * ι Q77 v * star (y : Cl77) := fun v => by
    rw [← Finset.univ_sum_single v]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [single_eq_smul, map_smul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hj]
  set z := star (y : Cl77) * x with hzdef
  have hzz : star z * z = 1 := by
    rw [hzdef, star_mul, star_star]
    calc star x * (y : Cl77) * (star (y : Cl77) * x) = star x * ((y : Cl77) * star (y : Cl77)) * x := by
          simp only [mul_assoc]
      _ = 1 := by rw [hys', mul_one, h1]
  have hzc : ∀ v, z * ι Q77 v = ι Q77 v * z := fun v => by
    have hconj : z * ι Q77 v * star z = ι Q77 v := by
      rw [hzdef, star_mul, star_star]
      calc star (y : Cl77) * x * ι Q77 v * (star x * (y : Cl77))
          = star (y : Cl77) * (x * ι Q77 v * star x) * (y : Cl77) := by simp only [mul_assoc]
        _ = ι Q77 v := by
          rw [hv]
          calc star (y : Cl77) * ((y : Cl77) * ι Q77 v * star (y : Cl77)) * (y : Cl77)
              = (star (y : Cl77) * y) * ι Q77 v * (star (y : Cl77) * y) := by simp only [mul_assoc]
            _ = ι Q77 v := by rw [hys, one_mul, mul_one]
    calc z * ι Q77 v = z * ι Q77 v * (star z * z) := by rw [hzz, mul_one]
      _ = (z * ι Q77 v * star z) * z := by simp only [mul_assoc]
      _ = ι Q77 v * z := by rw [hconj]
  obtain ⟨c, hc⟩ := scalar_of_comm_ι z hzc
  have hstar_c : star (algebraMap ℝ Cl77 c) = algebraMap ℝ Cl77 c := by
    rw [CliffordAlgebra.star_def, involute.commutes, reverse.commutes]
  have hc2 : c * c = 1 := by
    rw [hc, hstar_c, ← map_mul] at hzz
    exact (algebraMap ℝ Cl77).injective (by rw [hzz, map_one])
  have hxy : x = (y : Cl77) * z := by
    rw [hzdef, ← mul_assoc, hys', one_mul]
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · rw [hxy, hc, h, map_one, mul_one]; exact y.2
  · rw [hxy, hc, h, map_neg, map_one, mul_neg, mul_one, ← neg_one_mul]
    exact Submonoid.mul_mem _ neg_one_mem_spin y.2

/-- **`Spin(7,7)` equals its closed description.** -/
theorem spin_eq_S : (Spin77 : Set Cl77) = SpinS :=
  Set.Subset.antisymm spin_subset_S S_subset_spin

/-- **`Spin(7,7)` is closed in `Cl(7,7)`.** -/
theorem isClosed_spin : IsClosed (Spin77 : Set Cl77) := by
  have hS : SpinS = {x | star x * x = 1} ∩
      ((⋂ j : Fin 14, (fun x => x * ι Q77 (Pi.single j 1) * star x) ⁻¹'
          (LinearMap.range (ι Q77) : Set Cl77)) ∩
        Mfun ⁻¹' connectedComponentIn (O77 : Set (Mat 14)) (Matrix.of.symm 1)) := by
    ext x; simp only [SpinS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [spin_eq_S, hS]
  refine (isClosed_eq (continuous_star_cl.mul continuous_id) continuous_const).inter
    ((isClosed_iInter fun j => ?_).inter
      ((isClosed_connectedComponentIn isClosed_O77 _).preimage continuous_Mfun))
  exact (Submodule.closed_of_finiteDimensional (LinearMap.range (ι Q77))).preimage
    ((continuous_id.mul continuous_const).mul continuous_star_cl)

end GU.Spinor
