import GU.Shiab.EinsteinEquation
import GU.Spinor.Faithful

/-!
# The covering homomorphism `Spin(7,7) → O(7,7)` (vector representation)

For `x ∈ Spin(7,7)`, conjugation `v ↦ x·ι(v)·x*` preserves the vectors (`range ι`, Mathlib's
`pinGroup.conjAct_smul_ι_mem_range_ι`) and the quadratic form. This gives a group homomorphism
`vecRep : Spin(7,7) →* GL(ℝ¹⁴)` with `Q77 (vecRep x v) = Q77 v` (`vecRep_isometry`), whose kernel
contains `±1` (`vecRep_neg_one`). This is the algebraic core of the spin double cover
`P̃_Fr(C) → P_Fr(C)`: a spin structure is a lift of the orthonormal frame bundle along `vecRep`.
`ker = {±1}` is proved in `SpinKernel.lean`; surjectivity onto `SO₀(7,7)` is not proved, nor is global existence of the lift
(the `w₂` obstruction) is outside Mathlib.
-/

namespace GU.Spinor

open CliffordAlgebra

noncomputable instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

theorem gammaMap_injective : Function.Injective gammaMap := by
  intro u v h
  have hl := gamma_linIndep
  rw [Fintype.linearIndependent_iff] at hl
  have : ∑ i, (u i - v i) • gamma (gen i) = 0 := by
    have h' : gammaMap u - gammaMap v = 0 := sub_eq_zero.mpr h
    simpa [gammaMap, sub_smul, Finset.sum_sub_distrib] using h'
  funext i; exact sub_eq_zero.mp (hl _ this i)

theorem ι_injective : Function.Injective (ι Q77) := by
  intro u v h
  apply gammaMap_injective
  rw [← cliffordRep_ι, ← cliffordRep_ι, h]

/-- `ι` onto its range. -/
noncomputable def ιEquiv : (Fin 14 → ℝ) ≃ₗ[ℝ] LinearMap.range (ι Q77) :=
  LinearEquiv.ofInjective (ι Q77) ι_injective

/-- Spin elements as units. -/
def spinUnit (x : Spin77) : (Cl77)ˣ :=
  ⟨x, star (x : Cl77), spinGroup.mul_star_self_of_mem x.2, spinGroup.star_mul_self_of_mem x.2⟩

/-- Conjugation `v ↦ x ι(v) x*` as a linear map into `range ι`. -/
noncomputable def conjL (x : Spin77) : (Fin 14 → ℝ) →ₗ[ℝ] LinearMap.range (ι Q77) :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℝ (x : Cl77)).comp
      ((LinearMap.mulRight ℝ (star (x : Cl77))).comp (ι Q77))) (fun v => by
    have := pinGroup.conjAct_smul_ι_mem_range_ι (x := spinUnit x) (x.2.1) v
    simpa [ConjAct.units_smul_def, spinUnit, mul_assoc] using this)

/-- The vector representation, as a linear map. -/
noncomputable def vecL (x : Spin77) : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ) :=
  ιEquiv.symm.toLinearMap.comp (conjL x)

lemma ι_vecL (x : Spin77) (v : Fin 14 → ℝ) :
    ι Q77 (vecL x v) = (x : Cl77) * ι Q77 v * star (x : Cl77) := by
  have h := congrArg Subtype.val (ιEquiv.apply_symm_apply (conjL x v))
  simpa [vecL, ιEquiv, conjL, mul_assoc] using h

lemma vecL_mul (x y : Spin77) (v : Fin 14 → ℝ) : vecL (x * y) v = vecL x (vecL y v) := by
  apply ι_injective
  rw [ι_vecL, ι_vecL, ι_vecL, Submonoid.coe_mul, star_mul]
  simp only [mul_assoc]

lemma vecL_one (v : Fin 14 → ℝ) : vecL 1 v = v := by
  apply ι_injective; rw [ι_vecL]; simp

/-- **The vector representation** `Spin(7,7) →* GL(ℝ¹⁴)`. -/
noncomputable def vecRep : Spin77 →* ((Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) where
  toFun x :=
    { vecL x with
      invFun := vecL (star x)
      left_inv := fun v => by
        show vecL (star x) (vecL x v) = v
        rw [← vecL_mul, spinGroup.star_mul_self, vecL_one]
      right_inv := fun v => by
        show vecL x (vecL (star x) v) = v
        rw [← vecL_mul, spinGroup.mul_star_self, vecL_one] }
  map_one' := LinearEquiv.ext vecL_one
  map_mul' x y := LinearEquiv.ext (vecL_mul x y)

/-- `vecRep` preserves the (7,7) form. -/
theorem vecRep_isometry (x : Spin77) (v : Fin 14 → ℝ) : Q77 (vecRep x v) = Q77 v := by
  have h1 := ι_sq_scalar Q77 (vecRep x v)
  have hv : ι Q77 (vecRep x v) = (x : Cl77) * ι Q77 v * star (x : Cl77) := ι_vecL x v
  rw [hv] at h1
  have h2 : (x : Cl77) * ι Q77 v * star (x : Cl77) * ((x : Cl77) * ι Q77 v * star (x : Cl77))
      = algebraMap ℝ Cl77 (Q77 v) := by
    calc _ = (x : Cl77) * ι Q77 v * (star (x : Cl77) * (x : Cl77)) * ι Q77 v * star (x : Cl77) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [spinGroup.star_mul_self_of_mem x.2, mul_one, mul_assoc (x : Cl77), ι_sq_scalar,
            Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
            spinGroup.mul_star_self_of_mem x.2, ← Algebra.algebraMap_eq_smul_one]
  rw [h2] at h1
  exact (algebraMap ℝ Cl77).injective h1.symm

lemma Q77_e7 : Q77 (Pi.single 7 1) = -1 := by
  simp [Q77, QuadraticMap.weightedSumSquares_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- `−1 = ι(e₇)²` lies in `Spin(7,7)`. -/
theorem neg_one_mem_spin : (-1 : Cl77) ∈ spinGroup Q77 := by
  set e : Fin 14 → ℝ := Pi.single 7 1
  have hsq : ι Q77 e * ι Q77 e = -1 := by
    rw [ι_sq_scalar, Q77_e7, map_neg, map_one]
  let u : (Cl77)ˣ := ⟨ι Q77 e, -ι Q77 e, by rw [mul_neg, hsq, neg_neg], by rw [neg_mul, hsq, neg_neg]⟩
  have hu : u ∈ lipschitzGroup Q77 := Subgroup.subset_closure ⟨e, rfl⟩
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨⟨u * u, (lipschitzGroup Q77).mul_mem hu hu, ?_⟩, ?_⟩, ?_⟩
  · show (u : Cl77) * u = -1; exact hsq
  · rw [Unitary.mem_iff]; simp
  · rw [show (-1 : Cl77) = algebraMap ℝ Cl77 (-1) by simp]
    exact (CliffordAlgebra.even Q77).algebraMap_mem _

/-- `−1 ∈ Spin(7,7)` acts trivially: the covering is (at least) two-to-one. -/
theorem vecRep_neg_one (v : Fin 14 → ℝ) : vecRep ⟨-1, neg_one_mem_spin⟩ v = v := by
  show vecL ⟨-1, neg_one_mem_spin⟩ v = v
  apply ι_injective; rw [ι_vecL]; simp

end GU.Spinor
