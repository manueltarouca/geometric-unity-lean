/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinQuat

/-!
# `Sp(1) ≅ SU(2)` and `Spin4 ≅ SU(2) × SU(2)`

`qM : ℍ → M₂(ℂ)`, `a + b i + c j + d k ↦ [[a + b i, c + d i], [−c + d i, a − b i]]`, is multiplicative
(`qM_mul`), sends `star` to the conjugate transpose (`qM_star`), and has `det (qM q) = |q|²`
(`det_qM`). On unit quaternions it is a group isomorphism onto `SU(2)`:
* injective, since the entries recover `a, b, c, d`;
* surjective: for `U ∈ SU(2)`, `Uᴴ = U⁻¹ = adj U`, which forces `U = [[α, β], [−β̄, ᾱ]]`.

**`sp1EquivSU2 : Sp(1) ≃* SU(2)`** and, with `spin4QuatEquiv`,
**`spin4SU2Equiv : Spin4 ≃* SU(2) × SU(2)`**: the Pati–Salam `Spin(4)` factor (physically
`SU(2)_L × SU(2)_R`). Which factor is the weak `SU(2)_L` is a convention not fixed here.
-/

namespace GU.Spinor

open Matrix Quaternion

/-- The quaternion as a complex `2 × 2` matrix. -/
def qM (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

lemma qM_mul (p q : ℍ[ℝ]) : qM (p * q) = qM p * qM q := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma qM_one : qM 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qM]

lemma qM_star (q : ℍ[ℝ]) : qM (star q) = star (qM q) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qM, Matrix.star_apply]

lemma det_qM (q : ℍ[ℝ]) : (qM q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext
  · rw [Complex.ofReal_re, Quaternion.normSq_def']
    simp [qM]; ring
  · rw [Complex.ofReal_im]
    simp [qM]; ring

lemma qM_injective : Function.Injective qM := fun p q h => by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [qM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Complex.mk.injEq] at h00 h01
  ext
  · exact h00.1
  · exact h00.2
  · exact h01.1
  · exact h01.2

lemma qM_mem {q : ℍ[ℝ]} (hq : q ∈ unitary ℍ[ℝ]) : qM q ∈ specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨?_, ?_⟩
  · show qM q ∈ unitaryGroup (Fin 2) ℂ
    rw [mem_unitaryGroup_iff', ← qM_star, ← qM_mul, (Unitary.mem_iff.mp hq).1, qM_one]
  · show (qM q).det = 1
    rw [det_qM, normSq_one_of_unitary hq]; simp

/-- `Sp(1) →* SU(2)`. -/
noncomputable def sp1ToSU2 : unitary ℍ[ℝ] →* specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨qM q, qM_mem q.2⟩
  map_one' := Subtype.ext qM_one
  map_mul' p q := Subtype.ext (qM_mul p q)

lemma sp1ToSU2_surjective : Function.Surjective sp1ToSU2 := by
  rintro ⟨U, hU⟩
  obtain ⟨hu, hdet⟩ := mem_specialUnitaryGroup_iff.mp hU
  have hdet' : U.det = 1 := hdet
  -- `Uᴴ = U⁻¹ = adj U`
  have hinv : star U = U⁻¹ := (Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.mp hu)).symm
  have hadj : U⁻¹ = U.adjugate := by rw [Matrix.inv_def, hdet', Ring.inverse_one, one_smul]
  have hsa : star U = U.adjugate := hinv.trans hadj
  rw [Matrix.adjugate_fin_two] at hsa
  have e11 := congrFun (congrFun hsa 0) 0
  have e10 := congrFun (congrFun hsa 0) 1
  simp only [Matrix.star_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e11 e10
  set α := U 0 0
  set β := U 0 1
  have hU10 : U 1 0 = -star β := by
    have := congrArg star e10; rwa [star_star, star_neg] at this
  have hU11 : U 1 1 = star α := e11.symm
  let q : ℍ[ℝ] := ⟨α.re, α.im, β.re, β.im⟩
  have hqU : qM q = U := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · show (⟨-β.re, β.im⟩ : ℂ) = U 1 0
      rw [hU10]; apply Complex.ext <;> simp
    · show (⟨α.re, -α.im⟩ : ℂ) = U 1 1
      rw [hU11]; apply Complex.ext <;> simp
  have hq : q ∈ unitary ℍ[ℝ] := by
    have hn : normSq q = 1 := by
      have := det_qM q
      rw [hqU, hdet'] at this
      exact_mod_cast this.symm
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · rw [star_mul_self, hn]; simp
    · rw [self_mul_star, hn]; simp
  exact ⟨⟨q, hq⟩, Subtype.ext hqU⟩

/-- **`Sp(1) ≃* SU(2)`**. -/
noncomputable def sp1EquivSU2 : unitary ℍ[ℝ] ≃* specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective sp1ToSU2
    ⟨fun _ _ h => Subtype.ext (qM_injective (congrArg Subtype.val h)), sp1ToSU2_surjective⟩

/-- **`Spin4 ≃* SU(2) × SU(2)`**, the Pati–Salam `Spin(4)` (physically `SU(2)_L × SU(2)_R`; the
factor labelling is a convention not fixed here). -/
noncomputable def spin4SU2Equiv :
    Spin4 ≃* specialUnitaryGroup (Fin 2) ℂ × specialUnitaryGroup (Fin 2) ℂ :=
  spin4QuatEquiv.trans (MulEquiv.prodCongr sp1EquivSU2 sp1EquivSU2)

end GU.Spinor
