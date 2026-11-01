/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Torus

/-!
# `U(1)_Y` has minimal period exactly `π`

Via the vector representation: the circle in plane `k` rotates its own plane by twice the angle
(`vecRep_circle`) and fixes every vector supported off that plane (`circle_fixes`). So `U1Y t` rotates
the `e₁e₂` plane by `−4t` and the `e₁₀e₁₁` plane by `6t`. If `U1Y t = 1` then `cos 4t = cos 6t = 1`,
hence `t ∈ πℤ` (**`U1Y_eq_one_iff`**, with `U1Y_pi`).
-/

namespace GU.Spinor

open CliffordAlgebra Real

lemma planeRot_gens (k : Fin 5) (s : ℝ) (S : Finset (Fin 14)) (hS : pa k ∈ S ∧ pb k ∈ S) :
    planeCircle k (Multiplicative.ofAdd s) ∈ gens S (εp k) := by
  have ha : SuppIn S (eb (pa k)) := fun j hj => by
    have : j ≠ pa k := fun h => hj (h ▸ hS.1)
    simp [eb, this]
  have hb : SuppIn S (eb (pb k)) := fun j hj => by
    have : j ≠ pb k := fun h => hj (h ▸ hS.2)
    simp [eb, this]
  refine ⟨εp k • eb (pa k), cos s • eb (pa k) + (εp k * sin s) • eb (pb k),
    fun j hj => by simp [ha j hj], fun j hj => by simp [ha j hj, hb j hj], ?_, ?_, R_eq k s⟩
  · rw [QuadraticMap.map_smul, ← εp, εp_sq, one_smul]
  · rw [QuadraticMap.map_add Q77, QuadraticMap.map_smul, QuadraticMap.map_smul, Qb_eq,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, polar_eb (pa_ne_pb k), ← εp]
    have := sin_sq_add_cos_sq s
    have he := εp_sq k
    simp only [smul_eq_mul, mul_zero, add_zero]
    linear_combination (εp k) * this + (sin s ^ 2 * εp k) * he

/-- The circle in plane `k` fixes vectors supported off that plane. -/
lemma circle_fixes (k : Fin 5) (s : ℝ) (v : Fin 14 → ℝ) (hv : v (pa k) = 0 ∧ v (pb k) = 0) :
    vecRep (planeCircle k (Multiplicative.ofAdd s)) v = v := by
  have hS : pa k ∈ ({pa k, pb k} : Finset (Fin 14)) ∧ pb k ∈ ({pa k, pb k} : Finset (Fin 14)) := by simp
  refine gens_fix (planeRot_gens k s _ hS) v (off_perp fun i hi => ?_)
  rcases Finset.mem_insert.mp hi with rfl | h
  · exact hv.1
  · rw [Finset.mem_singleton.mp h]; exact hv.2

lemma star_planeP (k : Fin 5) : star (planeP k) = -planeP k := by
  rw [planeP, star_mul, star_ι, star_ι, neg_mul_neg, ι_anticomm (polar_eb (pa_ne_pb k).symm)]

lemma star_planeRot (k : Fin 5) (s : ℝ) : star (planeRot k s) = planeRot k (-s) := by
  simp [planeRot, star_planeP, Algebra.algebraMap_eq_smul_one, cos_neg, sin_neg]

/-- **Each circle rotates its plane by twice the angle.** -/
lemma vecRep_circle (k : Fin 5) (s : ℝ) :
    vecRep (planeCircle k (Multiplicative.ofAdd s)) (eb (pa k)) =
      cos (2 * s) • eb (pa k) - (εp k * sin (2 * s)) • eb (pb k) := by
  apply ι_injective
  show ι Q77 (vecL _ _) = _
  rw [ι_vecL]
  show planeRot k s * ι Q77 (eb (pa k)) * star (planeRot k s) = _
  rw [star_planeRot]
  have hab := ι_anticomm (polar_eb (pa_ne_pb k).symm)  -- ι b ι a = -(ι a ι b)
  have hqa : ι Q77 (eb (pa k)) * ι Q77 (eb (pa k)) = εp k • (1 : Cl77) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]; rfl
  have hqb : ι Q77 (eb (pb k)) * ι Q77 (eb (pb k)) = εp k • (1 : Cl77) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, Qb_eq]
  have h1 : planeP k * ι Q77 (eb (pa k)) = -(εp k • ι Q77 (eb (pb k))) := by
    rw [planeP, mul_assoc, hab, mul_neg, ← mul_assoc, hqa, smul_one_mul]
  have h2 : ι Q77 (eb (pa k)) * planeP k = εp k • ι Q77 (eb (pb k)) := by
    rw [planeP, ← mul_assoc, hqa, smul_one_mul]
  have h3 : ι Q77 (eb (pb k)) * planeP k = -(εp k • ι Q77 (eb (pa k))) := by
    rw [planeP, ← mul_assoc, hab, neg_mul, mul_assoc, hqb, mul_smul_comm, mul_one]
  have he := εp_sq k
  have hR : planeRot k s = cos s • (1 : Cl77) + sin s • planeP k := by
    simp [planeRot, Algebra.algebraMap_eq_smul_one]
  have hR' : planeRot k (-s) = cos s • (1 : Cl77) + (-sin s) • planeP k := by
    simp [planeRot, Algebra.algebraMap_eq_smul_one, cos_neg, sin_neg]
  rw [hR, hR', map_sub, map_smul, map_smul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2]
  rw [neg_mul, smul_mul_assoc, h3]
  rw [cos_two_mul', sin_two_mul]
  match_scalars
  · linear_combination (-(sin s ^ 2)) * he
  · ring

lemma U1Y_prod (t : ℝ) : U1Y (Multiplicative.ofAdd t) =
    planeCircle 0 (Multiplicative.ofAdd (-2 * t)) * planeCircle 1 (Multiplicative.ofAdd (-2 * t)) *
      planeCircle 2 (Multiplicative.ofAdd (-2 * t)) * planeCircle 3 (Multiplicative.ofAdd (3 * t)) *
        planeCircle 4 (Multiplicative.ofAdd (3 * t)) := by
  rw [U1Y, MonoidHom.comp_apply, torus_eq]
  simp [ycoef]

/-- **`U1Y t = 1` iff `t ∈ πℤ`**: the hypercharge circle has minimal period exactly `π`. -/
theorem U1Y_eq_one_iff (t : ℝ) : U1Y (Multiplicative.ofAdd t) = 1 ↔ ∃ z : ℤ, t = z * π := by
  constructor
  · intro h
    have hv : ∀ v, vecRep (U1Y (Multiplicative.ofAdd t)) v = v := fun v => by rw [h, map_one]; rfl
    -- plane e₁e₂: rotation by −4t
    have h1 := hv (eb 1)
    rw [U1Y_prod] at h1
    simp only [map_mul, LinearEquiv.mul_apply] at h1
    rw [circle_fixes 4 _ _ (by simp [eb, pa, pb]), circle_fixes 3 _ _ (by simp [eb, pa, pb]),
      circle_fixes 2 _ _ (by simp [eb, pa, pb]), circle_fixes 1 _ _ (by simp [eb, pa, pb])] at h1
    have h1' := vecRep_circle 0 (-2 * t)
    simp only [pa, pb] at h1'
    rw [show (![1, 3, 5, 10, 12] : Fin 5 → Fin 14) 0 = 1 from rfl] at h1'
    rw [h1'] at h1
    have c1 := congrFun h1 1
    simp [eb] at c1
    -- plane e₁₀e₁₁: rotation by 6t
    have h2 := hv (eb 10)
    rw [U1Y_prod] at h2
    simp only [map_mul, LinearEquiv.mul_apply] at h2
    rw [circle_fixes 4 _ _ (by simp [eb, pa, pb])] at h2
    have h2' := vecRep_circle 3 (3 * t)
    rw [show pa 3 = 10 from rfl, show pb 3 = 11 from rfl] at h2'
    rw [h2', circle_fixes 2 _ _ (by simp [eb, pa, pb]), circle_fixes 1 _ _ (by simp [eb, pa, pb]),
      circle_fixes 0 _ _ (by simp [eb, pa, pb])] at h2
    have c2 := congrFun h2 10
    simp [eb] at c2
    -- trigonometry
    obtain ⟨m, hm⟩ := (cos_eq_one_iff _).mp c1
    obtain ⟨n, hn⟩ := (cos_eq_one_iff _).mp c2
    have hint : ((3 * m - 2 * n : ℤ) : ℝ) * (2 * π) = 0 := by push_cast; linarith [hm, hn]
    have hz : 3 * m - 2 * n = 0 := by
      rcases mul_eq_zero.mp hint with h | h
      · exact_mod_cast h
      · exfalso; linarith [pi_pos]
    obtain ⟨j, hj⟩ : ∃ j : ℤ, m = 2 * j := ⟨m / 2, by omega⟩
    refine ⟨j, ?_⟩
    rw [hj] at hm
    push_cast at hm
    linarith
  · rintro ⟨z, rfl⟩
    have : Multiplicative.ofAdd ((z : ℝ) * π) = (Multiplicative.ofAdd π) ^ z := by
      rw [← ofAdd_zsmul, zsmul_eq_mul]
    rw [this, map_zpow]
    have h1 : U1Y (Multiplicative.ofAdd π) = 1 := Subtype.ext U1Y_pi
    rw [h1, one_zpow]

end GU.Spinor
