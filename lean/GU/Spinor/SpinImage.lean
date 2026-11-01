/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SpinDet
import GU.Spinor.Torus

/-!
# The image of `Spin(7,7) → SO(7,7)`: `SO⁺(7,7)`, the spinor-norm kernel in `SO(7,7)`

Written from scratch for `Q77`. TauCeti (`TauCeti/LinearAlgebra/QuadraticForm/CartanDieudonne`,
`…/Spin/SpinorNorm`) was read only as a reference; it is not a dependency and no code is copied.

1. **Reflections generate the isometries** (`isom_eq_reflProd`). Any linear `g` with
   `Q(g v) = Q v` is a product of reflections in vectors with `Q = ±1`. We fix the basis vectors
   `e₀, e₁, …` one at a time. For `x = e_k` and `y = g x`, use `refl (y − x)` if `Q(y − x) ≠ 0`,
   otherwise `refl x ∘ refl (y + x)`, since `Q(y + x) + Q(y − x) = 4 Q x ≠ 0`. Both fix the
   earlier `e_j`. This is the unbounded Cartan–Dieudonné theorem (no `≤ n` bound), so the
   isotropic exceptional case never arises.
2. **Clifford lift** (`yProd_conj`). `Y = ι v₁ ⋯ ι vₘ` conjugates `ι w` to
   `(∏ Q vᵢ) • ι(r_{v₁} ⋯ r_{vₘ} w)`.
3. **Spinor norm** (`vecRep_factor`). If `vecRep x = r_{v₁} ⋯ r_{vₘ}` then `m` is even (by
   determinants) and `∏ Q vᵢ = 1`. Proof: `star Y · x` commutes with every vector, so it is a scalar
   `c`, and `c² = ∏ Q vᵢ`.
4. **`range_vecRep`**: `g` is in the image of `vecRep` iff it is a product of an even number of
   unit reflections with `∏ Q vᵢ = 1`. This is the algebraic `SO⁺(7,7)`: the kernel of the spinor
   norm intersected with `SO(7,7)` (the parity condition is needed: `r_{e₀}` has norm `1`, `det −1`).
   Consequences:
   * the spinor norm `∏ Q vᵢ` is well defined on all of `O(7,7)` (`qProd_eq_of_reflProd_eq`);
   * `Spin(7,7)` is **not** onto `SO(7,7)`: `g₀ = r_{e₀} r_{e₇}` has `det = 1` but is not in the
     image (`g0_not_mem`);
   * the image has index exactly `2` in `SO(7,7)`: every `det = 1` isometry `g` has `g` or `g₀ g` in
     the image (`mem_or_g0_mul_mem`), and never both (`not_both`). (Informal index: no
     `Subgroup.index` is computed.)

`SO⁺(7,7)` is the identity component `SO₀(7,7)` of the matrix group `O(7,7)`, both connected and path
component (`cc_iff_spin`, `joined_iff_spin_mat`, `SpinComponent.lean`).
-/

namespace GU.Spinor

open CliffordAlgebra

/-- Vectors with `Q = ±1`. -/
abbrev UVec := {m : Fin 14 → ℝ // Q77 m = 1 ∨ Q77 m = -1}

lemma UVec.Q_ne (m : UVec) : Q77 m.1 ≠ 0 := by rcases m.2 with h | h <;> rw [h] <;> norm_num

lemma UVec.Q_sq (m : UVec) : Q77 m.1 * Q77 m.1 = 1 := by rcases m.2 with h | h <;> rw [h] <;> norm_num

/-! ### Reflections -/

section Refl

variable {m : Fin 14 → ℝ}

lemma refl_isometry (hm : Q77 m ≠ 0) (v : Fin 14 → ℝ) : Q77 (refl m v) = Q77 v := by
  rw [refl_apply, sub_eq_add_neg, QuadraticMap.map_add Q77, QuadraticMap.map_neg, QuadraticMap.map_smul,
    QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q77 v m]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma refl_refl (hm : Q77 m ≠ 0) (v : Fin 14 → ℝ) : refl m (refl m v) = v := by
  rw [refl_apply m (refl m v), refl_apply m v, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_self]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have hpq : QuadraticMap.polar Q77 m v / Q77 m * (2 * Q77 m) = 2 * QuadraticMap.polar Q77 m v := by
    field_simp
  rw [hpq, show (QuadraticMap.polar Q77 m v - 2 * QuadraticMap.polar Q77 m v) / Q77 m =
    -(QuadraticMap.polar Q77 m v / Q77 m) by ring]
  module

lemma refl_fix {v : Fin 14 → ℝ} (h : QuadraticMap.polar Q77 m v = 0) : refl m v = v := by
  rw [refl_apply, h, zero_div, zero_smul, sub_zero]

lemma refl_self (hm : Q77 m ≠ 0) : refl m m = -m := by
  rw [refl_apply, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat, mul_div_assoc, div_self hm,
    mul_one]
  module

lemma refl_smul {c : ℝ} (hc : c ≠ 0) : refl (c • m) = refl m := by
  refine LinearMap.ext fun v => ?_
  rw [refl_apply, refl_apply, QuadraticMap.polar_smul_left, QuadraticMap.map_smul, smul_smul]
  congr 1
  simp only [smul_eq_mul]
  field_simp

/-- Every reflection in an anisotropic vector is a reflection in a unit vector. -/
lemma exists_UVec (hm : Q77 m ≠ 0) : ∃ u : UVec, refl u.1 = refl m := by
  set c : ℝ := (Real.sqrt |Q77 m|)⁻¹
  have hpos : 0 < |Q77 m| := abs_pos.mpr hm
  have hc : c ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr hpos)
  have hcc : c * c = (|Q77 m|)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  have hQ : Q77 (c • m) = Q77 m / |Q77 m| := by
    rw [QuadraticMap.map_smul, smul_eq_mul, hcc, inv_mul_eq_div]
  refine ⟨⟨c • m, ?_⟩, refl_smul hc⟩
  rw [hQ]
  rcases lt_or_gt_of_ne hm with h | h
  · right; rw [abs_of_neg h, div_neg, div_self hm]
  · left; rw [abs_of_pos h, div_self hm]

end Refl

/-! ### Products of reflections -/

/-- `r_{v₁} ∘ ⋯ ∘ r_{vₘ}`. -/
noncomputable def reflProd (l : List UVec) : Module.End ℝ (Fin 14 → ℝ) := (l.map fun m => refl m.1).prod

/-- `∏ Q vᵢ`. -/
noncomputable def qProd (l : List UVec) : ℝ := (l.map fun m => Q77 m.1).prod

/-- `ι v₁ ⋯ ι vₘ`. -/
noncomputable def yProd (l : List UVec) : Cl77 := (l.map fun m => ι Q77 m.1).prod

@[simp] lemma reflProd_nil : reflProd [] = 1 := rfl
@[simp] lemma reflProd_cons (m : UVec) (l : List UVec) : reflProd (m :: l) = refl m.1 * reflProd l := rfl
@[simp] lemma qProd_nil : qProd [] = 1 := rfl
@[simp] lemma qProd_cons (m : UVec) (l : List UVec) : qProd (m :: l) = Q77 m.1 * qProd l := rfl
@[simp] lemma yProd_nil : yProd [] = 1 := rfl
@[simp] lemma yProd_cons (m : UVec) (l : List UVec) : yProd (m :: l) = ι Q77 m.1 * yProd l := rfl

lemma reflProd_append (l l' : List UVec) : reflProd (l ++ l') = reflProd l * reflProd l' := by
  simp [reflProd, List.map_append, List.prod_append]

lemma qProd_append (l l' : List UVec) : qProd (l ++ l') = qProd l * qProd l' := by
  simp [qProd, List.map_append, List.prod_append]

lemma qProd_sq (l : List UVec) : qProd l * qProd l = 1 := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [qProd_cons]
    calc Q77 m.1 * qProd l * (Q77 m.1 * qProd l) = (Q77 m.1 * Q77 m.1) * (qProd l * qProd l) := by ring
      _ = 1 := by rw [m.Q_sq, ih, one_mul]

lemma qProd_eq_one_or (l : List UVec) : qProd l = 1 ∨ qProd l = -1 :=
  mul_self_eq_one_iff.mp (qProd_sq l)

lemma qProd_reverse (l : List UVec) : qProd l.reverse = qProd l := by
  simp [qProd, List.map_reverse, List.prod_reverse]

lemma reflProd_reverse_mul (l : List UVec) : reflProd l.reverse * reflProd l = 1 := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [List.reverse_cons, reflProd_append, reflProd_cons, reflProd_cons, reflProd_nil, mul_one,
      show reflProd l.reverse * refl m.1 * (refl m.1 * reflProd l) =
        reflProd l.reverse * (refl m.1 * refl m.1) * reflProd l by simp only [mul_assoc]]
    have : refl m.1 * refl m.1 = 1 := LinearMap.ext fun v => refl_refl m.Q_ne v
    rw [this, mul_one, ih]

lemma det_reflProd (l : List UVec) : LinearMap.det (reflProd l) = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons m l ih => rw [reflProd_cons, map_mul, det_refl _ m.Q_ne, ih, List.length_cons, pow_succ']

/-! ### Reflections generate the isometries -/

/-- `g` preserves `Q77`. -/
def IsIsom77 (g : Module.End ℝ (Fin 14 → ℝ)) : Prop := ∀ v, Q77 (g v) = Q77 v

lemma IsIsom77.polar {g : Module.End ℝ (Fin 14 → ℝ)} (hg : IsIsom77 g) (v w : Fin 14 → ℝ) :
    QuadraticMap.polar Q77 (g v) (g w) = QuadraticMap.polar Q77 v w := by
  simp only [QuadraticMap.polar]
  rw [← map_add, hg, hg, hg]

lemma IsIsom77.mul {f g : Module.End ℝ (Fin 14 → ℝ)} (hf : IsIsom77 f) (hg : IsIsom77 g) :
    IsIsom77 (f * g) := fun v => by rw [Module.End.mul_apply, hf, hg]

lemma isIsom_reflProd (l : List UVec) : IsIsom77 (reflProd l) := by
  induction l with
  | nil => intro v; rfl
  | cons m l ih => exact IsIsom77.mul (refl_isometry m.Q_ne) ih

lemma Q_eb_ne (i : Fin 14) : Q77 (eb i) ≠ 0 := by rw [Q_eb]; split_ifs <;> norm_num

/-- `polar (y − x) y = Q (y − x)` when `Q y = Q x`. -/
lemma polar_sub_self {x y : Fin 14 → ℝ} (h : Q77 y = Q77 x) :
    QuadraticMap.polar Q77 (y - x) y = Q77 (y - x) := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, nsmul_eq_mul, sub_eq_add_neg y x,
    QuadraticMap.map_add Q77, QuadraticMap.map_neg, QuadraticMap.polar_neg_right,
    QuadraticMap.polar_comm Q77 x y, h]
  ring

/-- `polar (y + x) y = Q (y + x)` when `Q y = Q x`. -/
lemma polar_add_self {x y : Fin 14 → ℝ} (h : Q77 y = Q77 x) :
    QuadraticMap.polar Q77 (y + x) y = Q77 (y + x) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self, nsmul_eq_mul, QuadraticMap.map_add Q77,
    QuadraticMap.polar_comm Q77 x y, h]
  ring

/-- One step: if `f` fixes `e_j` for `j < k`, some reflections make it also fix `e_k`. -/
lemma step (f : Module.End ℝ (Fin 14 → ℝ)) (hf : IsIsom77 f) (k : Fin 14)
    (hfix : ∀ j : Fin 14, j < k → f (eb j) = eb j) :
    ∃ l : List UVec, ∀ j : Fin 14, j ≤ k → (reflProd l * f) (eb j) = eb j := by
  set x := eb k
  set y := f x
  have hQ : Q77 y = Q77 x := hf x
  have hx : Q77 x ≠ 0 := Q_eb_ne k
  have hyo : ∀ j : Fin 14, j < k → QuadraticMap.polar Q77 y (eb j) = 0 := fun j hj => by
    rw [← hfix j hj, hf.polar, polar_eb (Fin.ne_of_gt hj)]
  have hxo : ∀ j : Fin 14, j < k → QuadraticMap.polar Q77 x (eb j) = 0 :=
    fun j hj => polar_eb (Fin.ne_of_gt hj)
  by_cases hd : Q77 (y - x) ≠ 0
  · obtain ⟨u, hu⟩ := exists_UVec hd
    refine ⟨[u], fun j hj => ?_⟩
    simp only [reflProd_cons, reflProd_nil, mul_one, Module.End.mul_apply, hu]
    rcases lt_or_eq_of_le hj with hj | rfl
    · rw [hfix j hj]
      exact refl_fix (m := y - x) (v := eb j)
        (by rw [QuadraticMap.polar_sub_left, hyo j hj, hxo j hj, sub_zero])
    · show refl (y - x) y = x
      rw [refl_apply, polar_sub_self hQ, div_self hd, one_smul, sub_sub_cancel]
  · push Not at hd
    have hs : Q77 (y + x) ≠ 0 := by
      have e1 : Q77 (y + x) = Q77 y + Q77 x + QuadraticMap.polar Q77 y x := QuadraticMap.map_add Q77 _ _
      have e2 : Q77 (y - x) = Q77 y + Q77 x - QuadraticMap.polar Q77 y x := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q77, QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
        ring
      intro h0
      apply hx
      linarith
    obtain ⟨u, hu⟩ := exists_UVec hs
    obtain ⟨w, hw⟩ := exists_UVec hx
    refine ⟨[w, u], fun j hj => ?_⟩
    simp only [reflProd_cons, reflProd_nil, mul_one, Module.End.mul_apply, hu, hw]
    rcases lt_or_eq_of_le hj with hj | rfl
    · rw [hfix j hj, refl_fix (m := y + x) (v := eb j)
        (by rw [QuadraticMap.polar_add_left, hyo j hj, hxo j hj, add_zero]),
        refl_fix (m := x) (v := eb j) (hxo j hj)]
    · show refl x (refl (y + x) y) = x
      rw [refl_apply (y + x), polar_add_self hQ, div_self hs, one_smul,
        show y - (y + x) = -x by abel, map_neg, refl_self hx, neg_neg]

lemma fix_upto (f : Module.End ℝ (Fin 14 → ℝ)) (hf : IsIsom77 f) :
    ∀ n ≤ 14, ∃ l : List UVec, ∀ j : Fin 14, (j : ℕ) < n → (reflProd l * f) (eb j) = eb j := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨l, hl⟩ := ih (by omega)
    obtain ⟨l', hl'⟩ := step (reflProd l * f) ((isIsom_reflProd l).mul hf) ⟨n, by omega⟩
      (fun j hj => hl j hj)
    refine ⟨l' ++ l, fun j hj => ?_⟩
    rw [reflProd_append, mul_assoc]
    exact hl' j (by rw [Fin.le_def]; show (j : ℕ) ≤ n; omega)

/-- **Reflections generate the isometries of `(ℝ¹⁴, Q77)`** (unbounded Cartan–Dieudonné). -/
theorem isom_eq_reflProd (g : Module.End ℝ (Fin 14 → ℝ)) (hg : IsIsom77 g) :
    ∃ l : List UVec, g = reflProd l := by
  obtain ⟨l, hl⟩ := fix_upto g hg 14 le_rfl
  have hid : reflProd l * g = 1 :=
    (Pi.basisFun ℝ (Fin 14)).ext fun j => by
      simpa [Pi.basisFun_apply] using hl j j.2
  refine ⟨l.reverse, ?_⟩
  calc g = (reflProd l.reverse * reflProd l) * g := by rw [reflProd_reverse_mul, one_mul]
    _ = reflProd l.reverse := by rw [mul_assoc, hid, mul_one]

/-! ### Clifford lift -/

lemma ι_conj (m : UVec) (v : Fin 14 → ℝ) :
    ι Q77 m.1 * ι Q77 v * star (ι Q77 m.1) = Q77 m.1 • ι Q77 (refl m.1 v) := by
  have hm := m.Q_ne
  have hanti := ι_mul_ι_add_swap (Q := Q77) m.1 v
  have e1 : ι Q77 m.1 * ι Q77 v =
      algebraMap ℝ Cl77 (QuadraticMap.polar Q77 m.1 v) - ι Q77 v * ι Q77 m.1 := by
    rw [← hanti]; abel
  rw [CliffordAlgebra.star_ι, mul_neg, e1, sub_mul, mul_assoc, ι_sq_scalar, refl_apply, map_sub,
    map_smul, smul_sub, smul_smul, mul_div_cancel₀ _ hm]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  abel

lemma yProd_conj (l : List UVec) (w : Fin 14 → ℝ) :
    yProd l * ι Q77 w * star (yProd l) = qProd l • ι Q77 (reflProd l w) := by
  induction l generalizing w with
  | nil => simp
  | cons m l ih =>
    rw [yProd_cons, star_mul, qProd_cons, reflProd_cons, Module.End.mul_apply,
      show ι Q77 m.1 * yProd l * ι Q77 w * (star (yProd l) * star (ι Q77 m.1)) =
        ι Q77 m.1 * (yProd l * ι Q77 w * star (yProd l)) * star (ι Q77 m.1) by simp only [mul_assoc],
      ih, mul_smul_comm, smul_mul_assoc, ι_conj, smul_smul, mul_comm]

lemma star_yProd_mul (l : List UVec) :
    star (yProd l) * yProd l = algebraMap ℝ Cl77 ((-1) ^ l.length * qProd l) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    have e : star (yProd (m :: l)) * yProd (m :: l) =
        -(star (yProd l) * (ι Q77 m.1 * ι Q77 m.1) * yProd l) := by
      rw [yProd_cons, star_mul, CliffordAlgebra.star_ι]; simp only [mul_assoc, neg_mul, mul_neg]
    rw [e, ι_sq_scalar, mul_assoc, Algebra.commutes, ← mul_assoc, ih, ← map_mul, ← map_neg,
      List.length_cons, qProd_cons, pow_succ]
    congr 1; ring

lemma yProd_mul_star (l : List UVec) :
    yProd l * star (yProd l) = algebraMap ℝ Cl77 ((-1) ^ l.length * qProd l) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    have e : yProd (m :: l) * star (yProd (m :: l)) =
        -(ι Q77 m.1 * (yProd l * star (yProd l)) * ι Q77 m.1) := by
      rw [yProd_cons, star_mul, CliffordAlgebra.star_ι]; simp only [mul_assoc, mul_neg]
    rw [e, ih, ← Algebra.commutes, mul_assoc, ι_sq_scalar, ← map_mul, ← map_neg, List.length_cons,
      qProd_cons, pow_succ]
    congr 1; ring

lemma yProd_mem_evenOdd (l : List UVec) : yProd l ∈ evenOdd Q77 (l.length : ZMod 2) := by
  induction l with
  | nil => exact Submodule.one_le.mp (one_le_evenOdd_zero Q77)
  | cons m l ih =>
    rw [yProd_cons, List.length_cons, Nat.cast_succ, add_comm]
    exact Submodule.mul_le.mp (evenOdd_mul_le Q77 _ _) _ (ι_mem_evenOdd_one Q77 m.1) _ ih

/-! ### Elements commuting with all vectors are scalars -/

lemma central_of_comm (z : Cl77) (hz : ∀ v, z * ι Q77 v = ι Q77 v * z) (y : Cl77) :
    z * y = y * z := by
  have hy : y ∈ Algebra.adjoin ℝ (Set.range (ι Q77)) := by rw [adjoin_range_ι]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨v, rfl⟩ := ha; exact hz v
  | algebraMap r => exact (Algebra.commutes r _).symm
  | add a b _ _ ha hb => rw [mul_add, add_mul, ha, hb]
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

lemma scalar_of_comm (z : Cl77) (hz : ∀ v, z * ι Q77 v = ι Q77 v * z) :
    ∃ c : ℝ, z = algebraMap ℝ Cl77 c := by
  have hc : cl77Equiv z ∈ Set.center M128 := by
    rw [Semigroup.mem_center_iff]
    intro m
    obtain ⟨y, rfl⟩ := cl77Equiv.surjective m
    rw [← map_mul, ← map_mul, central_of_comm z hz y]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, cl77Equiv.injective ?_⟩
  rw [← hc, AlgEquiv.commutes]
  rfl

/-! ### The spinor norm on the image -/

lemma neg_one_pow_even {n : ℕ} (h : (-1 : ℝ) ^ n = 1) : Even n :=
  (neg_one_pow_eq_one_iff_even (by norm_num)).mp h

/-- **Spinor norm**: if `vecRep x = r_{v₁} ⋯ r_{vₘ}` then `m` is even and `∏ Q vᵢ = 1`. -/
theorem vecRep_factor (x : Spin77) (l : List UVec)
    (h : ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = reflProd l) :
    Even l.length ∧ qProd l = 1 := by
  have he : Even l.length := by
    have hd := det_vecRep x
    rw [h, det_reflProd] at hd
    exact neg_one_pow_even hd
  refine ⟨he, ?_⟩
  set s := qProd l
  set Y := yProd l
  have hpow : ((-1 : ℝ) ^ l.length) = 1 := he.neg_one_pow
  have hYY : star Y * Y = algebraMap ℝ Cl77 s := by rw [star_yProd_mul, hpow, one_mul]
  have hss : s * s = 1 := qProd_sq l
  have hxx : star (x : Cl77) * x = 1 := spinGroup.star_mul_self_of_mem x.2
  -- `x ι w star x = ι (g w)` and `Y ι w star Y = s • ι (g w)`
  have hgx : ∀ w, (x : Cl77) * ι Q77 w * star (x : Cl77) = ι Q77 (reflProd l w) := fun w => by
    rw [← ι_vecL]; congr 1; exact congrArg (fun f : Module.End ℝ _ => f w) h
  have hgY : ∀ w, ι Q77 (reflProd l w) = s • (Y * ι Q77 w * star Y) := fun w => by
    rw [yProd_conj, smul_smul, hss, one_smul]
  set z := star Y * (x : Cl77)
  have hz : ∀ v, z * ι Q77 v = ι Q77 v * z := fun v => by
    have h1 : (x : Cl77) * ι Q77 v = ι Q77 (reflProd l v) * x := by
      rw [← hgx, mul_assoc _ (star _), hxx, mul_one]
    calc z * ι Q77 v = star Y * ((x : Cl77) * ι Q77 v) := mul_assoc _ _ _
      _ = star Y * (s • (Y * ι Q77 v * star Y)) * x := by rw [h1, hgY, ← mul_assoc]
      _ = s • ((star Y * Y) * ι Q77 v * (star Y * x)) := by
        rw [mul_smul_comm, smul_mul_assoc]; simp only [mul_assoc]
      _ = ι Q77 v * z := by
        rw [hYY, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, smul_smul,
          hss, one_smul]
  obtain ⟨c, hc⟩ := scalar_of_comm z hz
  have hzz : star z * z = algebraMap ℝ Cl77 s := by
    calc star z * z = star (x : Cl77) * (Y * star Y) * x := by
          simp only [z, star_mul, star_star, mul_assoc]
      _ = algebraMap ℝ Cl77 s := by
        rw [yProd_mul_star, hpow, one_mul, ← Algebra.commutes, mul_assoc, hxx, mul_one]
  rw [hc, show star (algebraMap ℝ Cl77 c) = algebraMap ℝ Cl77 c by
    rw [CliffordAlgebra.star_def, involute.commutes, reverse.commutes], ← map_mul] at hzz
  have hcs : c * c = s := (algebraMap ℝ Cl77).injective hzz
  rcases qProd_eq_one_or l with h1 | h1
  · exact h1
  · exfalso
    have : c * c = -1 := hcs.trans h1
    nlinarith [mul_self_nonneg c]

/-- Even products with `∏ Q vᵢ = 1` lift to `Spin(7,7)`. -/
theorem exists_vecRep (l : List UVec) (he : Even l.length) (hq : qProd l = 1) :
    ∃ x : Spin77, ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) =
      reflProd l := by
  have hpow : ((-1 : ℝ) ^ l.length) = 1 := he.neg_one_pow
  -- units
  let uOf : UVec → Cl77ˣ := fun m => ⟨ι Q77 m.1, Q77 m.1 • ι Q77 m.1,
    by rw [mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul, m.Q_sq, one_smul],
    by rw [smul_mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul, m.Q_sq, one_smul]⟩
  let U : Cl77ˣ := (l.map uOf).prod
  have hU' : ∀ l' : List UVec, (((l'.map uOf).prod : Cl77ˣ) : Cl77) = yProd l' := by
    intro l'
    induction l' with
    | nil => rfl
    | cons m l' ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih]; rfl
  have hU : (U : Cl77) = yProd l := hU' l
  have hUmem : U ∈ lipschitzGroup Q77 :=
    Subgroup.list_prod_mem _ fun u hu => by
      obtain ⟨m, -, rfl⟩ := List.mem_map.mp hu
      exact Subgroup.subset_closure ⟨m.1, rfl⟩
  have hev : (l.length : ZMod 2) = 0 := by
    obtain ⟨k, hk⟩ := he
    rw [hk, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have hmem : yProd l ∈ spinGroup Q77 := by
    refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨⟨U, hUmem, hU⟩, ?_⟩, ?_⟩
    · rw [Unitary.mem_iff, star_yProd_mul, yProd_mul_star, hpow, hq, one_mul, map_one]
      exact ⟨rfl, rfl⟩
    · have := yProd_mem_evenOdd l
      rw [hev] at this
      exact this
  refine ⟨⟨yProd l, hmem⟩, LinearMap.ext fun w => ι_injective ?_⟩
  show ι Q77 (vecL _ w) = _
  rw [ι_vecL]
  show yProd l * ι Q77 w * star (yProd l) = _
  rw [yProd_conj, hq, one_smul]

/-- **The image of `Spin(7,7)` is `SO⁺(7,7)`**: products of an even number of unit reflections
with `∏ Q vᵢ = 1` (the spinor-norm kernel inside `SO(7,7)`). -/
theorem range_vecRep (g : Module.End ℝ (Fin 14 → ℝ)) :
    (∃ x : Spin77, ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = g) ↔
      ∃ l : List UVec, g = reflProd l ∧ Even l.length ∧ qProd l = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨l, hl⟩ := isom_eq_reflProd _ (vecRep_isometry x)
    exact ⟨l, hl, vecRep_factor x l hl⟩
  · rintro ⟨l, rfl, he, hq⟩
    exact exists_vecRep l he hq

/-- **The spinor norm is well defined**: two factorisations of the same isometry into unit
reflections have the same `∏ Q vᵢ` (the parities agree automatically, by determinants). -/
theorem qProd_eq_of_reflProd_eq (l l' : List UVec) (h : reflProd l = reflProd l') :
    qProd l = qProd l' := by
  have hid : reflProd (l'.reverse ++ l) = 1 := by
    rw [reflProd_append, h, reflProd_reverse_mul]
  have h1 : ((vecRep 1 : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) =
      reflProd (l'.reverse ++ l) := by rw [hid, map_one]; rfl
  have hq := (vecRep_factor 1 _ h1).2
  rw [qProd_append, qProd_reverse] at hq
  have hs := qProd_sq l'
  calc qProd l = qProd l' * (qProd l' * qProd l) := by rw [← mul_assoc, hs, one_mul]
    _ = qProd l' := by rw [hq, mul_one]

/-- `e₀` (`Q = 1`) and `e₇` (`Q = −1`). -/
noncomputable def ue0 : UVec := ⟨eb 0, Or.inl (by simp [Q_eb])⟩
noncomputable def ue7 : UVec := ⟨eb 7, Or.inr (by simp [Q_eb])⟩

lemma qProd_g0 : qProd [ue0, ue7] = -1 := by
  rw [qProd_cons, qProd_cons, qProd_nil]
  show Q77 (eb 0) * (Q77 (eb 7) * 1) = -1
  rw [Q_eb, Q_eb]; norm_num

/-- `g₀ = r_{e₀} r_{e₇}`: `det = 1`, spinor norm `−1`. -/
noncomputable def g0 : Module.End ℝ (Fin 14 → ℝ) := reflProd [ue0, ue7]

lemma det_g0 : LinearMap.det g0 = 1 := by rw [g0, det_reflProd]; norm_num

/-- **`Spin(7,7)` does not surject onto `SO(7,7)`**: `g₀ ∈ SO(7,7)` is not in the image. -/
theorem g0_not_mem (x : Spin77) :
    ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) ≠ g0 := by
  intro h
  have := (vecRep_factor x _ h).2
  rw [qProd_g0] at this; norm_num at this

/-- **Index at most two**: every `det = 1` isometry `g` has `g` or `g₀ g` in the image of `Spin(7,7)`
(exactly one of them: `not_both`). -/
theorem mem_or_g0_mul_mem (g : Module.End ℝ (Fin 14 → ℝ)) (hg : IsIsom77 g)
    (hdet : LinearMap.det g = 1) :
    (∃ x : Spin77, ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = g) ∨
      ∃ x : Spin77, ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) =
        g0 * g := by
  obtain ⟨l, rfl⟩ := isom_eq_reflProd g hg
  have he : Even l.length := by rw [det_reflProd] at hdet; exact neg_one_pow_even hdet
  rcases qProd_eq_one_or l with hq | hq
  · exact Or.inl ((range_vecRep _).mpr ⟨l, rfl, he, hq⟩)
  · refine Or.inr ((range_vecRep _).mpr ⟨[ue0, ue7] ++ l, by rw [reflProd_append]; rfl, ?_, ?_⟩)
    · rw [List.length_append]; exact (by decide : Even [ue0, ue7].length).add he
    · rw [qProd_append, hq, qProd_g0]; norm_num

/-- **…and never both**: so `SO(7,7) = Im ⊔ g₀·Im` is a disjoint union (index exactly `2`). -/
theorem not_both (g : Module.End ℝ (Fin 14 → ℝ)) (x y : Spin77)
    (hx : ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = g)
    (hy : ((vecRep y : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = g0 * g) :
    False := by
  apply g0_not_mem (y * x⁻¹)
  refine LinearMap.ext fun v => ?_
  have hy' : ∀ w, vecRep y w = g0 (g w) := fun w => congrArg (fun f : Module.End ℝ _ => f w) hy
  have hx' : ∀ w, vecRep x w = g w := fun w => congrArg (fun f : Module.End ℝ _ => f w) hx
  show vecRep (y * x⁻¹) v = g0 v
  rw [map_mul, LinearEquiv.mul_apply, hy', ← hx', ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel,
    map_one]
  rfl

end GU.Spinor
