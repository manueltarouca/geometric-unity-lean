import GU.Spinor.PatiSalamGroup
import GU.Spinor.Pauli

/-!
# A maximal torus of (the double cover of) `U(3,2)` in `Spin(7,7)`, and hypercharge `U(1)_Y`

The five complex planes of `N^{6,4} ≅ ℂ^{3,2}` (`planes` in `Reductions.lean`) are `e₁e₂, e₃e₄, e₅e₆`
(positive) and `e₁₀e₁₁, e₁₂e₁₃` (negative). With `P_k = ι(e_a) ι(e_b)`:

* `P_sq : P_k² = −1`, `P_comm`: the `P_k` commute.
* `planeRot k s = cos s + sin s · P_k` lies in `Spin(7,7)` (`R_mem`: it is `ι(εa) ι(cos s · a + ε sin s · b)`),
  `R_add : planeRot k s · planeRot k t = planeRot k (s + t)`, `planeRot k (2π) = 1`, `planeRot k π = −1`: a circle subgroup.
* **`torus : (Fin 5 → Multiplicative ℝ) →* Spin(7,7)`**: the five commuting circles, a homomorphism
  from `ℝ⁵`. It factors through `U(1)⁵` with a finite kernel (`Rot π = −1` in every plane, so e.g.
  `(π,π,0,0,0) ↦ 1`; by hand the kernel from `U(1)⁵` is `(ℤ/2)⁴`, not formalised). Its image is a
  5-torus, the double cover of the maximal torus of `U(3,2) ⊂ SO(6,4)`.
* **`torus_le_centJfib`**: the torus commutes with `J = Σ_k P_k` and fixes the base (1,3) directions.
  The centraliser of `J` alone (`centJ`) also contains the base `Spin(1,3)`; `centJfib = centJ ∩
  (fixes the base)` is the group-level counterpart of `u(3,2) = centraliser of J in spin(6,4)`
  (`centralizer_spin64`), i.e. the preimage of `U(3,2)` in `Spin(6,4)` (a double cover).
  `cliffordRep Jt = toMat Jc` (same planes and orientation as `Reductions.lean`) is checked by hand,
  not stated.
* **`U1Y : Multiplicative ℝ →* Spin(7,7)`**: the hypercharge one-parameter subgroup
  `t ↦ torus(−2t,−2t,−2t,3t,3t)` (direction forced by `hypercharge_forced`), inside `centJfib`. By
  `U1Y_pi : U1Y π = 1` and `U1Y_half_ne : U1Y (π/2) ≠ 1` (by traces in `ℝ(128)`): it is periodic,
  so a circle, and not of period `π/2`. That the minimal period is exactly `π` is by hand.
-/

namespace GU.Spinor

open CliffordAlgebra Real

/-- Basis vectors. -/
noncomputable abbrev eb (i : Fin 14) : Fin 14 → ℝ := Pi.single i 1

lemma Q_eb (i : Fin 14) : Q77 (eb i) = if (i : ℕ) < 7 then 1 else -1 := by
  simp [eb, Q77, QuadraticMap.weightedSumSquares_apply, Pi.single_apply, Finset.sum_ite_eq']

lemma polar_eb {i j : Fin 14} (h : i ≠ j) : QuadraticMap.polar Q77 (eb i) (eb j) = 0 := by
  rw [polar_Q77]
  have : ∀ k, eb i k * eb j k = 0 := fun k => by
    simp only [eb, Pi.single_apply]
    split_ifs with h1 h2 <;> simp_all
  simp [this]

def pa : Fin 5 → Fin 14 := ![1, 3, 5, 10, 12]
def pb : Fin 5 → Fin 14 := ![2, 4, 6, 11, 13]

/-- The sign `Q(e_a) = Q(e_b) = ε_k` of plane `k`. -/
noncomputable def εp (k : Fin 5) : ℝ := Q77 (eb (pa k))

lemma εp_sq (k : Fin 5) : εp k * εp k = 1 := by
  fin_cases k <;> simp [εp, Q_eb, pa]

lemma Qb_eq (k : Fin 5) : Q77 (eb (pb k)) = εp k := by
  fin_cases k <;> simp [εp, Q_eb, pa, pb]

lemma pa_ne_pb (k : Fin 5) : pa k ≠ pb k := by fin_cases k <;> decide

/-- `P_k = e_a e_b`. -/
noncomputable def planeP (k : Fin 5) : Cl77 := ι Q77 (eb (pa k)) * ι Q77 (eb (pb k))

lemma P_sq (k : Fin 5) : planeP k * planeP k = -1 := by
  rw [planeP, pair_sq (polar_eb (pa_ne_pb k).symm), Qb_eq, εp, ← εp, εp_sq, map_neg, map_one]

lemma P_comm (k l : Fin 5) : planeP k * planeP l = planeP l * planeP k := by
  by_cases hkl : k = l
  · rw [hkl]
  · have hd : ∀ (i : Fin 14), i = pa l ∨ i = pb l → i ≠ pa k ∧ i ≠ pb k := by
      revert k l; decide
    have h1 := pair_comm (polar_eb (hd _ (Or.inl rfl)).1.symm) (polar_eb (hd _ (Or.inl rfl)).2.symm)
    have h2 := pair_comm (polar_eb (hd _ (Or.inr rfl)).1.symm) (polar_eb (hd _ (Or.inr rfl)).2.symm)
    simp only [planeP]
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

/-- The rotation by angle `s` in plane `k`. -/
noncomputable def planeRot (k : Fin 5) (s : ℝ) : Cl77 := algebraMap ℝ Cl77 (cos s) + sin s • planeP k

lemma R_add (k : Fin 5) (s t : ℝ) : planeRot k s * planeRot k t = planeRot k (s + t) := by
  simp only [planeRot, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one,
    P_sq, cos_add, sin_add]
  module

lemma R_zero (k : Fin 5) : planeRot k 0 = 1 := by simp [planeRot]

lemma R_eq (k : Fin 5) (s : ℝ) :
    planeRot k s = ι Q77 (εp k • eb (pa k)) * ι Q77 (cos s • eb (pa k) + (εp k * sin s) • eb (pb k)) := by
  have hq : ι Q77 (eb (pa k)) * ι Q77 (eb (pa k)) = algebraMap ℝ Cl77 (εp k) := by
    rw [ι_sq_scalar]; rfl
  simp only [map_smul, map_add, mul_add, smul_mul_smul_comm, hq, planeRot, planeP]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  simp only [smul_smul]
  rw [show εp k * cos s * εp k = cos s by rw [mul_comm, ← mul_assoc, εp_sq, one_mul],
    show εp k * (εp k * sin s) = sin s by rw [← mul_assoc, εp_sq, one_mul]]

lemma R_mem (k : Fin 5) (s : ℝ) : planeRot k s ∈ spinGroup Q77 := by
  rw [R_eq]
  apply pair_mem
  have h1 : Q77 (εp k • eb (pa k)) = εp k := by
    rw [QuadraticMap.map_smul, ← εp, εp_sq, one_smul]
  have h2 : Q77 (cos s • eb (pa k) + (εp k * sin s) • eb (pb k)) = εp k := by
    rw [QuadraticMap.map_add Q77, QuadraticMap.map_smul, QuadraticMap.map_smul, Qb_eq,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, polar_eb (pa_ne_pb k)]
    rw [← εp]
    have := sin_sq_add_cos_sq s
    have he := εp_sq k
    simp only [smul_eq_mul, mul_zero, add_zero]
    linear_combination (εp k) * this + (sin s ^ 2 * εp k) * he
  rw [h1, h2, εp_sq]

lemma Rot_comm (k l : Fin 5) (s t : ℝ) : planeRot k s * planeRot l t = planeRot l t * planeRot k s := by
  simp only [planeRot, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_smul_comm, one_mul,
    mul_one, P_comm k l]
  module

lemma Rot_two_pi (k : Fin 5) : planeRot k (2 * π) = 1 := by simp [planeRot]
lemma Rot_pi (k : Fin 5) : planeRot k π = -1 := by simp [planeRot, Algebra.algebraMap_eq_smul_one]

/-- The circle in plane `k`, as a homomorphism into `Spin(7,7)`. -/
noncomputable def planeCircle (k : Fin 5) : Multiplicative ℝ →* Spin77 where
  toFun s := ⟨planeRot k (Multiplicative.toAdd s), R_mem k _⟩
  map_one' := Subtype.ext (R_zero k)
  map_mul' s t := Subtype.ext (by
    show planeRot k (Multiplicative.toAdd s + Multiplicative.toAdd t) = planeRot k _ * planeRot k _
    rw [R_add])

/-- **The torus `U(1)⁵ → Spin(7,7)`.** -/
theorem circle_comm : Pairwise fun i j => ∀ x y : Multiplicative ℝ, Commute (planeCircle i x) (planeCircle j y) :=
  fun k l _ _ _ => Subtype.ext (Rot_comm k l _ _)

noncomputable def torus : (Fin 5 → Multiplicative ℝ) →* Spin77 :=
  MonoidHom.noncommPiCoprod planeCircle circle_comm

/-- The complex structure `J = Σ P_k`. -/
noncomputable def Jt : Cl77 := ∑ k : Fin 5, planeP k

lemma Rot_comm_J (k : Fin 5) (s : ℝ) : planeRot k s * Jt = Jt * planeRot k s := by
  have h : ∀ l, planeRot k s * planeP l = planeP l * planeRot k s := fun l => by
    simp only [planeRot, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, P_comm k l]
  rw [Jt, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => h l

/-- The centraliser of `J` in `Spin(7,7)` (contains the base `Spin(1,3)` too; see `centJfib`). -/
def centJ : Subgroup Spin77 where
  carrier := {x | (x : Cl77) * Jt = Jt * x}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    show (x : Cl77) * y * Jt = Jt * (x * y)
    rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  inv_mem' {x} hx := by
    show ((x⁻¹ : Spin77) : Cl77) * Jt = Jt * (x⁻¹ : Spin77)
    have h1 : ((x⁻¹ : Spin77) : Cl77) * x = 1 := by rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
    have h2 : (x : Cl77) * (x⁻¹ : Spin77) = 1 := by rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
    calc ((x⁻¹ : Spin77) : Cl77) * Jt = (x⁻¹ : Spin77) * (Jt * (x * (x⁻¹ : Spin77))) := by
          rw [h2, mul_one]
      _ = (x⁻¹ : Spin77) * (x * Jt) * (x⁻¹ : Spin77) := by
          rw [← mul_assoc Jt, ← hx]; simp only [mul_assoc]
      _ = Jt * (x⁻¹ : Spin77) := by rw [← mul_assoc, h1, one_mul]

/-- The torus lies in the centraliser of `J`. -/
theorem torus_le_centJ : torus.range ≤ centJ := by
  rw [torus, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun k => ?_
  rintro _ ⟨s, rfl⟩
  exact Rot_comm_J k _

/-- Hypercharge direction `(−2,−2,−2,3,3)` (`hypercharge_forced`). -/
def ycoef : Fin 5 → ℝ := ![-2, -2, -2, 3, 3]

/-- **`U(1)_Y`**: the hypercharge circle `t ↦ torus(−2t,−2t,−2t,3t,3t)`. -/
noncomputable def U1Y : Multiplicative ℝ →* Spin77 :=
  torus.comp
    { toFun := fun t k => Multiplicative.ofAdd (ycoef k * Multiplicative.toAdd t)
      map_one' := by funext k; simp
      map_mul' := fun s t => by funext k; simp [mul_add] }

theorem U1Y_le_centJ (t : Multiplicative ℝ) : U1Y t ∈ centJ :=
  torus_le_centJ ⟨fun k => Multiplicative.ofAdd (ycoef k * Multiplicative.toAdd t), rfl⟩

/-- Each plane rotation by `π` is `−1`: the circles really are `U(1)`s through `−1`. -/
theorem circle_pi (k : Fin 5) : ((planeCircle k (Multiplicative.ofAdd π) : Spin77) : Cl77) = -1 := Rot_pi k

def S10 : Finset (Fin 14) := {1, 2, 3, 4, 5, 6, 10, 11, 12, 13}

/-- The centraliser of `J` among elements fixing the base directions: the group-level `U(3,2)`
(double cover). -/
def centJfib : Subgroup Spin77 := centJ ⊓ fixSub (perpOf S10)

lemma planeRot_fix (k : Fin 5) (s : ℝ) : (planeCircle k (Multiplicative.ofAdd s)) ∈ fixSub (perpOf S10) := by
  apply gens_fix (q := εp k)
  have hS : ∀ i : Fin 14, i = pa k ∨ i = pb k → i ∈ S10 := by
    revert k; decide
  have hsupp : ∀ (i : Fin 14), i ∈ S10 → ∀ v : Fin 14 → ℝ, SuppIn {i} v → SuppIn S10 v :=
    fun i hi v hv j hj => hv j (fun h => hj (by rw [Finset.mem_singleton.mp h]; exact hi))
  have ha : SuppIn S10 (eb (pa k)) := fun j hj => by
    have : j ≠ pa k := fun h => hj (h ▸ hS _ (Or.inl rfl))
    simp [eb, this]
  have hb : SuppIn S10 (eb (pb k)) := fun j hj => by
    have : j ≠ pb k := fun h => hj (h ▸ hS _ (Or.inr rfl))
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

/-- **The torus lies in `centJfib`**: commutes with `J`, fixes the base. -/
theorem torus_le_centJfib : torus.range ≤ centJfib := by
  rw [torus, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun k => ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨Rot_comm_J k _, planeRot_fix k (Multiplicative.toAdd s)⟩

theorem U1Y_le_centJfib (t : Multiplicative ℝ) : U1Y t ∈ centJfib :=
  torus_le_centJfib ⟨fun k => Multiplicative.ofAdd (ycoef k * Multiplicative.toAdd t), rfl⟩

/-- The torus is the ordered product of its five circles. -/
lemma torus_eq (f : Fin 5 → Multiplicative ℝ) :
    torus f = planeCircle 0 (f 0) * planeCircle 1 (f 1) * planeCircle 2 (f 2) * planeCircle 3 (f 3) *
      planeCircle 4 (f 4) := by
  have hf : f = Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) * Pi.mulSingle 2 (f 2) *
      Pi.mulSingle 3 (f 3) * Pi.mulSingle 4 (f 4) := by
    funext k; fin_cases k <;> simp
  conv_lhs => rw [hf]
  simp only [map_mul, torus, MonoidHom.noncommPiCoprod_mulSingle]

lemma U1Y_val (t : ℝ) : ((U1Y (Multiplicative.ofAdd t) : Spin77) : Cl77) =
    planeRot 0 (-2 * t) * planeRot 1 (-2 * t) * planeRot 2 (-2 * t) * planeRot 3 (3 * t) *
      planeRot 4 (3 * t) := by
  show ((torus _ : Spin77) : Cl77) = _
  rw [torus_eq]
  simp [planeCircle, ycoef]

/-- **`U(1)_Y` closes up after `π`**: `U1Y π = 1`. -/
theorem U1Y_pi : ((U1Y (Multiplicative.ofAdd π) : Spin77) : Cl77) = 1 := by
  rw [U1Y_val]
  have h2 : ∀ k, planeRot k (-2 * π) = 1 := fun k => by
    simp [planeRot, show -2 * π = -(2 * π) by ring]
  have h3 : ∀ k, planeRot k (3 * π) = -1 := fun k => by
    have : 3 * π = π + 2 * π := by ring
    simp [planeRot, this, Algebra.algebraMap_eq_smul_one]
  rw [h2, h2, h2, h3, h3]; simp

/-- **…and not before `π/2`**: `U1Y (π/2) ≠ 1` (it equals `−P₄P₅`). -/
theorem U1Y_half_ne : ((U1Y (Multiplicative.ofAdd (π / 2)) : Spin77) : Cl77) ≠ 1 := by
  rw [U1Y_val]
  have h2 : ∀ k, planeRot k (-2 * (π / 2)) = -1 := fun k => by
    simp [planeRot, show -2 * (π / 2) = -π by ring, Algebra.algebraMap_eq_smul_one]
  have h3 : ∀ k, planeRot k (3 * (π / 2)) = -planeP k := fun k => by
    have hc : cos (3 * (π / 2)) = 0 := by
      rw [show 3 * (π / 2) = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]
    have hs : sin (3 * (π / 2)) = -1 := by
      rw [show 3 * (π / 2) = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
    simp [planeRot, hc, hs]
  rw [h2, h2, h2, h3, h3]
  intro h
  have h' : planeP 3 * planeP 4 = -1 := by
    have e : (-1 : Cl77) * -1 * -1 * -planeP 3 * -planeP 4 = -(planeP 3 * planeP 4) := by
      simp only [neg_mul, mul_neg, neg_neg, one_mul]
    rw [e] at h
    rw [← neg_neg (planeP 3 * planeP 4), h]
  have hg : ∀ i, gammaMap (eb i) = gamma (gen i) := fun i => by
    simp [gammaMap, eb, Pi.single_apply]
  have hrep : cliffordRep (planeP 3 * planeP 4) = (gprod [gen 10, gen 11, gen 12, gen 13]).toMat := by
    rw [toMat_gprod]
    simp [planeP, pa, pb, hg, mul_assoc]
  have htr : (gprod [gen 10, gen 11, gen 12, gen 13]).tr = 0 := by decide
  have := congrArg (fun z => Matrix.trace (cliffordRep z)) h'
  simp only [hrep, PString.trace_toMat, htr, map_neg, map_one, Matrix.trace_neg, Matrix.trace_one] at this
  norm_num [Idx] at this

end GU.Spinor
