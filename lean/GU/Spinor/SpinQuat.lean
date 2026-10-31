import GU.Spinor.SpinIso

/-!
# `Spin(0,4) ≅ Sp(1) × Sp(1)`: the Pati–Salam `Spin4` as pairs of unit quaternions

`Cl(Q₄)` (with `Q₄ = −|v|²`) is represented on `ℍ²`: `γ(v) = [[0, v̂], [−v̄̂, 0]]`, where
`v̂ = v₀ + v₁ i + v₂ j + v₃ k`, so `γ(v)² = −|v|² = Q₄(v)` (`γ4 = CliffordAlgebra.lift`). Even
elements are diagonal and `γ(star x) = γ(x)ᴴ`, so `x ↦ (γ(x)₀₀, γ(x)₁₁)` is a homomorphism
`spinQ : spinGroup Q₄ →* Sp(1) × Sp(1)` (`Sp(1) = unitary ℍ`, the unit quaternions).
-/

namespace GU.Spinor

open CliffordAlgebra Matrix Quaternion

/-- `ℝ⁴ → ℍ`. -/
noncomputable def toH : (Fin 4 → ℝ) →ₗ[ℝ] ℍ[ℝ] where
  toFun v := ⟨v 0, v 1, v 2, v 3⟩
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp

lemma toH_injective : Function.Injective toH := fun v w h => by
  funext k
  have h0 := congrArg (·.re) h
  have h1 := congrArg (·.imI) h
  have h2 := congrArg (·.imJ) h
  have h3 := congrArg (·.imK) h
  simp only [toH, LinearMap.coe_mk, AddHom.coe_mk] at h0 h1 h2 h3
  fin_cases k <;> assumption

lemma normSq_toH (v : Fin 4 → ℝ) : normSq (toH v) = -Q4 v := by
  rw [normSq_def']
  simp [toH, Q4, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four]
  ring

abbrev M2H := Matrix (Fin 2) (Fin 2) ℍ[ℝ]

/-- `γ(v) = [[0, v̂], [−v̄̂, 0]]`. -/
noncomputable def gH : (Fin 4 → ℝ) →ₗ[ℝ] M2H where
  toFun v := !![0, toH v; -star (toH v), 0]
  map_add' v w := Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c v := Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

lemma gH_sq (v : Fin 4 → ℝ) : gH v * gH v = algebraMap ℝ M2H (Q4 v) := by
  have h1 : toH v * star (toH v) = ((-Q4 v : ℝ) : ℍ[ℝ]) := by rw [self_mul_star, normSq_toH]
  have h2 : star (toH v) * toH v = ((-Q4 v : ℝ) : ℍ[ℝ]) := by rw [star_mul_self, normSq_toH]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [gH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply, h1, h2]

/-- The representation `γ : Cl(Q₄) → M₂(ℍ)`. -/
noncomputable def γ4 : CliffordAlgebra Q4 →ₐ[ℝ] M2H := CliffordAlgebra.lift Q4 ⟨gH, gH_sq⟩

@[simp] lemma γ4_ι (v : Fin 4 → ℝ) : γ4 (ι Q4 v) = gH v := CliffordAlgebra.lift_ι_apply _ _ _

/-- Diagonal `2 × 2` quaternion matrices. -/
def IsDiag2 (A : M2H) : Prop := A 0 1 = 0 ∧ A 1 0 = 0

lemma isDiag2_mul {A B : M2H} (hA : IsDiag2 A) (hB : IsDiag2 B) : IsDiag2 (A * B) := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1, hA.2, hB.1, hB.2]

lemma isDiag2_gH_mul (a b : Fin 4 → ℝ) : IsDiag2 (gH a * gH b) := by
  constructor <;> simp [gH, Matrix.mul_apply, Fin.sum_univ_two]

/-- Even elements are represented by diagonal matrices. -/
lemma γ4_even {x : CliffordAlgebra Q4} (hx : x ∈ evenOdd Q4 0) : IsDiag2 (γ4 x) := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    constructor <;> simp [Matrix.algebraMap_matrix_apply]
  | add x y _ _ hx hy =>
    rw [map_add]; exact ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, γ4_ι, γ4_ι]
    exact isDiag2_mul (isDiag2_gH_mul m₁ m₂) hx

lemma diag_mul_00 {A B : M2H} (hA : IsDiag2 A) : (A * B) 0 0 = A 0 0 * B 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1]

lemma diag_mul_11 {A B : M2H} (hA : IsDiag2 A) : (A * B) 1 1 = A 1 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hA.2]

lemma star_algebraMap_H (r : ℝ) : star (algebraMap ℝ M2H r) = algebraMap ℝ M2H r := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.star_apply, Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `γ(star x) = γ(x)ᴴ`. -/
lemma γ4_star (x : CliffordAlgebra Q4) : γ4 (star x) = star (γ4 x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [star_algebraMap_Cl, AlgHom.commutes, star_algebraMap_H]
  | ι v =>
    rw [CliffordAlgebra.star_ι, map_neg, γ4_ι]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gH, Matrix.star_apply]
  | mul a b ha hb => rw [star_mul, map_mul, map_mul, ha, hb, star_mul]
  | add a b ha hb => rw [star_add, map_add, map_add, ha, hb, star_add]

lemma diag_star_mul {A : M2H} (hA : IsDiag2 A) (h : star A * A = 1) (k : Fin 2) :
    star (A k k) * A k k = 1 := by
  have := congrFun (congrFun h k) k
  fin_cases k <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hA.1, hA.2] using this

lemma diag_mul_star {A : M2H} (hA : IsDiag2 A) (h : A * star A = 1) (k : Fin 2) :
    A k k * star (A k k) = 1 := by
  have := congrFun (congrFun h k) k
  fin_cases k <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hA.1, hA.2] using this

lemma γ4_spin_unitary {x : CliffordAlgebra Q4} (hx : x ∈ spinGroup Q4) (k : Fin 2) :
    γ4 x k k ∈ unitary ℍ[ℝ] := by
  have hd := γ4_even (spinGroup.mem_iff.mp hx).2
  have h1 : star (γ4 x) * γ4 x = 1 := by
    rw [← γ4_star, ← map_mul, spinGroup.star_mul_self_of_mem hx, map_one]
  have h2 : γ4 x * star (γ4 x) = 1 := by
    rw [← γ4_star, ← map_mul, spinGroup.mul_star_self_of_mem hx, map_one]
  exact Unitary.mem_iff.mpr ⟨diag_star_mul hd h1 k, diag_mul_star hd h2 k⟩

/-- **`spinGroup Q₄ →* Sp(1) × Sp(1)`**, `x ↦ (γ(x)₀₀, γ(x)₁₁)`. -/
noncomputable def spinQ : spinGroup Q4 →* unitary ℍ[ℝ] × unitary ℍ[ℝ] where
  toFun x := (⟨γ4 x 0 0, γ4_spin_unitary x.2 0⟩, ⟨γ4 x 1 1, γ4_spin_unitary x.2 1⟩)
  map_one' := by ext <;> simp
  map_mul' x y := by
    have hd := γ4_even (spinGroup.mem_iff.mp x.2).2
    ext <;> simp [map_mul, diag_mul_00 hd, diag_mul_11 hd]

/-! ### Injectivity -/

lemma γ4_eq_one {x : CliffordAlgebra Q4} (hd : IsDiag2 (γ4 x)) (h0 : γ4 x 0 0 = 1)
    (h1 : γ4 x 1 1 = 1) : γ4 x = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hd.1, hd.2]

/-- If `γ(x) = 1` for `x ∈ spinGroup Q₄`, then `x` acts trivially on `W4`. -/
lemma vecRep_block_fix (x : spinGroup Q4) (hx : γ4 (x : CliffordAlgebra Q4) = 1) (v : Fin 4 → ℝ) :
    vecRep (spin4Hom x) (f4L v) = f4L v := by
  set y := spin4Hom x
  set u := vecRep y (f4L v)
  have hout := (spin4_iff y).mp (spin4Hom_mem x)
  have hsu : SuppIn S4 u := supp_of_polar u fun j hj => by
    have hj' : (j : ℕ) < 10 := (by decide : ∀ j : Fin 14, j ∉ S4 → (j : ℕ) < 10) j hj
    rw [← hout.2.2 j hj, vecRep_polar, polar_eb_right, f4L_low v hj']; ring
  have hιu : ι Q77 u = Φ4 ((x : CliffordAlgebra Q4) * ι Q4 v * star (x : CliffordAlgebra Q4)) := by
    show ι Q77 (vecL _ _) = _
    rw [ι_vecL, map_mul, map_mul, Φ4_ι, Φ4_star]; rfl
  have hw : (x : CliffordAlgebra Q4) * ι Q4 v * star (x : CliffordAlgebra Q4) = ι Q4 (res4 u) := by
    apply Φ4_injective
    rw [← hιu, Φ4_ι, f4L_res4 hsu]
  have hγ := congrArg γ4 hw
  rw [map_mul, map_mul, γ4_star, hx, star_one, one_mul, mul_one, γ4_ι, γ4_ι] at hγ
  have h01 := congrFun (congrFun hγ 0) 1
  simp only [gH, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01
  have hv : v = res4 u := toH_injective (by simpa using h01)
  rw [hv, f4L_res4 hsu]

/-- **`spinQ` is injective.** -/
theorem spinQ_injective : Function.Injective spinQ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hd := γ4_even (spinGroup.mem_iff.mp x.2).2
  have h0 : γ4 (x : CliffordAlgebra Q4) 0 0 = 1 := congrArg Subtype.val (congrArg Prod.fst hx)
  have h1 : γ4 (x : CliffordAlgebra Q4) 1 1 = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
  have hγ := γ4_eq_one hd h0 h1
  have hout := (spin4_iff (spin4Hom x)).mp (spin4Hom_mem x)
  have hid : ∀ j, vecRep (spin4Hom x) (eb j) = eb j := fun j => by
    by_cases hj : j ∈ S4
    · have hk : ∃ k : Fin 4, emb4 k = j := by revert hj; revert j; decide
      obtain ⟨k, rfl⟩ := hk
      rw [← f4L_single, vecRep_block_fix x hγ]
    · exact hout.2.2 j hj
  have hker : spin4Hom x ∈ vecRep.ker := by
    rw [MonoidHom.mem_ker]
    exact LinearEquiv.toLinearMap_injective ((Pi.basisFun ℝ (Fin 14)).ext fun j => by
      simpa [Pi.basisFun_apply] using hid j)
  rcases (mem_ker_iff _).mp hker with h | h
  · apply Subtype.ext
    apply Φ4_injective
    show Φ4 (x : CliffordAlgebra Q4) = Φ4 1
    rw [map_one]
    exact congrArg Subtype.val h
  · exfalso
    have e : Φ4 (x : CliffordAlgebra Q4) = Φ4 (-1) := by
      rw [map_neg, map_one]; exact congrArg Subtype.val h
    have := congrFun (congrFun (congrArg γ4 (Φ4_injective e)) 0) 0
    rw [hγ, map_neg, map_one] at this
    have h1 := congrArg (·.re) this
    simp at h1
    norm_num at h1

/-! ### Quaternion lemmas -/

/-- `ℍ → ℝ⁴`, inverse of `toH`. -/
noncomputable def fromH : ℍ[ℝ] →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun q := ![q.re, q.imI, q.imJ, q.imK]
  map_add' a b := by funext k; fin_cases k <;> simp
  map_smul' c a := by funext k; fin_cases k <;> simp

@[simp] lemma toH_fromH (q : ℍ[ℝ]) : toH (fromH q) = q := by ext <;> rfl
@[simp] lemma fromH_toH (v : Fin 4 → ℝ) : fromH (toH v) = v := by
  funext k; fin_cases k <;> rfl

/-- Unit quaternions have unit square roots. -/
lemma exists_sqrt (p : ℍ[ℝ]) (hp : normSq p = 1) : ∃ s : ℍ[ℝ], normSq s = 1 ∧ s * s = p := by
  by_cases hm : p = -1
  · refine ⟨⟨0, 1, 0, 0⟩, by rw [normSq_def']; norm_num, ?_⟩
    rw [hm]; ext <;> simp
  · have hn : normSq p = p.re ^ 2 + p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 := normSq_def' p
    have hre : p.re ≠ -1 := by
      intro h
      apply hm
      have hi : p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 0 := by rw [h] at hn; linarith
      have h1 : p.imI = 0 := by nlinarith [sq_nonneg p.imI, sq_nonneg p.imJ, sq_nonneg p.imK]
      have h2 : p.imJ = 0 := by nlinarith [sq_nonneg p.imI, sq_nonneg p.imJ, sq_nonneg p.imK]
      have h3 : p.imK = 0 := by nlinarith [sq_nonneg p.imI, sq_nonneg p.imJ, sq_nonneg p.imK]
      ext <;> simp [h, h1, h2, h3]
    have hge : -1 ≤ p.re := by nlinarith [sq_nonneg p.imI, sq_nonneg p.imJ, sq_nonneg p.imK]
    have hpos : 0 < 2 + 2 * p.re := by
      rcases lt_or_eq_of_le hge with h | h
      · linarith
      · exact absurd h.symm hre
    set c : ℝ := (Real.sqrt (2 + 2 * p.re))⁻¹
    have hcc : c * c * (2 + 2 * p.re) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    have hS : p.re ^ 2 + p.imI ^ 2 + p.imJ ^ 2 + p.imK ^ 2 = 1 := hn.symm.trans hp
    have key : (1 + p) * (1 + p) = (2 + 2 * p.re) • p := by
      ext <;> simp <;> nlinarith [hS]
    have hn1 : normSq (1 + p) = 2 + 2 * p.re := by
      rw [normSq_def']; simp; nlinarith [hS]
    refine ⟨c • (1 + p), ?_, ?_⟩
    · rw [normSq_smul, hn1]; linarith [hcc]
    · rw [smul_mul_smul_comm, key, smul_smul, hcc, one_smul]

lemma normSq_one_of_unitary {p : ℍ[ℝ]} (hp : p ∈ unitary ℍ[ℝ]) : normSq p = 1 := by
  have h := (Unitary.mem_iff.mp hp).1
  rw [star_mul_self] at h
  have := congrArg (·.re) h
  simpa using this

/-- **Uniqueness**: if `a q b̄ = p q r̄` for all `q` (all unit), then `(a, b) = ±(p, r)`. -/
lemma quat_pair_unique {a b p r : ℍ[ℝ]} (ha : normSq a = 1) (hb : normSq b = 1)
    (hp : normSq p = 1) (hr : normSq r = 1) (h : ∀ q, a * q * star b = p * q * star r) :
    (a = p ∧ b = r) ∨ (a = -p ∧ b = -r) := by
  have hpp : star p * p = 1 := by rw [star_mul_self, hp]; simp
  have hrr : r * star r = 1 := by rw [self_mul_star, hr]; simp
  have hpp' : p * star p = 1 := by rw [self_mul_star, hp]; simp
  have hrr' : star r * r = 1 := by rw [star_mul_self, hr]; simp
  set c := star p * a
  set d := star r * b
  have hc : ∀ q, c * q * star d = q := fun q => by
    have := h q
    calc c * q * star d = star p * (a * q * star b) * r := by
          simp only [c, d, star_mul, star_star, mul_assoc]
      _ = star p * (p * q * star r) * r := by rw [this]
      _ = q := by
          rw [← mul_assoc, ← mul_assoc, hpp, one_mul, mul_assoc, hrr', mul_one]
  have hdd : star d * d = 1 := by
    rw [star_mul_self]
    simp only [d, map_mul, normSq_star, hr, hb, one_mul]; simp
  have hcd : c = d := by
    have h1 := hc 1
    rw [mul_one] at h1
    calc c = c * (star d * d) := by rw [hdd, mul_one]
      _ = d := by rw [← mul_assoc, h1, one_mul]
  have hcomm : ∀ q, c * q = q * c := fun q => by
    have hcc : star c * c = 1 := by rw [hcd]; exact hdd
    have hc' := hc q
    rw [← hcd] at hc'
    calc c * q = c * q * (star c * c) := by rw [hcc, mul_one]
      _ = (c * q * star c) * c := by simp only [mul_assoc]
      _ = q * c := by rw [hc']
  have hI := hcomm ⟨0, 1, 0, 0⟩
  have hJ := hcomm ⟨0, 0, 1, 0⟩
  have e1 := congrArg (·.imJ) hI
  have e2 := congrArg (·.imK) hI
  have e3 := congrArg (·.imI) hJ
  have e4 := congrArg (·.imK) hJ
  simp at e1 e2 e3 e4
  have hcI : c.imI = 0 := by linarith
  have hcJ : c.imJ = 0 := by linarith
  have hcK : c.imK = 0 := by linarith
  have hcn : normSq c = 1 := by
    simp only [c, map_mul, normSq_star, hp, ha, one_mul]
  rw [normSq_def', hcI, hcJ, hcK] at hcn
  have hre : c.re = 1 ∨ c.re = -1 := by
    have : c.re * c.re = 1 := by nlinarith
    exact mul_self_eq_one_iff.mp this
  have hca : a = p * c := by simp only [c, ← mul_assoc, hpp', one_mul]
  have hdb : b = r * d := by simp only [d, ← mul_assoc, hrr, one_mul]
  rcases hre with h1 | h1
  · left
    have : c = 1 := by ext <;> simp [h1, hcI, hcJ, hcK]
    exact ⟨by rw [hca, this, mul_one], by rw [hdb, ← hcd, this, mul_one]⟩
  · right
    have : c = -1 := by ext <;> simp [h1, hcI, hcJ, hcK]
    exact ⟨by rw [hca, this, mul_neg_one], by rw [hdb, ← hcd, this, mul_neg_one]⟩

/-! ### Block maps `T_{p,r}` -/

lemma res4_f4L (v : Fin 4 → ℝ) : res4 (f4L v) = v := by
  funext k
  simp only [res4, f4L, LinearMap.coe_mk, AddHom.coe_mk, emb4]
  rw [dif_pos (by simp)]; congr 1

/-- `res4` as a linear map. -/
noncomputable def res4L : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := res4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma res4L_apply (u : Fin 14 → ℝ) : res4L u = res4 u := rfl

/-- `u ↦ u` off `W4`, `v̂ ↦ p v̂ r̄` on `W4`. -/
noncomputable def Tmap (p r : ℍ[ℝ]) : Module.End ℝ (Fin 14 → ℝ) :=
  LinearMap.id - f4L ∘ₗ res4L +
    f4L ∘ₗ fromH ∘ₗ (LinearMap.mulLeft ℝ p ∘ₗ LinearMap.mulRight ℝ (star r)) ∘ₗ toH ∘ₗ res4L

lemma Tmap_apply (p r : ℍ[ℝ]) (u : Fin 14 → ℝ) :
    Tmap p r u = u - f4L (res4 u) + f4L (fromH (p * toH (res4 u) * star r)) := by
  simp only [Tmap, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, res4L_apply, mul_assoc]

lemma res4_Tmap (p r : ℍ[ℝ]) (u : Fin 14 → ℝ) :
    res4 (Tmap p r u) = fromH (p * toH (res4 u) * star r) := by
  rw [Tmap_apply]
  have hl : ∀ a b : Fin 14 → ℝ, res4 (a + b) = res4 a + res4 b := fun _ _ => rfl
  have hs : ∀ a b : Fin 14 → ℝ, res4 (a - b) = res4 a - res4 b := fun _ _ => rfl
  rw [hl, hs, res4_f4L, res4_f4L, sub_self, zero_add]

lemma Tmap_mul (p r p' r' : ℍ[ℝ]) : Tmap p r * Tmap p' r' = Tmap (p * p') (r * r') := by
  refine LinearMap.ext fun u => ?_
  rw [Module.End.mul_apply, Tmap_apply, res4_Tmap, Tmap_apply, Tmap_apply, toH_fromH, star_mul]
  simp only [mul_assoc]
  abel

lemma Tmap_off (p r : ℍ[ℝ]) {j : Fin 14} (hj : j ∉ S4) : Tmap p r (eb j) = eb j := by
  have h0 : res4 (eb j) = 0 := by
    funext k
    have hk : ∀ k : Fin 4, emb4 k ∈ S4 := by decide
    have : emb4 k ≠ j := fun e => hj (e ▸ hk k)
    simp [res4, eb, this]
  rw [Tmap_apply, h0]
  simp

lemma Tmap_f4L (p r : ℍ[ℝ]) (v : Fin 4 → ℝ) :
    Tmap p r (f4L v) = f4L (fromH (p * toH v * star r)) := by
  rw [Tmap_apply, res4_f4L]; abel

/-- Off-block part `u − f₄(res₄ u)` is orthogonal to the block. -/
lemma polar_off_block (u : Fin 14 → ℝ) (w : Fin 4 → ℝ) :
    QuadraticMap.polar Q77 (u - f4L (res4 u)) (f4L w) = 0 := by
  rw [polar_Q77]
  have : ∀ i : Fin 14, (u - f4L (res4 u)) i * f4L w i = 0 := fun i => by
    by_cases hi : 10 ≤ (i : ℕ)
    · have : (u - f4L (res4 u)) i = 0 := by
        simp only [Pi.sub_apply, f4L, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left_iff, dif_pos hi, res4, emb4]
        rw [sub_eq_zero]; congr 1; ext; simp; omega
      rw [this, zero_mul]
    · rw [f4L_low w (by omega), mul_zero]
  simp only [this, mul_zero, Finset.sum_const_zero]

lemma Tmap_isometry {p r : ℍ[ℝ]} (hp : normSq p = 1) (hr : normSq r = 1) : IsIsom77 (Tmap p r) := by
  intro u
  have hsplit : ∀ w : Fin 4 → ℝ, Q77 (u - f4L (res4 u) + f4L w) = Q77 (u - f4L (res4 u)) + Q4 w :=
    fun w => by rw [QuadraticMap.map_add Q77, polar_off_block, add_zero, Q77_f4L]
  have hu : u = u - f4L (res4 u) + f4L (res4 u) := by abel
  rw [Tmap_apply, hsplit]
  conv_rhs => rw [hu, hsplit]
  congr 1
  have hQ : ∀ w, Q4 w = -normSq (toH w) := fun w => by rw [normSq_toH]; ring
  rw [hQ, hQ, toH_fromH, map_mul, map_mul, normSq_star, hp, hr, one_mul, mul_one]

lemma det_Tmap {p r : ℍ[ℝ]} (hp : normSq p = 1) (hr : normSq r = 1) :
    LinearMap.det (Tmap p r) = 1 := by
  obtain ⟨s, hs, rfl⟩ := exists_sqrt p hp
  obtain ⟨t, ht, rfl⟩ := exists_sqrt r hr
  rw [← Tmap_mul, map_mul, ← LinearMap.det_toMatrix']
  exact det_sq (toMatrix_mem _ (Tmap_isometry hs ht))

/-! ### Vector action and surjectivity -/

lemma diag_conj_01 {A : M2H} (hA : IsDiag2 A) (G : M2H) :
    (A * G * star A) 0 1 = A 0 0 * G 0 1 * star (A 1 1) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hA.1, hA.2]

/-- **Vector action**: `x ∈ spinGroup Q₄` acts on `W4 ≅ ℍ` by `v̂ ↦ α v̂ β̄`. -/
lemma vecRep_spinQ (x : spinGroup Q4) (v : Fin 4 → ℝ) :
    vecRep (spin4Hom x) (f4L v) = f4L (fromH (γ4 (x : CliffordAlgebra Q4) 0 0 * toH v *
      star (γ4 (x : CliffordAlgebra Q4) 1 1))) := by
  set y := spin4Hom x
  set u := vecRep y (f4L v)
  have hout := (spin4_iff y).mp (spin4Hom_mem x)
  have hsu : SuppIn S4 u := supp_of_polar u fun j hj => by
    have hj' : (j : ℕ) < 10 := (by decide : ∀ j : Fin 14, j ∉ S4 → (j : ℕ) < 10) j hj
    rw [← hout.2.2 j hj, vecRep_polar, polar_eb_right, f4L_low v hj']; ring
  have hιu : ι Q77 u = Φ4 ((x : CliffordAlgebra Q4) * ι Q4 v * star (x : CliffordAlgebra Q4)) := by
    show ι Q77 (vecL _ _) = _
    rw [ι_vecL, map_mul, map_mul, Φ4_ι, Φ4_star]; rfl
  have hw : (x : CliffordAlgebra Q4) * ι Q4 v * star (x : CliffordAlgebra Q4) = ι Q4 (res4 u) := by
    apply Φ4_injective
    rw [← hιu, Φ4_ι, f4L_res4 hsu]
  have hγ := congrArg γ4 hw
  rw [map_mul, map_mul, γ4_star, γ4_ι, γ4_ι] at hγ
  have h01 := congrFun (congrFun hγ 0) 1
  rw [diag_conj_01 (γ4_even (spinGroup.mem_iff.mp x.2).2)] at h01
  have e : toH (res4 u) = γ4 (x : CliffordAlgebra Q4) 0 0 * toH v * star (γ4 (x : CliffordAlgebra Q4) 1 1) := by
    simpa [gH] using h01.symm
  rw [← e, fromH_toH, f4L_res4 hsu]

/-- `−1 ∈ spinGroup Q₄`. -/
noncomputable def negOne4 : spinGroup Q4 :=
  ⟨ι Q4 (Pi.single 0 1) * ι Q4 (Pi.single 0 1), pair_mem_gen Q4 _ _ (by
    simp [Q4, QuadraticMap.weightedSumSquares_apply, Pi.single_apply])⟩

lemma negOne4_val : (negOne4 : CliffordAlgebra Q4) = -1 := by
  show ι Q4 (Pi.single 0 1) * ι Q4 (Pi.single 0 1) = -1
  rw [ι_sq_scalar, show Q4 (Pi.single 0 1) = -1 by
    simp [Q4, QuadraticMap.weightedSumSquares_apply, Pi.single_apply], map_neg, map_one]

/-- **`spinQ` is surjective onto `Sp(1) × Sp(1)`.** -/
theorem spinQ_surjective : Function.Surjective spinQ := by
  rintro ⟨p, r⟩
  have hp := normSq_one_of_unitary p.2
  have hr := normSq_one_of_unitary r.2
  set T := Tmap (p : ℍ[ℝ]) (r : ℍ[ℝ])
  obtain ⟨y, hy, hyT⟩ := block_onto uniform_S4 T (Tmap_isometry hp hr) (det_Tmap hp hr)
    (fun j hj => Tmap_off _ _ hj)
  set x := spin4Equiv.symm ⟨y, hy⟩
  have hxy : spin4Hom x = y := congrArg Subtype.val (spin4Equiv.apply_symm_apply ⟨y, hy⟩)
  have hact : ∀ q : ℍ[ℝ], γ4 (x : CliffordAlgebra Q4) 0 0 * q * star (γ4 (x : CliffordAlgebra Q4) 1 1) =
      (p : ℍ[ℝ]) * q * star (r : ℍ[ℝ]) := fun q => by
    have h1 := vecRep_spinQ x (fromH q)
    rw [hxy] at h1
    have h2 : vecRep y (f4L (fromH q)) = T (f4L (fromH q)) :=
      congrArg (fun f : Module.End ℝ (Fin 14 → ℝ) => f (f4L (fromH q))) hyT
    rw [h2, Tmap_f4L, toH_fromH] at h1
    have h3 := congrArg (fun w => toH (res4 w)) h1
    simpa [res4_f4L] using h3.symm
  rcases quat_pair_unique (normSq_one_of_unitary (γ4_spin_unitary x.2 0))
    (normSq_one_of_unitary (γ4_spin_unitary x.2 1)) hp hr hact with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨x, Prod.ext (Subtype.ext ha) (Subtype.ext hb)⟩
  · refine ⟨negOne4 * x, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · show γ4 ((negOne4 : CliffordAlgebra Q4) * x) 0 0 = p
      rw [negOne4_val, neg_one_mul, map_neg, Matrix.neg_apply, ha, neg_neg]
    · show γ4 ((negOne4 : CliffordAlgebra Q4) * x) 1 1 = r
      rw [negOne4_val, neg_one_mul, map_neg, Matrix.neg_apply, hb, neg_neg]

/-- **`Spin4 ≃* Sp(1) × Sp(1)`**, pairs of unit quaternions. With `sp1EquivSU2` (`SpinSU2.lean`) this
gives `Spin4 ≃* SU(2) × SU(2)` (`spin4SU2Equiv`). -/
noncomputable def spin4QuatEquiv : Spin4 ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  spin4Equiv.symm.trans (MulEquiv.ofBijective spinQ ⟨spinQ_injective, spinQ_surjective⟩)

end GU.Spinor
