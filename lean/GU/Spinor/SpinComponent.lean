import GU.Spinor.BlockSpin

/-!
# `SO⁺(7,7) = SO₀(7,7)`: the image of `Spin(7,7)` is the identity component of `O(7,7)`

Topology: matrices `Matrix (Fin 14) (Fin 14) ℝ` with the product topology, and
`IsoSet = {M | toLin' M preserves Q77}` (the matrix group `O(7,7)`).

1. **Unit quadrics are path-connected to a base point** (`joined_rep`). For `q = ±1`, every `a` with
   `Q a = q` is joined inside `{Q = q}` to `e₀` (`q = 1`) or `e₇` (`q = −1`). The path is a normalised
   straight segment `t ↦ v(t)/√(q Q(v(t)))`, with `q Q(v(t)) = (1−2t)² + t(1−t)(2 + q·polar(u,w)) > 0`.
   It needs at most one detour through `±e₁` (resp. `±e₈`).
2. **`spin_joined`**: for every `x ∈ Spin(7,7)`, `vecRep x` is joined to `1` inside `IsoSet`. Write
   `vecRep x = r_{v₁} ⋯ r_{vₘ}` (`range_vecRep`) and move every `vᵢ` to its base point. The endpoint
   is a product of commuting involutions `r_{e₀}`, `r_{e₇}` with even counts, hence `1`.
3. **`g0_not_joined`**: `g₀ = r_{e₀} r_{e₇}` is not joined to `1` inside `IsoSet`. For an isometry
   with blocks `[[A, B], [C, D]]`, `Mᵀ η M = η` gives `DᵀD = 1 + BᵀB`, which is positive definite, so
   `det D ≠ 0`. Since `det D(1) = 1` and `det D(g₀) = −1`, the intermediate value theorem rules out
   a path.
4. **`joined_iff_spin`** / **`joined_iff_spin_mat`**: `g` is joined to `1` inside `O(7,7)` iff
   `g ∈ vecRep(Spin(7,7))`. So the identity path component of `O(7,7)` (topologically `SO₀(7,7)`)
   equals the algebraic `SO⁺(7,7)`. Every isometry joined to `1` has `det = 1` automatically, by
   continuity of `det` (`det_eq_one_of_joined`).
5. **`cc_iff_spin`**: the same holds for the identity *connected* component `connectedComponentIn
   O(7,7) 1`. On it `det D > 0`, since `det D` is continuous and nonvanishing, and left
   multiplication by `g₀` flips the sign of `det D` (`det_Dblk_g0_mul`). So `SO₀(7,7)` in its usual
   meaning (the identity connected component) equals `SO⁺(7,7)`. No Lie group structure is used or
   claimed.
-/

namespace GU.Spinor

open CliffordAlgebra Matrix

/-! ### 1. Unit quadrics -/

/-- The quadric `{Q = q}`. -/
def UQ (q : ℝ) : Set (Fin 14 → ℝ) := {v | Q77 v = q}

lemma continuous_Q77 : Continuous fun v : Fin 14 → ℝ => Q77 v := by
  simp only [Q77, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  fun_prop

lemma Q_comb (a b : ℝ) (u w : Fin 14 → ℝ) :
    Q77 (a • u + b • w) = a ^ 2 * Q77 u + b ^ 2 * Q77 w + a * b * QuadraticMap.polar Q77 u w := by
  rw [QuadraticMap.map_add Q77, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]; ring

/-- The normalised segment from `u` to `w` stays in `{Q = q}` when `q · polar(u, w) > −2`. -/
lemma joined_seg {q : ℝ} (hq : q * q = 1) {u w : Fin 14 → ℝ} (hu : Q77 u = q) (hw : Q77 w = q)
    (hp : -2 < q * QuadraticMap.polar Q77 u w) : JoinedIn (UQ q) u w := by
  set p := QuadraticMap.polar Q77 u w
  let v : ℝ → Fin 14 → ℝ := fun t => (1 - t) • u + t • w
  have hQv : ∀ t, q * Q77 (v t) = (1 - 2 * t) ^ 2 + t * (1 - t) * (2 + q * p) := fun t => by
    simp only [v, Q_comb, hu, hw]
    linear_combination ((1 - t) ^ 2 + t ^ 2) * hq
  have hpos : ∀ t : unitInterval, 0 < q * Q77 (v t) := fun t => by
    rw [hQv]
    have h0 : (0 : ℝ) ≤ t := t.2.1
    have h1 : (t : ℝ) ≤ 1 := t.2.2
    by_cases ht : (1 - 2 * (t : ℝ)) = 0
    · have : (t : ℝ) = 1 / 2 := by linarith
      rw [ht, this]; nlinarith
    · have := pow_pos (abs_pos.mpr ht) 2
      rw [sq_abs] at this
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  let s : unitInterval → Fin 14 → ℝ := fun t => (Real.sqrt (q * Q77 (v t)))⁻¹ • v t
  have hv : Continuous fun t : unitInterval => v t :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hc : Continuous fun t : unitInterval => (Real.sqrt (q * Q77 (v t)))⁻¹ :=
    Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_const.mul (continuous_Q77.comp hv)))
      fun t => (Real.sqrt_pos.mpr (hpos t)).ne'
  have hs : Continuous s := hc.smul hv
  have hv0 : v 0 = u := by simp [v]
  have hv1 : v 1 = w := by simp [v]
  have hn : ∀ t : unitInterval, (Real.sqrt (q * Q77 (v t)))⁻¹ • v t ∈ UQ q := fun t => by
    show Q77 _ = q
    have hne : Q77 (v t) ≠ 0 := fun h => by have := hpos t; rw [h, mul_zero] at this; exact lt_irrefl _ this
    rw [QuadraticMap.map_smul, smul_eq_mul, ← mul_inv, Real.mul_self_sqrt (hpos t).le, mul_inv,
      mul_assoc, inv_mul_cancel₀ hne, mul_one]
    exact inv_eq_of_mul_eq_one_left hq
  refine ⟨⟨⟨s, hs⟩, ?_, ?_⟩, hn⟩
  · show (Real.sqrt (q * Q77 (v 0)))⁻¹ • v 0 = u
    rw [hv0, hu, hq, Real.sqrt_one, inv_one, one_smul]
  · show (Real.sqrt (q * Q77 (v 1)))⁻¹ • v 1 = w
    rw [hv1, hw, hq, Real.sqrt_one, inv_one, one_smul]

/-- Every point of `{Q = q}` is joined to the base point `e_{i₀}`, using a helper `e_{i₁}`. -/
lemma joined_rep {q : ℝ} (hq : q * q = 1) {i₀ i₁ : Fin 14} (h0 : Q77 (eb i₀) = q) (h1 : Q77 (eb i₁) = q)
    (h01 : i₀ ≠ i₁) {a : Fin 14 → ℝ} (ha : Q77 a = q) : JoinedIn (UQ q) a (eb i₀) := by
  by_cases hd : -2 < q * QuadraticMap.polar Q77 a (eb i₀)
  · exact joined_seg hq ha h0 hd
  · -- detour through `w = ±e_{i₁}`, chosen with `q · polar(a, w) ≥ 0`
    have hw : ∃ w : Fin 14 → ℝ, Q77 w = q ∧ 0 ≤ q * QuadraticMap.polar Q77 a w ∧
        QuadraticMap.polar Q77 w (eb i₀) = 0 := by
      by_cases hs : 0 ≤ q * QuadraticMap.polar Q77 a (eb i₁)
      · exact ⟨eb i₁, h1, hs, polar_eb h01.symm⟩
      · refine ⟨-eb i₁, by rw [QuadraticMap.map_neg, h1], ?_, ?_⟩
        · rw [QuadraticMap.polar_neg_right]; linarith
        · rw [QuadraticMap.polar_neg_left, polar_eb h01.symm, neg_zero]
    obtain ⟨w, hwq, hwp, hw0⟩ := hw
    exact (joined_seg hq ha hwq (by linarith)).trans (joined_seg hq hwq h0 (by rw [hw0]; norm_num))

/-- Base point of the sign class of a unit vector. -/
noncomputable def baseVec (m : UVec) : UVec := if Q77 m.1 = 1 then ue0 else ue7

lemma baseVec_Q (m : UVec) : Q77 (baseVec m).1 = Q77 m.1 := by
  unfold baseVec
  split_ifs with h
  · rw [h]; simp [ue0, Q_eb]
  · rcases m.2 with h' | h'
    · exact absurd h' h
    · rw [h']; simp [ue7, Q_eb]

lemma joined_base (m : UVec) : JoinedIn (UQ (Q77 m.1)) (baseVec m).1 m.1 := by
  have hq := m.Q_sq
  refine JoinedIn.symm ?_
  unfold baseVec
  split_ifs with h
  · exact joined_rep hq (i₁ := 1) (by rw [h]; simp [Q_eb]) (by rw [h]; simp [Q_eb]) (by decide) rfl
  · have h' : Q77 m.1 = -1 := m.2.resolve_left h
    exact joined_rep hq (i₁ := 8) (by rw [h']; simp [Q_eb]) (by rw [h']; simp [Q_eb]) (by decide) rfl

/-! ### 2. Paths of reflection products -/

/-- The matrix group `O(7,7)`. -/
def IsoSet : Set (Matrix (Fin 14) (Fin 14) ℝ) := {M | IsIsom77 (Matrix.toLin' M)}

lemma toMatrix_mem (f : Module.End ℝ (Fin 14 → ℝ)) (hf : IsIsom77 f) : LinearMap.toMatrix' f ∈ IsoSet := by
  show IsIsom77 (Matrix.toLin' _); rw [Matrix.toLin'_toMatrix']; exact hf

lemma IsoSet_mul {M N : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) (hN : N ∈ IsoSet) :
    M * N ∈ IsoSet := by
  show IsIsom77 (Matrix.toLin' (M * N)); rw [Matrix.toLin'_mul]; exact IsIsom77.mul hM hN

lemma one_mem_IsoSet : (1 : Matrix (Fin 14) (Fin 14) ℝ) ∈ IsoSet := by
  show IsIsom77 (Matrix.toLin' 1); rw [Matrix.toLin'_one]; intro v; rfl

/-- A path of reflections along a path in a quadric is continuous. -/
lemma continuous_refl_path {q : ℝ} (γ : unitInterval → Fin 14 → ℝ) (hγ : Continuous γ)
    (hQ : ∀ t, Q77 (γ t) = q) : Continuous fun t => LinearMap.toMatrix' (refl (γ t)) := by
  have e : (fun t => LinearMap.toMatrix' (refl (γ t))) = fun t => fun i j =>
      (eb j) i - 2 * ((if (j : ℕ) < 7 then (1 : ℝ) else -1) * γ t j) / q * γ t i := by
    funext t i j
    rw [LinearMap.toMatrix'_apply, refl_apply, polar_eb_right, hQ t]
    rfl
  rw [e]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hi : Continuous fun t => γ t i := (continuous_apply i).comp hγ
  have hj : Continuous fun t => γ t j := (continuous_apply j).comp hγ
  exact continuous_const.sub (((continuous_const.mul (continuous_const.mul hj)).div_const q).mul hi)

lemma list_path (l : List UVec) : ∃ F : unitInterval → Matrix (Fin 14) (Fin 14) ℝ, Continuous F ∧
    F 0 = LinearMap.toMatrix' (reflProd (l.map baseVec)) ∧ F 1 = LinearMap.toMatrix' (reflProd l) ∧
      ∀ t, F t ∈ IsoSet := by
  induction l with
  | nil =>
    exact ⟨fun _ => 1, continuous_const, by simp, by simp, fun _ => one_mem_IsoSet⟩
  | cons m l ih =>
    obtain ⟨F, hF, h0, h1, hiso⟩ := ih
    obtain ⟨γ, hγ⟩ := joined_base m
    refine ⟨fun t => LinearMap.toMatrix' (refl (γ t)) * F t,
      (continuous_refl_path γ γ.continuous hγ).mul hF, ?_, ?_, fun t => ?_⟩
    · simp only [List.map_cons, reflProd_cons, LinearMap.toMatrix'_mul, h0, γ.source]
    · simp only [reflProd_cons, LinearMap.toMatrix'_mul, h1, γ.target]
    · exact IsoSet_mul (toMatrix_mem _ (refl_isometry (by rw [hγ t]; exact m.Q_ne))) (hiso t)

lemma refl_comm {a b : Fin 14 → ℝ} (h : QuadraticMap.polar Q77 a b = 0) : refl a * refl b = refl b * refl a := by
  refine LinearMap.ext fun v => ?_
  have h' : QuadraticMap.polar Q77 b a = 0 := by rw [QuadraticMap.polar_comm]; exact h
  simp only [Module.End.mul_apply, refl_apply, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, h, h', smul_zero, sub_zero]
  abel

lemma reflProd_base (l : List UVec) : ∃ a b : ℕ,
    reflProd (l.map baseVec) = refl (eb 0) ^ a * refl (eb 7) ^ b ∧ a + b = l.length ∧
      qProd l = (-1) ^ b := by
  induction l with
  | nil => exact ⟨0, 0, by simp, rfl, rfl⟩
  | cons m l ih =>
    obtain ⟨a, b, hp, hl, hq⟩ := ih
    have hc : Commute (refl (eb 7)) (refl (eb 0)) :=
      refl_comm (polar_eb (by decide))
    by_cases hm : Q77 m.1 = 1
    · refine ⟨a + 1, b, ?_, by simp; omega, by rw [qProd_cons, hm, one_mul, hq]⟩
      rw [List.map_cons, reflProd_cons, hp, show baseVec m = ue0 by simp [baseVec, hm], pow_succ',
        mul_assoc]
      rfl
    · have hm' : Q77 m.1 = -1 := m.2.resolve_left hm
      refine ⟨a, b + 1, ?_, by simp; omega, by rw [qProd_cons, hm', hq, pow_succ']⟩
      rw [List.map_cons, reflProd_cons, hp, show baseVec m = ue7 by simp [baseVec, hm], pow_succ',
        ← mul_assoc, ← mul_assoc]
      show refl (eb 7) * refl (eb 0) ^ a * refl (eb 7) ^ b = refl (eb 0) ^ a * refl (eb 7) * refl (eb 7) ^ b
      rw [(hc.pow_right a).eq]

lemma refl_pow_even {m : Fin 14 → ℝ} (hm : Q77 m ≠ 0) {a : ℕ} (ha : Even a) : refl m ^ a = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [← two_mul, pow_mul, sq, show refl m * refl m = 1 from LinearMap.ext fun v => refl_refl hm v,
    one_pow]

/-- **`Spin(7,7)` lands in the identity path component of `O(7,7)`.** -/
theorem spin_joined (x : Spin77) :
    JoinedIn IsoSet 1 (LinearMap.toMatrix'
      ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ))) := by
  obtain ⟨l, hl, he, hq⟩ := (range_vecRep _).mp ⟨x, rfl⟩
  obtain ⟨F, hF, h0, h1, hiso⟩ := list_path l
  obtain ⟨a, b, hp, hab, hqb⟩ := reflProd_base l
  have hb : Even b := neg_one_pow_even (hqb ▸ hq)
  have ha : Even a := by
    have : Even (a + b) := hab ▸ he
    exact (Nat.even_add.mp this).mpr hb
  have hbase : reflProd (l.map baseVec) = 1 := by
    rw [hp, refl_pow_even (Q_eb_ne 0) ha, refl_pow_even (Q_eb_ne 7) hb, one_mul]
  refine ⟨⟨⟨F, hF⟩, ?_, ?_⟩, hiso⟩
  · show F 0 = 1; rw [h0, hbase, LinearMap.toMatrix'_one]
  · show F 1 = _; rw [h1, hl]

/-! ### 3. The `D`-block obstruction -/

/-- The signature weights `η`. -/
def ηw (k : Fin 14) : ℝ := if (k : ℕ) < 7 then 1 else -1

lemma toLin'_eb (M : Matrix (Fin 14) (Fin 14) ℝ) (a : Fin 14) :
    Matrix.toLin' M (eb a) = fun k => M k a := by
  funext k; simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, eb, Pi.single_apply]

/-- **Gram identity** `Mᵀ η M = η` for `M ∈ O(7,7)`, entrywise. -/
lemma iso_gram {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) (a b : Fin 14) :
    ∑ k, ηw k * (M k a * M k b) = if a = b then ηw a else 0 := by
  have h := IsIsom77.polar hM (eb a) (eb b)
  rw [toLin'_eb, toLin'_eb, polar_Q77, polar_Q77] at h
  have h2 : ∑ i : Fin 14, (if (i : ℕ) < 7 then (1 : ℝ) else -1) * (eb a i * eb b i) =
      if a = b then ηw a else 0 := by
    rw [Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab; simp [ηw, eb]
      · simp [eb, hab]
    · intro i _ hia; simp [eb, Pi.single_apply, hia]
    · simp
  have : ∑ k, ηw k * (M k a * M k b) =
      ∑ i : Fin 14, (if (i : ℕ) < 7 then (1 : ℝ) else -1) * (eb a i * eb b i) := by
    simp only [ηw]; linarith
  rw [this, h2]

/-- Positive and negative coordinate embeddings `Fin 7 → Fin 14`. -/
def pos7 (i : Fin 7) : Fin 14 := ⟨i, by omega⟩
def neg7 (i : Fin 7) : Fin 14 := ⟨i + 7, by omega⟩

lemma sum14 (f : Fin 14 → ℝ) : ∑ k, f k = ∑ k : Fin 7, f (pos7 k) + ∑ k : Fin 7, f (neg7 k) := by
  have := Fin.sum_univ_add (a := 7) (b := 7) f
  rw [this]
  congr 1

/-- Lower-right block `D` and upper-right block `B`. -/
def Dblk (M : Matrix (Fin 14) (Fin 14) ℝ) : Matrix (Fin 7) (Fin 7) ℝ := M.submatrix neg7 neg7
def Bblk (M : Matrix (Fin 14) (Fin 14) ℝ) : Matrix (Fin 7) (Fin 7) ℝ := M.submatrix pos7 neg7

lemma DtD {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) :
    (Dblk M)ᵀ * Dblk M = 1 + (Bblk M)ᵀ * Bblk M := by
  ext i j
  have h := iso_gram hM (neg7 i) (neg7 j)
  rw [sum14] at h
  have hη1 : ∀ k, ηw (pos7 k) = 1 := fun k => by simp [ηw, pos7]
  have hη2 : ∀ k, ηw (neg7 k) = -1 := fun k => by simp [ηw, neg7]
  have hinj : (neg7 i = neg7 j) ↔ i = j := ⟨fun e => Fin.ext (by simpa [neg7] using e), fun e => e ▸ rfl⟩
  simp only [hη1, hη2, one_mul, neg_one_mul, Finset.sum_neg_distrib, hinj] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Dblk, Bblk, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.one_apply]
  split_ifs at h ⊢ with hij
  · linarith
  · linarith

lemma det_Dblk_ne {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : (Dblk M).det ≠ 0 := by
  intro h0
  have hpd : (1 + (Bblk M)ᵀ * Bblk M).PosDef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (Bblk M)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact Matrix.PosDef.one.add_posSemidef this
  have hdet := hpd.det_pos
  rw [← DtD hM, Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at hdet
  exact lt_irrefl _ hdet

lemma g0_eb (k : Fin 14) : g0 (eb k) = if k = 0 ∨ k = 7 then -eb k else eb k := by
  show refl (eb 0) (refl (eb 7) (eb k)) = _
  by_cases h7 : k = 7
  · subst h7
    rw [refl_self (Q_eb_ne 7), map_neg, refl_fix (polar_eb (by decide : (0 : Fin 14) ≠ 7))]
    simp
  · rw [refl_fix (polar_eb (Ne.symm h7))]
    by_cases h0 : k = 0
    · subst h0; rw [refl_self (Q_eb_ne 0)]; simp
    · rw [refl_fix (polar_eb (Ne.symm h0))]; simp [h0, h7]

lemma Dblk_g0 : Dblk (LinearMap.toMatrix' g0) = Matrix.diagonal fun i => if i = 0 then -1 else 1 := by
  ext i j
  simp only [Dblk, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]
  rw [show (Pi.single (neg7 j) 1 : Fin 14 → ℝ) = eb (neg7 j) from rfl, g0_eb]
  have hn0 : neg7 j ≠ 0 := fun h => by
    have := congrArg Fin.val h; simp only [neg7] at this; omega
  have h7 : neg7 j = 7 ↔ j = 0 := by
    constructor
    · intro h; have := congrArg Fin.val h; simp only [neg7] at this; exact Fin.ext (by simp; omega)
    · rintro rfl; rfl
  have hij : neg7 i = neg7 j ↔ i = j := by
    constructor
    · intro h; have := congrArg Fin.val h; simp only [neg7] at this; exact Fin.ext (by omega)
    · rintro rfl; rfl
  by_cases hj : j = 0
  · subst hj
    by_cases hi : i = 0
    · subst hi; simp [hn0, h7, eb]
    · simp [hn0, h7, eb, hij, hi]
  · by_cases hi : i = j
    · subst hi; simp [hn0, h7, hj, eb]
    · simp [hn0, h7, hj, eb, hij, hi]

lemma det_Dblk_g0 : (Dblk (LinearMap.toMatrix' g0)).det = -1 := by
  rw [Dblk_g0, Matrix.det_diagonal, Fin.prod_univ_succ]; simp

lemma det_Dblk_one : (Dblk (1 : Matrix (Fin 14) (Fin 14) ℝ)).det = 1 := by
  have : Dblk (1 : Matrix (Fin 14) (Fin 14) ℝ) = 1 := by
    ext i j; simp [Dblk, Matrix.one_apply, neg7, Fin.ext_iff]
  rw [this, Matrix.det_one]

/-- **`g₀` is not in the identity path component of `O(7,7)`.** -/
theorem g0_not_joined : ¬ JoinedIn IsoSet 1 (LinearMap.toMatrix' g0) := by
  rintro ⟨γ, hγ⟩
  have hc : Continuous fun t => (Dblk (γ t)).det :=
    (γ.continuous.matrix_submatrix neg7 neg7).matrix_det
  obtain ⟨t, ht⟩ : (0 : ℝ) ∈ Set.range fun t => (Dblk (γ t)).det := by
    refine intermediate_value_univ 1 0 hc ⟨?_, ?_⟩
    · show (Dblk (γ 1)).det ≤ 0
      rw [γ.target, det_Dblk_g0]; norm_num
    · show 0 ≤ (Dblk (γ 0)).det
      rw [γ.source, det_Dblk_one]; norm_num
  exact det_Dblk_ne (hγ t) ht

/-! ### 4. Identity component = image of `Spin(7,7)` -/

/-- `η = diag(+1×7, −1×7)`. -/
def ηM : Matrix (Fin 14) (Fin 14) ℝ := Matrix.diagonal ηw

lemma ηw_sq (k : Fin 14) : ηw k * ηw k = 1 := by unfold ηw; split_ifs <;> norm_num

lemma ηM_mul_self : ηM * ηM = 1 := by
  rw [ηM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext k; exact ηw_sq k

lemma gram_mat {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : Mᵀ * ηM * M = ηM := by
  ext a b
  rw [Matrix.mul_apply, ηM, Matrix.diagonal_apply, ← iso_gram hM a b]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]; ring

/-- The inverse of an `O(7,7)` matrix: `M⁻¹ = η Mᵀ η`. -/
def invη (M : Matrix (Fin 14) (Fin 14) ℝ) : Matrix (Fin 14) (Fin 14) ℝ := ηM * Mᵀ * ηM

lemma invη_mul {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : invη M * M = 1 := by
  rw [invη, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, gram_mat hM, ηM_mul_self]

lemma mul_invη {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : M * invη M = 1 :=
  mul_eq_one_comm.mp (invη_mul hM)

lemma invη_mem {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : invη M ∈ IsoSet := fun v => by
  have hv : Matrix.toLin' M (Matrix.toLin' (invη M) v) = v := by
    rw [← Matrix.toLin'_mul_apply, mul_invη hM, Matrix.toLin'_one]; rfl
  have h := hM (Matrix.toLin' (invη M) v)
  rw [hv] at h
  exact h.symm

lemma invη_one : invη 1 = 1 := by rw [invη, Matrix.transpose_one, Matrix.mul_one, ηM_mul_self]

lemma continuous_invη : Continuous invη :=
  (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const

lemma det_sq {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ IsoSet) : M.det * M.det = 1 := by
  have h := congrArg Matrix.det (invη_mul hM)
  rw [Matrix.det_mul, invη, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hη : ηM.det * ηM.det = 1 := by rw [← Matrix.det_mul, ηM_mul_self, Matrix.det_one]
  linear_combination h - M.det * M.det * hη
  
/-- An isometry joined to `1` inside `O(7,7)` has `det = 1`. -/
lemma det_eq_one_of_joined {M : Matrix (Fin 14) (Fin 14) ℝ} (h : JoinedIn IsoSet 1 M) : M.det = 1 := by
  obtain ⟨γ, hγ⟩ := h
  have hM : M ∈ IsoSet := γ.target ▸ hγ 1
  rcases mul_self_eq_one_iff.mp (det_sq hM) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨t, ht⟩ : (0 : ℝ) ∈ Set.range fun t => (γ t).det := by
      refine intermediate_value_univ 1 0 γ.continuous.matrix_det ⟨?_, ?_⟩
      · show (γ 1).det ≤ 0; rw [γ.target, h1]; norm_num
      · show 0 ≤ (γ 0).det; rw [γ.source, Matrix.det_one]; norm_num
    have := det_sq (hγ t)
    rw [show (γ t).det = 0 from ht, mul_zero] at this
    exact zero_ne_one this

/-- **Identity path component of `O(7,7)` = `SO⁺(7,7)` = `vecRep(Spin(7,7))`**: an isometry is joined
to `1` inside `O(7,7)` iff it is in the image of `Spin(7,7)` (connected version: `cc_iff_spin`). -/
theorem joined_iff_spin (g : Module.End ℝ (Fin 14 → ℝ)) (hg : IsIsom77 g) :
    JoinedIn IsoSet 1 (LinearMap.toMatrix' g) ↔
      ∃ x : Spin77, ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = g := by
  constructor
  · intro hj
    have hdet : LinearMap.det g = 1 := by
      rw [← LinearMap.det_toMatrix']; exact det_eq_one_of_joined hj
    rcases mem_or_g0_mul_mem g hg hdet with h | ⟨y, hy⟩
    · exact h
    · exfalso
      obtain ⟨γ, hγ⟩ := hj
      have hjy : JoinedIn IsoSet 1 (LinearMap.toMatrix' (g0 * g)) := hy ▸ spin_joined y
      obtain ⟨δ, hδ⟩ := hjy
      apply g0_not_joined
      refine ⟨⟨⟨fun t => δ t * invη (γ t),
        δ.continuous.matrix_mul (continuous_invη.comp γ.continuous)⟩, ?_, ?_⟩,
        fun t => IsoSet_mul (hδ t) (invη_mem (hγ t))⟩
      · show δ 0 * invη (γ 0) = 1
        rw [δ.source, γ.source, invη_one, Matrix.mul_one]
      · show δ 1 * invη (γ 1) = _
        rw [δ.target, γ.target, LinearMap.toMatrix'_mul, Matrix.mul_assoc,
          mul_invη (toMatrix_mem g hg), Matrix.mul_one]
  · rintro ⟨x, rfl⟩
    exact spin_joined x

/-! ### 5. The identity *connected* component -/

/-- `g₀` is diagonal: `diag(−1 at e₀, −1 at e₇, 1 elsewhere)`. -/
def dg0 (k : Fin 14) : ℝ := if k = 0 ∨ k = 7 then -1 else 1

lemma toMatrix_g0 : LinearMap.toMatrix' g0 = Matrix.diagonal dg0 := by
  ext i j
  rw [LinearMap.toMatrix'_apply, show (Pi.single j 1 : Fin 14 → ℝ) = eb j from rfl, g0_eb,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; by_cases h : i = 0 ∨ i = 7 <;> simp [h, eb, dg0]
  · by_cases h : j = 0 ∨ j = 7 <;> simp [h, eb, hij, dg0]

lemma det_Dblk_g0_mul (M : Matrix (Fin 14) (Fin 14) ℝ) :
    (Dblk (LinearMap.toMatrix' g0 * M)).det = -(Dblk M).det := by
  have h : Dblk (LinearMap.toMatrix' g0 * M) = Matrix.diagonal (fun i => dg0 (neg7 i)) * Dblk M := by
    ext i j
    simp [Dblk, toMatrix_g0, Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_succ]
  have h0 : dg0 (neg7 0) = -1 := by simp [dg0, neg7]
  have hs : ∀ i : Fin 6, dg0 (neg7 i.succ) = 1 := fun i => by
    unfold dg0; rw [ite_eq_right_iff.mpr]; intro h
    rcases h with h | h <;> have := congrArg Fin.val h <;> simp [neg7] at this
  simp [h0, hs]

/-- On the identity connected component of `O(7,7)`, `det D > 0` and `det = 1`. -/
lemma cc_pos {M : Matrix (Fin 14) (Fin 14) ℝ} (hM : M ∈ connectedComponentIn IsoSet 1) :
    0 < (Dblk M).det ∧ M.det = 1 := by
  have hC := isPreconnected_connectedComponentIn (F := IsoSet) (x := (1 : Matrix (Fin 14) (Fin 14) ℝ))
  have h1 : (1 : Matrix (Fin 14) (Fin 14) ℝ) ∈ connectedComponentIn IsoSet 1 :=
    mem_connectedComponentIn one_mem_IsoSet
  have hsub := connectedComponentIn_subset IsoSet (1 : Matrix (Fin 14) (Fin 14) ℝ)
  have hf : Continuous fun N : Matrix (Fin 14) (Fin 14) ℝ => (Dblk N).det :=
    (continuous_id.matrix_submatrix neg7 neg7).matrix_det
  have hd : Continuous fun N : Matrix (Fin 14) (Fin 14) ℝ => N.det := continuous_id.matrix_det
  constructor
  · by_contra hneg
    push Not at hneg
    have hI := (hC.image _ hf.continuousOn).Icc_subset ⟨M, hM, rfl⟩ ⟨1, h1, rfl⟩
    have h0 : (0 : ℝ) ∈ Set.Icc ((fun N => (Dblk N).det) M) ((fun N => (Dblk N).det) 1) := by
      simp only [det_Dblk_one]; exact ⟨hneg, zero_le_one⟩
    obtain ⟨N, hN, hN0⟩ := hI h0
    exact det_Dblk_ne (hsub hN) hN0
  · rcases mul_self_eq_one_iff.mp (det_sq (hsub hM)) with h | h
    · exact h
    · exfalso
      have hI := (hC.image _ hd.continuousOn).Icc_subset ⟨M, hM, rfl⟩ ⟨1, h1, rfl⟩
      have h0 : (0 : ℝ) ∈ Set.Icc ((fun N : Matrix (Fin 14) (Fin 14) ℝ => N.det) M)
          ((fun N : Matrix (Fin 14) (Fin 14) ℝ => N.det) 1) := by
        simp only [Matrix.det_one, h]; norm_num
      obtain ⟨N, hN, hN0⟩ := hI h0
      have := det_sq (hsub hN)
      simp only at hN0
      rw [hN0, mul_zero] at this
      exact zero_ne_one this

/-- Path-joined to `1` implies in the connected component. -/
lemma joined_cc {M : Matrix (Fin 14) (Fin 14) ℝ} (h : JoinedIn IsoSet 1 M) :
    M ∈ connectedComponentIn IsoSet 1 := by
  obtain ⟨γ, hγ⟩ := h
  have hr : Set.range γ ⊆ connectedComponentIn IsoSet 1 :=
    (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
      ⟨0, γ.source⟩ (Set.range_subset_iff.mpr hγ)
  exact hr ⟨1, γ.target⟩

/-- **`SO₀(7,7) = vecRep(Spin(7,7))`**: a matrix lies in the identity connected component of
`O(7,7)` iff it is `vecRep x` for some `x ∈ Spin(7,7)`; the same holds for the identity path
component (`joined_iff_spin_mat`). -/
theorem cc_iff_spin (M : Matrix (Fin 14) (Fin 14) ℝ) :
    M ∈ connectedComponentIn IsoSet 1 ↔
      ∃ x : Spin77, LinearMap.toMatrix'
        ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = M := by
  constructor
  · intro hM
    obtain ⟨hD, hdet⟩ := cc_pos hM
    have hiso := connectedComponentIn_subset IsoSet 1 hM
    set g := Matrix.toLin' M
    have hg : IsIsom77 g := hiso
    have hgdet : LinearMap.det g = 1 := by rw [LinearMap.det_toLin']; exact hdet
    rcases mem_or_g0_mul_mem g hg hgdet with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨x, by rw [hx, LinearMap.toMatrix'_toLin']⟩
    · exfalso
      have hj := joined_cc (spin_joined y)
      rw [hy, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin'] at hj
      have := (cc_pos hj).1
      rw [det_Dblk_g0_mul] at this
      linarith
  · rintro ⟨x, rfl⟩
    exact joined_cc (spin_joined x)

/-- Matrix form of `joined_iff_spin`: the identity path component of `O(7,7)` is `vecRep(Spin(7,7))`. -/
theorem joined_iff_spin_mat (M : Matrix (Fin 14) (Fin 14) ℝ) :
    JoinedIn IsoSet 1 M ↔
      ∃ x : Spin77, LinearMap.toMatrix'
        ((vecRep x : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : Module.End ℝ (Fin 14 → ℝ)) = M := by
  constructor
  · intro h; exact (cc_iff_spin M).mp (joined_cc h)
  · rintro ⟨x, rfl⟩; exact spin_joined x

end GU.Spinor
