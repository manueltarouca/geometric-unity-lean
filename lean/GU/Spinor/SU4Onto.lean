/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.SU4Det

/-!
# Track 1, S5: lifting `SU(4)` to `Spin6`

Part 1: block extensions. For `T : ℝ⁶ → ℝ⁶`, `ext6 T` acts as `T` on `W6` and as the identity on
its complement. It is multiplicative (`ext6_mul`), isometric when `T` is (`ext6_isometry`), and
`det (ext6 T_U) = 1` for `U ∈ SU(4)` (`det_ext6_TUL`). The ℝ¹⁴ determinant is handled by the same
square-root argument as `det_TUL`, with `vecRep ω₆` (`−1` on `W6`) in place of `−1`.

Part 2: surjectivity. `block_onto` lifts `ext6 T_U` to `x ∈ Spin6`. The vector action gives
`A σ(v) Bᴴ = U σ(v) M` with `M = K Uᵀ K`, so `C = Uᴴ A` commutes with `σ(e₀..e₃)`. Then `C` is a
scalar `c` (`scalar4_of_comm`) with `c⁴ = 1` (`quartic_roots`), and `x ω₆ᵏ` with `(−i)ᵏ c = 1`
maps to `U` (**`spinSU4_surjective`**). Hence **`spin6SU4Equiv : spinGroup Q₆ ≃* SU(4)`** and
**`Spin6SU4 : Spin6 ≃* SU(4)`** (the Pati–Salam factor inside `Spin(7,7)`).
-/

namespace GU.Spinor

open Matrix CliffordAlgebra

lemma res6_f6L (v : Fin 6 → ℝ) : res6 (f6L v) = v := by
  funext k; exact f6L_emb v k

/-- `res6` as a linear map. -/
noncomputable def res6L : (Fin 14 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := res6
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Block extension: `T` on `W6`, identity on the complement. -/
noncomputable def ext6 (T : Module.End ℝ (Fin 6 → ℝ)) : Module.End ℝ (Fin 14 → ℝ) :=
  LinearMap.id - f6L ∘ₗ res6L + f6L ∘ₗ T ∘ₗ res6L

lemma ext6_apply (T : Module.End ℝ (Fin 6 → ℝ)) (u : Fin 14 → ℝ) :
    ext6 T u = u - f6L (res6 u) + f6L (T (res6 u)) := rfl

lemma res6_ext6 (T : Module.End ℝ (Fin 6 → ℝ)) (u : Fin 14 → ℝ) : res6 (ext6 T u) = T (res6 u) := by
  rw [ext6_apply]
  have hl : ∀ a b : Fin 14 → ℝ, res6 (a + b) = res6 a + res6 b := fun _ _ => rfl
  have hs : ∀ a b : Fin 14 → ℝ, res6 (a - b) = res6 a - res6 b := fun _ _ => rfl
  rw [hl, hs, res6_f6L, res6_f6L, sub_self, zero_add]

lemma ext6_f6L (T : Module.End ℝ (Fin 6 → ℝ)) (v : Fin 6 → ℝ) : ext6 T (f6L v) = f6L (T v) := by
  rw [ext6_apply, res6_f6L]; abel

lemma ext6_mul (T S : Module.End ℝ (Fin 6 → ℝ)) : ext6 T * ext6 S = ext6 (T * S) := by
  refine LinearMap.ext fun u => ?_
  rw [Module.End.mul_apply, ext6_apply (T := T), res6_ext6, ext6_apply, ext6_apply, Module.End.mul_apply]
  abel

lemma ext6_off (T : Module.End ℝ (Fin 6 → ℝ)) {j : Fin 14} (hj : j ∉ S6) : ext6 T (eb j) = eb j := by
  have h0 : res6 (eb j) = 0 := by
    funext k
    have hk : ∀ k : Fin 6, emb6 k ∈ S6 := by decide
    have : emb6 k ≠ j := fun e => hj (e ▸ hk k)
    simp [res6, eb, this]
  rw [ext6_apply, h0, map_zero, map_zero]; simp

lemma polar_off_block6 (u : Fin 14 → ℝ) (w : Fin 6 → ℝ) :
    QuadraticMap.polar Q77 (u - f6L (res6 u)) (f6L w) = 0 := by
  rw [polar_Q77]
  have : ∀ i : Fin 14, (u - f6L (res6 u)) i * f6L w i = 0 := fun i => by
    by_cases hi : inW6 i
    · have hie : i = emb6 ⟨i - 1, by unfold inW6 at hi; omega⟩ := by
        ext; simp [emb6]; unfold inW6 at hi; omega
      have : (u - f6L (res6 u)) i = 0 := by
        rw [Pi.sub_apply, hie, f6L_emb]; simp [res6]
      rw [this, zero_mul]
    · rw [f6L_off w hi, mul_zero]
  simp only [this, mul_zero, Finset.sum_const_zero]

lemma ext6_isometry {T : Module.End ℝ (Fin 6 → ℝ)} (hT : ∀ v, Q6 (T v) = Q6 v) : IsIsom77 (ext6 T) := by
  intro u
  have hsplit : ∀ w : Fin 6 → ℝ, Q77 (u - f6L (res6 u) + f6L w) = Q77 (u - f6L (res6 u)) + Q6 w :=
    fun w => by rw [QuadraticMap.map_add Q77, polar_off_block6, add_zero, Q77_f6L]
  have hu : u = u - f6L (res6 u) + f6L (res6 u) := by abel
  rw [ext6_apply, hsplit]
  conv_rhs => rw [hu, hsplit]
  rw [hT]

lemma det_sq_ext6 {T : Module.End ℝ (Fin 6 → ℝ)} (hT : ∀ v, Q6 (T v) = Q6 v) :
    LinearMap.det (ext6 T) * LinearMap.det (ext6 T) = 1 := by
  rw [← LinearMap.det_toMatrix']
  exact det_sq (toMatrix_mem _ (ext6_isometry hT))

/-- `ext6 (−1) = vecRep ω₆`, so it has determinant `1`. -/
lemma det_ext6_neg_one : LinearMap.det (ext6 (-1)) = 1 := by
  have h : ext6 (-1) = ((vecRep (spin6Hom ω6) : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) :
      Module.End ℝ (Fin 14 → ℝ)) :=
    (Pi.basisFun ℝ (Fin 14)).ext fun j => by
      simp only [Pi.basisFun_apply, LinearEquiv.coe_coe]
      by_cases hj : j ∈ S6
      · have hk : ∃ k : Fin 6, emb6 k = j := by revert hj; revert j; decide
        obtain ⟨k, rfl⟩ := hk
        rw [show (Pi.single (emb6 k) 1 : Fin 14 → ℝ) = f6L (Pi.single k 1) from (f6L_single k).symm,
          ext6_f6L, vecRep_ω6]
        rfl
      · rw [show (Pi.single j 1 : Fin 14 → ℝ) = eb j from rfl, ext6_off _ hj,
          ((spin6_iff _).mp (spin6Hom_mem ω6)).2.2 j hj]
  rw [h]; exact det_vecRep _

/-- **Square-root dichotomy**: `T_U = T_V²` or `T_U = −T_V²` for some `V ∈ SU(4)`. -/
lemma su4_sqrt {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ) :
    ∃ V, ∃ hV : V ∈ specialUnitaryGroup (Fin 4) ℂ,
      TUL hU = TUL hV * TUL hV ∨ TUL hU = -(TUL hV * TUL hV) := by
  obtain ⟨hu, hdetU⟩ := mem_specialUnitaryGroup_iff.mp hU
  obtain ⟨V, hVu, hVV⟩ := unitary_sqrt U hu
  have hdV : V.det * V.det = 1 := by rw [← Matrix.det_mul, hVV]; exact hdetU
  rcases mul_self_eq_one_iff.mp hdV with h1 | h1
  · have hV : V ∈ specialUnitaryGroup (Fin 4) ℂ := mem_specialUnitaryGroup_iff.mpr ⟨hVu, h1⟩
    exact ⟨V, hV, Or.inl (TUL_mul_of hU hV hV hVV)⟩
  · set ζ : ℂ := (1 + Complex.I) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : Real.sqrt 2 ≠ 0 := by positivity
    have hζ2 : ζ * ζ = Complex.I := by
      apply Complex.ext <;> simp [ζ] <;> field_simp <;> nlinarith [hs]
    have hζn : star ζ * ζ = 1 := by
      apply Complex.ext <;> simp [ζ] <;> field_simp <;> nlinarith [hs]
    have hIu : Complex.I • U ∈ specialUnitaryGroup (Fin 4) ℂ := by
      refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
      · rw [mem_unitaryGroup_iff, StarModule.star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          (mem_unitaryGroup_iff.mp hu)]
        simp [Complex.conj_I]
      · rw [Matrix.det_smul, hdetU]; simp [Fintype.card_fin]
    have hV' : ζ • V ∈ specialUnitaryGroup (Fin 4) ℂ := by
      refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
      · rw [mem_unitaryGroup_iff, StarModule.star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          mem_unitaryGroup_iff.mp hVu, mul_comm, hζn, one_smul]
      · rw [Matrix.det_smul, h1, Fintype.card_fin,
          show ζ ^ 4 = (ζ * ζ) * (ζ * ζ) by ring, hζ2, Complex.I_mul_I]
        norm_num
    have hsq : (ζ • V) * (ζ • V) = Complex.I • U := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hζ2, hVV]
    refine ⟨ζ • V, hV', Or.inr ?_⟩
    rw [← TUL_mul_of hIu hV' hV' hsq]
    exact LinearMap.ext fun v => by
      show TU U v = -TU (Complex.I • U) v
      rw [TU_I hU hIu, neg_neg]

/-- **`det (ext6 T_U) = 1`** on `ℝ¹⁴`. -/
theorem det_ext6_TUL {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 4) ℂ) :
    LinearMap.det (ext6 (TUL hU)) = 1 := by
  obtain ⟨V, hV, h | h⟩ := su4_sqrt hU
  · rw [h, ← ext6_mul, map_mul]; exact det_sq_ext6 (TU_isometry hV)
  · rw [h, show -(TUL hV * TUL hV) = (-1) * (TUL hV * TUL hV) from LinearMap.ext fun v => by simp,
      ← ext6_mul, ← ext6_mul, map_mul, map_mul, det_ext6_neg_one, one_mul]
    exact det_sq_ext6 (TU_isometry hV)

set_option maxHeartbeats 4000000 in
lemma scalar4_of_comm (C : Matrix (Fin 4) (Fin 4) ℂ)
    (h0 : C * σM (Pi.single 0 1) = σM (Pi.single 0 1) * C)
    (h1 : C * σM (Pi.single 1 1) = σM (Pi.single 1 1) * C)
    (h2 : C * σM (Pi.single 2 1) = σM (Pi.single 2 1) * C)
    (h3 : C * σM (Pi.single 3 1) = σM (Pi.single 3 1) * C) :
    C = C 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have E : ∀ i j, (C * σM (Pi.single 0 1)) i j = (σM (Pi.single 0 1) * C) i j ∧
      (C * σM (Pi.single 1 1)) i j = (σM (Pi.single 1 1) * C) i j ∧
      (C * σM (Pi.single 2 1)) i j = (σM (Pi.single 2 1) * C) i j ∧
      (C * σM (Pi.single 3 1)) i j = (σM (Pi.single 3 1) * C) i j := fun i j =>
    ⟨congrFun (congrFun h0 i) j, congrFun (congrFun h1 i) j, congrFun (congrFun h2 i) j,
      congrFun (congrFun h3 i) j⟩
  have := E 0 0; have := E 0 1; have := E 0 2; have := E 0 3
  have := E 1 0; have := E 1 1; have := E 1 2; have := E 1 3
  have := E 2 0; have := E 2 1; have := E 2 2; have := E 2 3
  have := E 3 0; have := E 3 1; have := E 3 2; have := E 3 3
  simp [σM, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff] at *
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Complex.ext_iff] <;>
    constructor <;> linarith

lemma γ6_spin_B {x : CliffordAlgebra Q6} (hx : x ∈ spinGroup Q6) :
    star (γ6 x 1 1) * γ6 x 1 1 = 1 := by
  have he := (spinGroup.mem_iff.mp hx).2
  have hd := γ6_even he
  have hst : γ6 (star x) = star (γ6 x) := by rw [γ6_star, involute_of_even he]
  have h1 : star (γ6 x) * γ6 x = 1 := by
    rw [← hst, ← map_mul, spinGroup.star_mul_self_of_mem hx, map_one]
  have := congrFun (congrFun h1 1) 1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hd.1] using this

lemma quartic_roots {c : ℂ} (h : c ^ 4 = 1) : c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I := by
  have hf : (c - 1) * (c + 1) * (c - Complex.I) * (c + Complex.I) = 0 := by
    have : (c - 1) * (c + 1) * (c - Complex.I) * (c + Complex.I) = c ^ 4 - 1 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this, h, sub_self]
  rcases mul_eq_zero.mp hf with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · left; exact sub_eq_zero.mp h3
      · right; left; exact eq_neg_of_add_eq_zero_left h3
    · right; right; left; exact sub_eq_zero.mp h2
  · right; right; right; exact eq_neg_of_add_eq_zero_left h1

/-- **`spinSU4` is surjective**: every `U ∈ SU(4)` comes from `Spin(6)`. -/
theorem spinSU4_surjective : Function.Surjective spinSU4 := by
  rintro ⟨U, hU⟩
  obtain ⟨hu, hdetU⟩ := mem_specialUnitaryGroup_iff.mp hU
  set g := ext6 (TUL hU)
  obtain ⟨y, hy, hyg⟩ := block_onto uniform_S6 g (ext6_isometry (TU_isometry hU)) (det_ext6_TUL hU)
    (fun j hj => ext6_off _ hj)
  set x := spin6Equiv.symm ⟨y, hy⟩
  have hxy : spin6Hom x = y := congrArg Subtype.val (spin6Equiv.apply_symm_apply ⟨y, hy⟩)
  set A := γ6 (x : CliffordAlgebra Q6) 0 0
  set B := γ6 (x : CliffordAlgebra Q6) 1 1
  set M := Kc * Uᵀ * Kc
  -- `A σ(v) Bᴴ = U σ(v) M`
  have hact : ∀ v, A * σM v * Bᴴ = U * σM v * M := fun v => by
    have h1 := (vecRep_spinU x v).1
    rw [hxy] at h1
    have h2 : vecRep y (f6L v) = g (f6L v) :=
      congrArg (fun f : Module.End ℝ (Fin 14 → ℝ) => f (f6L v)) hyg
    rw [h2, ext6_f6L, res6_f6L] at h1
    rw [← h1]
    have h3 := congrArg (· * Kc) (σK_TU hU v)
    simp only [Matrix.mul_assoc, Kc_sq, Matrix.mul_one] at h3
    show σM (TU U v) = _
    rw [h3]; simp only [M, Matrix.mul_assoc]
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hu
  have hUU' : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hu
  have hBB : Bᴴ * B = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact γ6_spin_B x.2
  have e5 : A * Bᴴ = U * M := by
    have := hact (Pi.single 5 1); rwa [σM_e5, Matrix.mul_one, Matrix.mul_one] at this
  have hcomm : ∀ v, (Uᴴ * A) * σM v = σM v * (Uᴴ * A) := fun v => by
    have hM : M = Uᴴ * A * Bᴴ := by rw [Matrix.mul_assoc, e5, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    calc (Uᴴ * A) * σM v = Uᴴ * (A * σM v * Bᴴ) * B := by
          simp only [Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = σM v * (Uᴴ * A) := by
          rw [hact, show Uᴴ * (U * σM v * M) * B = (Uᴴ * U) * σM v * (M * B) by
            simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, hM]
          simp only [Matrix.mul_assoc, hBB, Matrix.mul_one]
  set C := Uᴴ * A
  have hC := scalar4_of_comm C (hcomm _) (hcomm _) (hcomm _) (hcomm _)
  set c := C 0 0
  have hA : A = c • U := by
    calc A = (U * Uᴴ) * A := by rw [hUU', Matrix.one_mul]
      _ = U * C := by rw [Matrix.mul_assoc]
      _ = c • U := by rw [hC, Matrix.mul_smul, Matrix.mul_one]
  have hdetA : A.det = 1 := (mem_specialUnitaryGroup_iff.mp (spinSU4 x).2).2
  have hc4 : c ^ 4 = 1 := by
    rw [hA, Matrix.det_smul, hdetU, Fintype.card_fin, mul_one] at hdetA; exact hdetA
  have hval : ∀ k : ℕ, ((spinSU4 (x * ω6 ^ k) : specialUnitaryGroup (Fin 4) ℂ) : M4C) =
      ((-Complex.I) ^ k * c) • U := fun k => by
    rw [map_mul, map_pow]
    show A * ((spinSU4 ω6 : specialUnitaryGroup (Fin 4) ℂ) : M4C) ^ k = _
    rw [show ((spinSU4 ω6 : specialUnitaryGroup (Fin 4) ℂ) : M4C) = (-Complex.I) • 1 from γ6_ω6_00,
      smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one, hA, smul_smul, mul_comm]
  have pick : ∃ k : ℕ, (-Complex.I) ^ k * c = 1 := by
    rcases quartic_roots hc4 with h | h | h | h
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨2, by rw [h]; ring_nf; rw [Complex.I_sq]; ring⟩
    · exact ⟨1, by rw [h]; ring_nf; rw [Complex.I_sq]; ring⟩
    · exact ⟨3, by rw [h]; ring_nf; rw [show Complex.I ^ 4 = 1 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num]⟩
  obtain ⟨k, hk⟩ := pick
  exact ⟨x * ω6 ^ k, Subtype.ext (by rw [hval, hk, one_smul])⟩

/-- **`Spin(6) ≅ SU(4)`**: `spinGroup Q₆ ≃* SU(4)`. -/
noncomputable def spin6SU4Equiv : spinGroup Q6 ≃* specialUnitaryGroup (Fin 4) ℂ :=
  MulEquiv.ofBijective spinSU4 ⟨spinSU4_injective, spinSU4_surjective⟩

/-- **The Pati–Salam `Spin6 ≅ SU(4)`**. -/
noncomputable def Spin6SU4 : Spin6 ≃* specialUnitaryGroup (Fin 4) ℂ :=
  spin6Equiv.symm.trans spin6SU4Equiv

end GU.Spinor
