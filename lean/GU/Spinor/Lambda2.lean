import GU.Spinor.SpinSU4

/-!
# `Λ²` of `4 × 4` matrices: the Hodge dual identity

For an antisymmetric `4 × 4` matrix `A`, `⋆A` is its Hodge dual, `(⋆A)ᵢⱼ = ½ εᵢⱼₖₗ Aₖₗ` (`dualE`).
**`lam2`**: for any `4 × 4` matrix `U` over any commutative ring, `Uᵀ ⋆(U A Uᵀ) U = det U · ⋆A`.
This is the identity behind `SU(4) → SO(6)`. For unitary `U` with `det U = 1` it says that
`A ↦ U A Uᵀ` commutes with `⋆` up to complex conjugation, so it preserves the 6-dimensional real
form of `Λ²ℂ⁴`. Track 1 of `MULTISESSION_PLAN.md`: S1 (`lam2`), S2 partly (`σK_eq`, `σK_vOf`: the
real form is `{A antisym : ⋆A = Ā}`), S3 (`su4_preserves`, the linear map `TUL`, `σK_TU`, `TU_isometry` via the Pfaffian `pf_conj`,
`TU_mul`). S4 is `SU4Det.lean`.
-/

namespace GU.Spinor

open Matrix

/-- Hodge dual on `4 × 4` matrices (reads only the upper triangle). -/
def dualE {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, A 2 3, -A 1 3, A 1 2; -A 2 3, 0, A 0 3, -A 0 2; A 1 3, -A 0 3, 0, A 0 1; -A 1 2, A 0 2, -A 0 1, 0]

/-- The antisymmetric matrix with upper-triangle entries `a b c d e f`. -/
def asym {R : Type*} [CommRing R] (a b c d e f : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

set_option maxHeartbeats 4000000 in
/-- **`Λ²` identity**: `Uᵀ ⋆(U A Uᵀ) U = det U · ⋆A` for antisymmetric `A`. -/
theorem lam2 {R : Type*} [CommRing R] (U : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    Uᵀ * dualE (U * asym a b c d e f * Uᵀ) * U = U.det • dualE (asym a b c d e f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asym, dualE, Matrix.mul_apply, Fin.sum_univ_four, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Fin.succAbove] <;> ring

/-! ### S2: `σ(v) K` and the real form of `Λ²ℂ⁴` -/

/-- `K = X ⊗ Y`. -/
def Kc : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, -Complex.I, 0, 0; Complex.I, 0, 0, 0]

/-- Complex coordinates of `σ(v) K`: `a = v₀ − i v₁`, `b = −v₂ + i v₃`, `c = v₄ − i v₅`. -/
def ca (v : Fin 6 → ℝ) : ℂ := ⟨v 0, -v 1⟩
def cb (v : Fin 6 → ℝ) : ℂ := ⟨-v 2, v 3⟩
def cc (v : Fin 6 → ℝ) : ℂ := ⟨v 4, -v 5⟩

set_option maxHeartbeats 1000000 in
/-- **`σ(v) K` is antisymmetric**, of the form `asym(a, b, c, c̄, −b̄, ā)`. -/
lemma σK_eq (v : Fin 6 → ℝ) :
    σM v * Kc = asym (ca v) (cb v) (cc v) (star (cc v)) (-star (cb v)) (star (ca v)) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [σM, Kc, asym, ca, cb, cc, Matrix.mul_apply, Fin.sum_univ_four]

/-- Real-form matrices: `asym(a, b, c, c̄, −b̄, ā)`. -/
def RF (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := asym a b c (star c) (-star b) (star a)

/-- The vector with given complex coordinates. -/
def vOf (a b c : ℂ) : Fin 6 → ℝ := ![a.re, -a.im, -b.re, b.im, c.re, -c.im]

lemma σK_vOf (a b c : ℂ) : σM (vOf a b c) * Kc = RF a b c := by
  rw [σK_eq]
  have ha : ca (vOf a b c) = a := by apply Complex.ext <;> simp [ca, vOf]
  have hb : cb (vOf a b c) = b := by apply Complex.ext <;> simp [cb, vOf]
  have hc : cc (vOf a b c) = c := by apply Complex.ext <;> simp [cc, vOf]
  rw [ha, hb, hc]; rfl

/-! ### S3: `SU(4)` preserves the real form -/

lemma dualE_RF (a b c : ℂ) : dualE (RF a b c) = (RF a b c).map star := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [dualE, RF, asym]

/-- An antisymmetric `4 × 4` matrix is `asym` of its upper triangle. -/
lemma eq_asym {A : Matrix (Fin 4) (Fin 4) ℂ} (h : Aᵀ = -A) :
    A = asym (A 0 1) (A 0 2) (A 0 3) (A 1 2) (A 1 3) (A 2 3) := by
  have e : ∀ i j, A j i = -A i j := fun i j => by
    have := congrFun (congrFun h i) j; simpa using this
  have d : ∀ i, A i i = 0 := fun i => by
    have := e i i; linear_combination this / 2
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [asym, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first | rfl | exact d _ | exact e _ _

lemma conj_mul_transpose {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    U.map star * Uᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  have := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one] at this
  have hs : (star U)ᵀ = U.map star := by
    refine Matrix.ext fun i j => ?_; simp [Matrix.star_apply]
  rwa [hs] at this

/-- **`SU(4)` preserves the real form**: `U · RF(a,b,c) · Uᵀ = RF(a', b', c')`. -/
theorem su4_preserves {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ)
    (a b c : ℂ) : ∃ a' b' c', U * RF a b c * Uᵀ = RF a' b' c' := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hU
  set A' := U * RF a b c * Uᵀ
  have hanti : A'ᵀ = -A' := by
    have hR : (RF a b c)ᵀ = -RF a b c := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [RF, asym]
    simp only [A', Matrix.transpose_mul, Matrix.transpose_transpose, hR, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
  have hA := eq_asym hanti
  -- reality: `⋆A' = conj A'`
  have hlam := lam2 U (a) (b) (c) (star c) (-star b) (star a)
  rw [show asym a b c (star c) (-star b) (star a) = RF a b c from rfl, hdet, one_smul, dualE_RF] at hlam
  have hlam' : dualE (U * RF a b c * Uᵀ) = A'.map star := by
    have hc := conj_mul_transpose hu
    have hu' : U * Uᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hu
    calc dualE (U * RF a b c * Uᵀ)
        = (U.map star * Uᵀ) * dualE (U * RF a b c * Uᵀ) * (U * Uᴴ) := by rw [hc, hu', one_mul, mul_one]
      _ = U.map star * (Uᵀ * dualE (U * RF a b c * Uᵀ) * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U.map star * (RF a b c).map star * Uᴴ := by rw [hlam]
      _ = A'.map star := by
        have hm : ∀ M N : Matrix (Fin 4) (Fin 4) ℂ, (M * N).map star = M.map star * N.map star :=
          fun M N => by
            have := Matrix.map_mul (L := M) (M := N) (f := starRingEnd ℂ)
            simpa using this
        rw [hm, hm]; rfl
  have e01 : A' 2 3 = star (A' 0 1) := by
    have := congrFun (congrFun hlam' 0) 1; simpa [dualE] using this
  have e02 : A' 1 3 = -star (A' 0 2) := by
    have := congrFun (congrFun hlam' 0) 2; simp [dualE] at this
    show (U * RF a b c * Uᵀ) 1 3 = _
    rw [← neg_neg ((U * RF a b c * Uᵀ) 1 3), this]; rfl
  have e03 : A' 1 2 = star (A' 0 3) := by
    have := congrFun (congrFun hlam' 0) 3; simpa [dualE] using this
  refine ⟨A' 0 1, A' 0 2, A' 0 3, ?_⟩
  calc A' = asym (A' 0 1) (A' 0 2) (A' 0 3) (A' 1 2) (A' 1 3) (A' 2 3) := hA
    _ = RF (A' 0 1) (A' 0 2) (A' 0 3) := by rw [e01, e02, e03]; rfl

/-! ### S3: the map `T_U` -/

/-- Pfaffian of a `4 × 4` matrix (from its upper triangle). -/
def pf {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : R :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- **`Pf(U A Uᵀ) = det U · Pf A`** for antisymmetric `A`. -/
theorem pf_conj {R : Type*} [CommRing R] (U : Matrix (Fin 4) (Fin 4) R) (a b c d e f : R) :
    pf (U * asym a b c d e f * Uᵀ) = U.det * pf (asym a b c d e f) := by
  simp [pf, asym, Matrix.mul_apply, Fin.sum_univ_four, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring

lemma pf_σK (v : Fin 6 → ℝ) : pf (σM v * Kc) = ((Q6 v : ℝ) : ℂ) := by
  rw [σK_eq]
  apply Complex.ext
  · rw [Complex.ofReal_re, Q6_apply]
    simp [pf, asym, ca, cb, cc, Fin.sum_univ_succ]; ring
  · rw [Complex.ofReal_im]
    simp [pf, asym, ca, cb, cc]; ring

lemma Kc_sq : Kc * Kc = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Kc, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

lemma σK_injective {v w : Fin 6 → ℝ} (h : σM v * Kc = σM w * Kc) : v = w := by
  apply σM_injective
  have := congrArg (· * Kc) h
  simpa [Matrix.mul_assoc, Kc_sq] using this

lemma σK_RF (v : Fin 6 → ℝ) : σM v * Kc = RF (ca v) (cb v) (cc v) := σK_eq v

/-- `T_U v`: the real-form coordinates of `U σ(v) K Uᵀ`. Meaningful for `U ∈ SU(4)` (`σK_TU`);
for other `U` it only reads off the first row. -/
noncomputable def TU (U : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 6 → ℝ) : Fin 6 → ℝ :=
  vOf ((U * (σM v * Kc) * Uᵀ) 0 1) ((U * (σM v * Kc) * Uᵀ) 0 2) ((U * (σM v * Kc) * Uᵀ) 0 3)

/-- **Defining property**: `σ(T_U v) K = U σ(v) K Uᵀ` for `U ∈ SU(4)`. -/
theorem σK_TU {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ)
    (v : Fin 6 → ℝ) : σM (TU U v) * Kc = U * (σM v * Kc) * Uᵀ := by
  obtain ⟨a', b', c', h⟩ := su4_preserves hU (ca v) (cb v) (cc v)
  rw [← σK_RF] at h
  rw [TU, σK_vOf, h]
  have e1 : (RF a' b' c') 0 1 = a' := rfl
  have e2 : (RF a' b' c') 0 2 = b' := rfl
  have e3 : (RF a' b' c') 0 3 = c' := rfl
  rw [e1, e2, e3]

lemma TU_isometry {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ)
    (v : Fin 6 → ℝ) : Q6 (TU U v) = Q6 v := by
  have h := congrArg pf (σK_TU hU v)
  rw [pf_σK, σK_RF, show RF (ca v) (cb v) (cc v) = asym _ _ _ _ _ _ from rfl, pf_conj,
    show asym (ca v) (cb v) (cc v) _ _ _ = RF (ca v) (cb v) (cc v) from rfl, ← σK_RF, pf_σK,
    (Matrix.mem_specialUnitaryGroup_iff.mp hU).2, one_mul] at h
  exact_mod_cast h

lemma TU_mul {U V : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ)
    (hV : V ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ) (v : Fin 6 → ℝ) :
    TU (U * V) v = TU U (TU V v) := by
  apply σK_injective
  rw [σK_TU (Submonoid.mul_mem _ hU hV), σK_TU hU, σK_TU hV, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- `T_U` as a real-linear map. -/
noncomputable def TUL {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ) :
    Module.End ℝ (Fin 6 → ℝ) where
  toFun := TU U
  map_add' v w := by
    apply σK_injective
    have hl : ∀ u : Fin 6 → ℝ, σM u = σL u := fun _ => rfl
    rw [σK_TU hU, hl (TU U v + TU U w), map_add, ← hl, ← hl, Matrix.add_mul, σK_TU hU, σK_TU hU,
      hl (v + w), map_add, ← hl, ← hl, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
  map_smul' c v := by
    apply σK_injective
    have hl : ∀ u : Fin 6 → ℝ, σM u = σL u := fun _ => rfl
    rw [σK_TU hU, RingHom.id_apply, hl (c • TU U v), map_smul, ← hl, Matrix.smul_mul, σK_TU hU,
      hl (c • v), map_smul, ← hl, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

end GU.Spinor
