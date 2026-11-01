/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Fermion.Bilinear
import GU.Spinor.Faithful

/-!
# The draft's (3.27): `u(64,64)` inside `Cl(7,7) ⊗ ℂ`, and the placement of `i` (blueprint B7)

`u(C) = {Z ∈ ℂ(128) | Zᴴ C + C Z = 0}` is (by the standard definition, not derived here) the Lie
algebra of `U(64,64) = UC`. Writing `Z = A + iB`:
`Z ∈ u(C) ↔ Aᵀ C + C A = 0 ∧ Bᵀ C = C B` (`mem_uC_iff`). Since `ρ(y*) = C ρ(y)ᵀ C`
(`cliffordRep_star`, `*` = Clifford conjugation = the draft's "canonical automorphism composed with
reversal"), the real part is `ρ` of a `*`-antisymmetric element and the imaginary part is `ρ` of a
`*`-symmetric one. So

  `Ψ y = ρ(y⁻) + i ρ(y⁺)`,  `y^± = (y ± y*)/2`

is a bijection `Cl(7,7) → u(64,64)` (`uEquiv`), real-linear (`Ψu_add`, `Ψu_smul`), intertwining the adjoint actions:
`Ψ(x y x*) = ρ_D(x) Ψ(y) ρ_D(x)⁻¹` for `x ∈ Spin(7,7)` (`Ψu_equivariant`).

On a basis blade of `k` distinct vectors, `star = (−1 if k ≡ 1,2 mod 4 else +1)` (`star_blade`), so
`Ψ` puts `Λ^k` in the real part iff `k ≡ 1, 2 (mod 4)` and in the `i`-part iff `k ≡ 0, 3 (mod 4)`
(`Ψu_blade`, stated per blade; it extends to spans by linearity). That is exactly the draft's (3.27),
`u(64,64) = ⊕Λ^{4i+2} ⊕ ⊕iΛ^{4i} ⊕ ⊕Λ^{4i+1} ⊕ ⊕iΛ^{4i+3}`: **the placement of `i` is correct**, and
the identification is Spin(7,7)-equivariant. (Here `Λ^k` means the span of `k`-blades inside
`Cl(7,7)`; that the blades span `Cl(7,7)`, and the identification with the exterior power
`Λ^k ℝ¹⁴` (Chevalley map), are standard and not formalised.)

Scope: `Ψ` is a map of real vector spaces and Spin(7,7)-modules, **not** of Lie algebras. This settles
the linear statement (3.27). It does not touch Nguyen–Polya's complexification objection, which is
about the Shiab *operator*: Clifford products of `u`-elements leave `u` (e.g. `Λ¹ · Λ² ∋ Λ³`, real
times real gives a grade whose `u`-slot is imaginary), so an `i` must be inserted by hand. Compare
B3, where the scalar term needs an anticommutator, which is Hermitian.
-/

namespace GU.Spinor

open Matrix

/-- Real and imaginary parts of a complex matrix. -/
def reM (Z : Matrix Idx Idx ℂ) : M128 := Z.map Complex.re
def imM (Z : Matrix Idx Idx ℂ) : M128 := Z.map Complex.im

-- `uC = {Z | Zᴴ Cc + Cc Z = 0}`, the Lie algebra `u(64,64)`, is defined in `GU.Fermion.Bilinear`.

lemma mem_uC_iff (Z : Matrix Idx Idx ℂ) :
    Z ∈ uC ↔ (reM Z)ᵀ * C + C * reM Z = 0 ∧ (imM Z)ᵀ * C = C * imM Z := by
  have key : ∀ i j, (Zᴴ * Cc + Cc * Z) i j =
      ⟨((reM Z)ᵀ * C + C * reM Z) i j, (C * imM Z - (imM Z)ᵀ * C) i j⟩ := fun i j => by
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Cc, toC, reM, imM, Complex.re_sum, Complex.im_sum] <;> ring
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> ext i j <;> have := congrFun (congrFun h i) j <;>
      rw [key] at this <;> simp only [Matrix.zero_apply, Complex.ext_iff, Complex.zero_re,
        Complex.zero_im] at this
    · exact this.1
    · have := this.2; rw [Matrix.sub_apply] at this; linarith
  · rintro ⟨h1, h2⟩
    ext i j
    rw [key, h1, h2, sub_self]; rfl

lemma rep_transpose_C (x : Cl77) : (cliffordRep x)ᵀ * C = C * cliffordRep (star x) := by
  rw [cliffordRep_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, C_mul_C, Matrix.one_mul]

/-- `*`-antisymmetric and `*`-symmetric parts. -/
noncomputable def antiP (y : Cl77) : Cl77 := (1 / 2 : ℝ) • (y - star y)
noncomputable def symP (y : Cl77) : Cl77 := (1 / 2 : ℝ) • (y + star y)

lemma star_antiP (y : Cl77) : star (antiP y) = -antiP y := by
  unfold antiP; rw [CliffordAlgebra.star_smul, star_sub, star_star, ← smul_neg, neg_sub]

lemma star_symP (y : Cl77) : star (symP y) = symP y := by
  unfold symP; rw [CliffordAlgebra.star_smul, star_add, star_star, add_comm]

lemma antiP_add_symP (y : Cl77) : antiP y + symP y = y := by
  unfold antiP symP
  rw [← smul_add, show y - star y + (y + star y) = (2 : ℝ) • y by rw [two_smul]; abel, smul_smul]
  norm_num


/-- **The draft's identification** `Ψ y = ρ(y⁻) + i ρ(y⁺)`. -/
noncomputable def Ψu (y : Cl77) : Matrix Idx Idx ℂ :=
  toC (cliffordRep (antiP y)) + Complex.I • toC (cliffordRep (symP y))

lemma reM_Ψu (y : Cl77) : reM (Ψu y) = cliffordRep (antiP y) := by
  ext i j; simp [reM, Ψu, toC]

lemma imM_Ψu (y : Cl77) : imM (Ψu y) = cliffordRep (symP y) := by
  ext i j; simp [imM, Ψu, toC]

lemma Ψu_mem (y : Cl77) : Ψu y ∈ uC := by
  rw [mem_uC_iff, reM_Ψu, imM_Ψu, rep_transpose_C, rep_transpose_C, star_antiP, star_symP,
    map_neg, Matrix.mul_neg, neg_add_cancel]
  exact ⟨rfl, rfl⟩

lemma Ψu_injective : Function.Injective Ψu := by
  intro y y' h
  have ha := congrArg reM h
  have hs := congrArg imM h
  rw [reM_Ψu, reM_Ψu] at ha
  rw [imM_Ψu, imM_Ψu] at hs
  rw [← antiP_add_symP y, ← antiP_add_symP y', cliffordRep_bijective.1 ha,
    cliffordRep_bijective.1 hs]

lemma Ψu_surjective (Z : Matrix Idx Idx ℂ) (hZ : Z ∈ uC) : ∃ y, Ψu y = Z := by
  rw [mem_uC_iff] at hZ
  obtain ⟨a, ha⟩ := cliffordRep_bijective.2 (reM Z)
  obtain ⟨b, hb⟩ := cliffordRep_bijective.2 (imM Z)
  have hsa : star a = -a := by
    apply cliffordRep_bijective.1
    have := hZ.1
    rw [← ha, rep_transpose_C] at this
    have h2 : C * (C * cliffordRep (star a) + C * cliffordRep a) = 0 := by rw [this, Matrix.mul_zero]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, C_mul_C, Matrix.one_mul,
      Matrix.one_mul, add_eq_zero_iff_eq_neg] at h2
    rw [h2, map_neg]
  have hsb : star b = b := by
    apply cliffordRep_bijective.1
    have := hZ.2
    rw [← hb, rep_transpose_C] at this
    have h2 := congrArg (C * ·) this
    simp only [← Matrix.mul_assoc, C_mul_C, Matrix.one_mul] at h2
    exact h2
  refine ⟨a + b, ?_⟩
  have h1 : antiP (a + b) = a := by
    unfold antiP
    rw [star_add, hsa, hsb, show a + b - (-a + b) = (2 : ℝ) • a by rw [two_smul]; abel, smul_smul]
    norm_num
  have h2 : symP (a + b) = b := by
    unfold symP
    rw [star_add, hsa, hsb, show a + b + (-a + b) = (2 : ℝ) • b by rw [two_smul]; abel, smul_smul]
    norm_num
  ext i j
  apply Complex.ext
  · have := congrFun (congrFun ha i) j
    simp [Ψu, h1, h2, toC, reM] at this ⊢; exact this
  · have := congrFun (congrFun hb i) j
    simp [Ψu, h1, h2, toC, imM] at this ⊢; exact this

lemma star_conj (x y : Cl77) : star (x * y * star x) = x * star y * star x := by
  rw [star_mul, star_mul, star_star, mul_assoc]

lemma conj_antiP (x y : Cl77) : antiP (x * y * star x) = x * antiP y * star x := by
  unfold antiP; rw [star_conj, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]

lemma conj_symP (x y : Cl77) : symP (x * y * star x) = x * symP y * star x := by
  unfold symP; rw [star_conj, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]

lemma rhoD_inv_val (x : Spin77) : ((rhoD x)⁻¹ : UC).1 = toC (cliffordRep (star (x : Cl77))) := by
  show Cc * (toC (cliffordRep x))ᴴ * Cc = _
  rw [toC_conjTranspose, Cc, ← toC_mul, ← toC_mul, ← cliffordRep_star]

/-- **Equivariance**: `Ψ(x y x⁻¹) = ρ_D(x) Ψ(y) ρ_D(x)⁻¹` for `x ∈ Spin(7,7)` (`x⁻¹ = x*`). -/
theorem Ψu_equivariant (x : Spin77) (y : Cl77) :
    Ψu ((x : Cl77) * y * star (x : Cl77)) = (rhoD x).1 * Ψu y * ((rhoD x)⁻¹ : UC).1 := by
  rw [rhoD_inv_val]
  show _ = toC (cliffordRep x) * Ψu y * toC (cliffordRep (star (x : Cl77)))
  unfold Ψu
  rw [conj_antiP, conj_symP, map_mul, map_mul, map_mul, map_mul, toC_mul, toC_mul, toC_mul,
    toC_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- **`Cl(7,7) ≃ u(64,64)`** as real vector spaces (the draft's (3.27)). -/
noncomputable def uEquiv : Cl77 ≃ uC :=
  Equiv.ofBijective (fun y => ⟨Ψu y, Ψu_mem y⟩)
    ⟨fun _ _ h => Ψu_injective (congrArg Subtype.val h),
     fun Z => (Ψu_surjective Z.1 Z.2).imp fun _ h => Subtype.ext h⟩

-- Same statement as `SMAlgebra.toC_add`; private to avoid a name clash without importing it.
private lemma toC_add (A B : M128) : toC (A + B) = toC A + toC B := by ext; simp [toC]

lemma Ψu_add (y y' : Cl77) : Ψu (y + y') = Ψu y + Ψu y' := by
  unfold Ψu antiP symP
  rw [star_add, add_sub_add_comm, add_add_add_comm, smul_add, smul_add, map_add, map_add,
    toC_add, toC_add, smul_add]
  abel

lemma Ψu_smul (r : ℝ) (y : Cl77) : Ψu (r • y) = (r : ℂ) • Ψu y := by
  unfold Ψu antiP symP
  rw [CliffordAlgebra.star_smul, ← smul_sub, ← smul_add, smul_comm (1 / 2 : ℝ) r,
    smul_comm (1 / 2 : ℝ) r, map_smul, map_smul]
  ext i j; simp [toC]; ring

/-! ### Grade placement: the draft's (3.27) -/

/-- Basis vector `e_i` of `ℝ¹⁴`. -/
noncomputable def eb14 (i : Fin 14) : Fin 14 → ℝ := Pi.single i 1

/-- The basis blade `e_{i₁} ⋯ e_{iₖ}`. -/
noncomputable def blade (l : List (Fin 14)) : Cl77 :=
  (l.map fun i => CliffordAlgebra.ι Q77 (eb14 i)).prod

lemma eb14_ortho {i j : Fin 14} (h : i ≠ j) : Q77.IsOrtho (eb14 i) (eb14 j) := by
  show Q77 (eb14 i + eb14 j) = Q77 (eb14 i) + Q77 (eb14 j)
  simp only [Q77, QuadraticMap.weightedSumSquares_apply, eb14, Pi.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hi : k = i <;> by_cases hj : k = j <;> subst_vars <;>
    simp_all

/-- Moving `e_a` through a blade not containing `a`. -/
lemma blade_mul_ι (a : Fin 14) (l : List (Fin 14)) (ha : a ∉ l) :
    blade l * CliffordAlgebra.ι Q77 (eb14 a) =
      ((-1 : ℝ) ^ l.length) • (CliffordAlgebra.ι Q77 (eb14 a) * blade l) := by
  induction l with
  | nil => simp [blade]
  | cons b l ih =>
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    have hl : a ∉ l := fun h => ha (List.mem_cons_of_mem _ h)
    have hb : blade (b :: l) = CliffordAlgebra.ι Q77 (eb14 b) * blade l := rfl
    rw [hb, mul_assoc, ih hl, mul_smul_comm, ← mul_assoc,
      CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (eb14_ortho (Ne.symm hab)), List.length_cons, pow_succ,
      neg_mul, mul_assoc, smul_neg, ← neg_smul, mul_neg_one]

/-- The sign of Clifford conjugation on a `k`-blade: `−1` iff `k ≡ 1, 2 (mod 4)`. -/
def starSign (k : ℕ) : ℝ := if k % 4 = 1 ∨ k % 4 = 2 then -1 else 1

lemma starSign_succ (m : ℕ) : starSign (m + 1) = -(starSign m * (-1 : ℝ) ^ m) := by
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hpar : (-1 : ℝ) ^ m = if m % 4 = 0 ∨ m % 4 = 2 then 1 else -1 := by
    rcases Nat.even_or_odd m with he | ho
    · rw [he.neg_one_pow]; obtain ⟨t, rfl⟩ := he; split_ifs with h <;> [rfl; omega]
    · rw [ho.neg_one_pow]; obtain ⟨t, rfl⟩ := ho; split_ifs with h <;> [omega; rfl]
  rw [hpar]; unfold starSign
  interval_cases hm : m % 4 <;> simp [hm, Nat.add_mod]

/-- **Clifford conjugation on a basis blade** of `k` distinct vectors is `starSign k`. -/
theorem star_blade (l : List (Fin 14)) (hl : l.Nodup) :
    star (blade l) = starSign l.length • blade l := by
  induction l with
  | nil => simp [blade, starSign]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hb : blade (a :: l) = CliffordAlgebra.ι Q77 (eb14 a) * blade l := rfl
    rw [hb, star_mul, ih hl.2, CliffordAlgebra.star_ι, mul_neg, smul_mul_assoc,
      blade_mul_ι a l hl.1, smul_smul, List.length_cons, starSign_succ, neg_smul]

/-- **The draft's (3.27) is right**: under `Ψ`, a `k`-blade lands in the real part of `u(64,64)`
iff `k ≡ 1, 2 (mod 4)` (`Λ^{4i+1}`, `Λ^{4i+2}`), and in the `i`-part iff `k ≡ 0, 3 (mod 4)`
(`iΛ^{4i}`, `iΛ^{4i+3}`). -/
theorem Ψu_blade (l : List (Fin 14)) (hl : l.Nodup) :
    ((l.length % 4 = 1 ∨ l.length % 4 = 2) → Ψu (blade l) = toC (cliffordRep (blade l))) ∧
    (¬(l.length % 4 = 1 ∨ l.length % 4 = 2) →
      Ψu (blade l) = Complex.I • toC (cliffordRep (blade l))) := by
  have hs := star_blade l hl
  unfold starSign at hs
  have h0 : toC (cliffordRep (0 : Cl77)) = 0 := by rw [map_zero]; ext; simp [toC]
  constructor
  · intro h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), neg_one_smul] at hs
    have ha : antiP (blade l) = blade l := by
      unfold antiP; rw [hs, sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
    have hsy : symP (blade l) = 0 := by unfold symP; rw [hs, add_neg_cancel, smul_zero]
    rw [Ψu, ha, hsy, h0, smul_zero, add_zero]
  · intro h
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), one_smul] at hs
    have ha : antiP (blade l) = 0 := by unfold antiP; rw [hs, sub_self, smul_zero]
    have hsy : symP (blade l) = blade l := by
      unfold symP; rw [hs, ← two_smul ℝ, smul_smul]; norm_num
    rw [Ψu, ha, hsy, h0, zero_add]

end GU.Spinor
