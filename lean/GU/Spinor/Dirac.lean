import GU.Spinor.Gamma
import GU.Geometry.IndefUnitary

/-!
# The Dirac representation `ρ_D : Spin(7,7) → U(64,64)` (closing roadblock R4, part 2)

* `C` is the spinor bilinear form. It is the tensor product `ε ⊗ σ₁ ⊗ ε ⊗ σ₁ ⊗ ε ⊗ σ₁ ⊗ ε`,
  chosen so that `C γ_g = -γ_gᵀ C` for every generator. We prove `Cᵀ = C`, `C² = 1` and
  `tr C = 0`, so `C` is a symmetric form of split signature (64,64).
* `Γ = σ₃^{⊗7}` is the chirality operator: it anticommutes with every `γ`, and `C Γ = -Γ C`.
  So `C` pairs left-handed with right-handed Weyl spinors, as the draft's metric (3.24) does.
* `cliffordRep_star`: `ρ(x*) = C ρ(x)ᵀ C`, where `*` is Mathlib's Clifford conjugation (reverse ∘
  involute). This is exactly the draft's adjoint (p.23, after (3.27)): "canonical automorphism
  composed with reversal".
* Identification with (3.24): `C` is Spin-invariant and pairs `S̸_L` with `S̸_R`. The
  Spin(7,7)-invariant pairing is unique up to scale (half-spin representations are irreducible
  of real type), and scale does not change `U(C)`. That standard uniqueness step is *not*
  formalised here.
* The SO(64,64) step of (3.30) is only implicit: `spin_preserves_C` shows `ρ(x)` is real and
  `C`-orthogonal, but `det = 1` is not proved. For `x ∈ Spin(7,7)`, `x* x = 1` then gives `ρ(x)ᵀ C ρ(x) = C`.
* `rhoD : Spin77 →* UC`, with `UC` the unitary group of the complexified `C`, i.e. `U(64,64)`
  in the draft's own basis (3.24). Even elements commute with `Γ` (`spin_commutes_Γ`), giving the
  Weyl splitting (3.25).

Faithfulness (the `↪` of (3.28)) is not proved here.
-/

namespace GU.Spinor

open Matrix

/-- Slot pattern of `C`: `ε` in even slots, `σ₁` in odd slots. -/
def csym (j : Fin 7) : F2 := if (j : ℕ) % 2 = 0 then .ep else .s1

/-- The spinor bilinear form. -/
def C : M128 := tprod (fun j => F2.toM (csym j))

/-- Chirality operator `σ₃^{⊗7}`. -/
def Γ : M128 := tprod (fun _ => F2.toM .s3)

namespace F2

/-- `c a = (sgn c a · tr a) • aᵀ c`. -/
theorem comm_transpose (c a : F2) :
    toM c * toM a = ((sgn c a * tr a : ℤ) : ℝ) • ((toM a)ᵀ * toM c) := by
  cases c <;> cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [toM, sgn, tr, mul_apply, Fin.sum_univ_two]

end F2

theorem C_gamma (g : Gen) : C * gamma g = -((gamma g)ᵀ * C) := by
  have hs : ∏ j, (F2.sgn (csym j) (sym g j) * F2.tr (sym g j)) = -1 := by
    revert g; decide
  rw [C, gamma, tprod_transpose, tprod_mul, tprod_mul]
  have : (fun j => F2.toM (csym j) * F2.toM (sym g j))
      = fun j => ((F2.sgn (csym j) (sym g j) * F2.tr (sym g j) : ℤ) : ℝ) •
          ((F2.toM (sym g j))ᵀ * F2.toM (csym j)) := by
    funext j; exact F2.comm_transpose _ _
  rw [this, tprod_smul, ← Int.cast_prod, hs]
  simp

theorem C_mul_C : C * C = 1 := by
  have hs : ∏ j, F2.sq (csym j) = 1 := by decide
  rw [C, tprod_mul]
  simp_rw [F2.square]
  rw [tprod_smul, tprod_one, ← Int.cast_prod, hs]
  simp

theorem C_transpose : Cᵀ = C := by
  have hs : ∏ j, F2.tr (csym j) = 1 := by decide
  rw [C, tprod_transpose]
  simp_rw [F2.transpose]
  rw [tprod_smul, ← Int.cast_prod, hs]
  simp

/-- `tr C = 0`: with `C² = 1` and `Cᵀ = C`, the `±1` eigenspaces have dimension 64 each. -/
theorem C_trace : trace C = 0 := by
  rw [trace, Finset.sum_eq_zero]
  intro a _
  simp only [C, tprod, diag_apply, of_apply]
  refine Finset.prod_eq_zero (i := 0) (Finset.mem_univ _) ?_
  have : csym 0 = .ep := rfl
  rw [this]
  generalize a 0 = b
  fin_cases b <;> simp [F2.toM]

theorem Γ_gamma (g : Gen) : Γ * gamma g = -(gamma g * Γ) := by
  have hs : ∏ j, F2.sgn .s3 (sym g j) = -1 := by revert g; decide
  rw [Γ, gamma, tprod_mul, tprod_mul]
  simp_rw [F2.comm .s3]
  rw [tprod_smul, ← Int.cast_prod, hs]
  simp

theorem Γ_mul_Γ : Γ * Γ = 1 := by
  rw [Γ, tprod_mul]; simp_rw [F2.square]
  rw [tprod_smul, tprod_one]; simp [F2.sq]

/-- `C` anticommutes with chirality: the form pairs `S̸_L` with `S̸_R` (draft (3.24)). -/
theorem C_Γ : C * Γ = -(Γ * C) := by
  have hs : ∏ j, F2.sgn (csym j) .s3 = -1 := by decide
  rw [C, Γ, tprod_mul, tprod_mul]
  simp_rw [F2.comm (csym _) .s3]
  rw [tprod_smul, ← Int.cast_prod, hs]
  simp

lemma gamma_transpose_conj (g : Gen) : C * (gamma g)ᵀ * C = -gamma g := by
  have h1 : (gamma g)ᵀ * C = -(C * gamma g) := by rw [C_gamma, neg_neg]
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, C_mul_C, Matrix.one_mul]

lemma gammaMap_transpose_conj (v : Fin 14 → ℝ) : C * (gammaMap v)ᵀ * C = -gammaMap v := by
  simp only [gammaMap, LinearMap.coe_mk, AddHom.coe_mk, transpose_sum, transpose_smul,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, gamma_transpose_conj,
    smul_neg, Finset.sum_neg_distrib]

/-- `ρ(x*) = C ρ(x)ᵀ C`. -/
theorem cliffordRep_star (x : Cl77) : cliffordRep (star x) = C * (cliffordRep x)ᵀ * C := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [CliffordAlgebra.star_algebraMap, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      transpose_smul, transpose_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, C_mul_C]
  | ι v => rw [CliffordAlgebra.star_ι, map_neg, cliffordRep_ι, gammaMap_transpose_conj]
  | mul a b ha hb =>
    rw [star_mul, map_mul, map_mul, ha, hb, transpose_mul]
    calc C * (cliffordRep b)ᵀ * C * (C * (cliffordRep a)ᵀ * C)
        = C * (cliffordRep b)ᵀ * (C * C) * (cliffordRep a)ᵀ * C := by
          simp only [Matrix.mul_assoc]
      _ = C * ((cliffordRep b)ᵀ * (cliffordRep a)ᵀ) * C := by
          rw [C_mul_C, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  | add a b ha hb =>
    rw [star_add, map_add, map_add, ha, hb, transpose_add, Matrix.mul_add, Matrix.add_mul]

/-- `Γ ρ(x) Γ = ρ(involute x)`. -/
theorem Γ_conj (x : Cl77) : Γ * cliffordRep x * Γ = cliffordRep (CliffordAlgebra.involute x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Γ_mul_Γ]
    exact ((cliffordRep.commutes r).trans (Algebra.algebraMap_eq_smul_one r)).symm
  | ι v =>
    rw [CliffordAlgebra.involute_ι, map_neg, cliffordRep_ι]
    simp only [gammaMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_neg_distrib, ← smul_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Γ_gamma, Matrix.neg_mul, Matrix.mul_assoc, Γ_mul_Γ, Matrix.mul_one]
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, ← ha, ← hb]
    calc Γ * (cliffordRep a * cliffordRep b) * Γ
        = Γ * cliffordRep a * (Γ * Γ) * cliffordRep b * Γ := by
          rw [Γ_mul_Γ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Γ * cliffordRep a * Γ * (Γ * cliffordRep b * Γ) := by simp only [Matrix.mul_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ← ha, ← hb, Matrix.mul_add, Matrix.add_mul]

/-- Spin elements preserve `C`: `ρ(x)ᵀ C ρ(x) = C`. -/
theorem spin_preserves_C (x : Spin77) :
    (cliffordRep x)ᵀ * C * cliffordRep x = C := by
  have h : cliffordRep (star (x : Cl77)) * cliffordRep x = 1 := by
    rw [← map_mul, spinGroup.star_mul_self_of_mem x.2, map_one]
  rw [cliffordRep_star] at h
  calc (cliffordRep x)ᵀ * C * cliffordRep x
      = C * (C * (cliffordRep x)ᵀ * C * cliffordRep x) := by
        simp only [← Matrix.mul_assoc, C_mul_C, Matrix.one_mul]
    _ = C := by rw [h, Matrix.mul_one]

/-- Spin elements commute with chirality, so they preserve `S̸_L` and `S̸_R` (3.25). -/
theorem spin_commutes_Γ (x : Spin77) : Γ * cliffordRep x = cliffordRep x * Γ := by
  have hx : CliffordAlgebra.involute (x : Cl77) = x :=
    CliffordAlgebra.involute_eq_of_mem_even ((spinGroup.mem_iff.mp x.2).2)
  have := Γ_conj (x : Cl77)
  rw [hx] at this
  calc Γ * cliffordRep x = Γ * cliffordRep x * Γ * Γ := by
        rw [Matrix.mul_assoc _ Γ Γ, Γ_mul_Γ, Matrix.mul_one]
    _ = cliffordRep x * Γ := by rw [this]

/-! ### Complexification and the unitary group of `C` -/

/-- Real matrix viewed as complex. -/
def toC (A : M128) : Matrix Idx Idx ℂ := A.map Complex.ofRealHom

lemma toC_mul (A B : M128) : toC (A * B) = toC A * toC B := Matrix.map_mul

lemma toC_conjTranspose (A : M128) : (toC A)ᴴ = toC Aᵀ := by
  ext i j; simp [toC]

/-- The complexified spinor form. -/
def Cc : Matrix Idx Idx ℂ := toC C

lemma Cc_mul_Cc : Cc * Cc = 1 := by
  rw [Cc, ← toC_mul, C_mul_C, toC, Matrix.map_one] <;> simp

lemma Cc_conjTranspose : Ccᴴ = Cc := by rw [Cc, toC_conjTranspose, C_transpose]

/-- `U(64,64)` in the draft's basis (3.24): the unitary group of the split Hermitian form `C`. -/
abbrev UC : Type := ↥(indefUnitary Cc)

instance : Group UC :=
  { (inferInstance : Monoid UC) with
    inv := fun A => ⟨Cc * A.1ᴴ * Cc, indefUnitary_inv_mem Cc_mul_Cc Cc_conjTranspose A.2⟩
    inv_mul_cancel := fun A => Subtype.ext (indefUnitary_left_inv Cc_mul_Cc A.2) }

lemma rho_mem (x : Spin77) : toC (cliffordRep x) ∈ indefUnitary Cc := by
  show (toC (cliffordRep x))ᴴ * Cc * toC (cliffordRep x) = Cc
  rw [toC_conjTranspose, Cc, ← toC_mul, ← toC_mul, spin_preserves_C]

/-- **The Dirac representation** `ρ_D : Spin(7,7) → U(64,64)` (3.31), constructed explicitly. -/
def rhoD : Spin77 →* UC where
  toFun x := ⟨toC (cliffordRep x), rho_mem x⟩
  map_one' := Subtype.ext (by simp [toC, Matrix.map_one])
  map_mul' x y := Subtype.ext (by simp [toC_mul])

end GU.Spinor
