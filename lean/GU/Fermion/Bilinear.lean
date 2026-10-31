import GU.Spinor.Dirac

/-!
# Fermion pairings valued in `ad = u(64,64)` (gap in (9.18))

Note: `μ` is sesquilinear (it uses `χᴴ`), not complex-bilinear.

The draft writes `ν̄ζ + ζ̄ν + ⧉ζ̄ζ ∈ Ω^{d−1}(Y, ad)` but never defines the pairing
`S̸ ⊗ S̸ → ad`.

-- AI_BREAKTHROUGH_PATCH_V1 (synthetic operator): `μ(ψ, χ) = i (ψ χᴴ + χ ψᴴ) C`.

Proved:
* `mu_mem_u`: `μ(ψ,χ)` lies in the Lie algebra `u(C) = {X | Xᴴ C + C X = 0}`, the Lie algebra of
  the draft's `H = U(64,64)` in the basis (3.24).
* `mu_equivariant`: for `g ∈ Spin(7,7)`, `μ(ρg ψ, ρg χ) = ρg μ(ψ,χ) ρg⁻¹`, with
  `ρg⁻¹ = C ρgᴴ C` (from `spin_preserves_C`). So `μ` is gauge covariant.
* `mu_symm`: `μ` is symmetric. With Grassmann-odd fields this becomes the antisymmetric pairing
  physics needs; Grassmann parity is not modelled here.
-/

namespace GU.Spinor

open Matrix Complex

abbrev Sp := Idx → ℂ

/-- Lie algebra of `U(C)`. -/
def uC : Set (Matrix Idx Idx ℂ) := {X | Xᴴ * Cc + Cc * X = 0}

/-- Outer product `ψ χᴴ`. -/
def outer (ψ χ : Sp) : Matrix Idx Idx ℂ := Matrix.of fun i j => ψ i * star (χ j)

lemma outer_conjTranspose (ψ χ : Sp) : (outer ψ χ)ᴴ = outer χ ψ := by
  ext i j; simp [outer, mul_comm]

noncomputable def mu (ψ χ : Sp) : Matrix Idx Idx ℂ := (I • (outer ψ χ + outer χ ψ)) * Cc

theorem mu_symm (ψ χ : Sp) : mu ψ χ = mu χ ψ := by
  simp [mu, add_comm]

theorem mu_mem_u (ψ χ : Sp) : mu ψ χ ∈ uC := by
  show (mu ψ χ)ᴴ * Cc + Cc * mu ψ χ = 0
  simp only [mu, conjTranspose_mul, conjTranspose_smul, conjTranspose_add, outer_conjTranspose,
    Cc_conjTranspose, star_def, conj_I, Matrix.smul_mul, Matrix.mul_smul]
  rw [add_comm (outer χ ψ) (outer ψ χ), neg_smul, Matrix.mul_assoc, neg_add_cancel]

lemma outer_mulVec (A : Matrix Idx Idx ℂ) (ψ χ : Sp) :
    outer (A *ᵥ ψ) (A *ᵥ χ) = A * outer ψ χ * Aᴴ := by
  ext i j
  simp only [outer, of_apply, mulVec, dotProduct, mul_apply, conjTranspose_apply, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem mu_equivariant (g : Spin77) (ψ χ : Sp) :
    let R := toC (cliffordRep g)
    mu (R *ᵥ ψ) (R *ᵥ χ) = R * mu ψ χ * (Cc * Rᴴ * Cc) := by
  intro R
  have hR : Rᴴ * Cc * R = Cc := (rho_mem g)
  have hinv : (Cc * Rᴴ * Cc) * R = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hR, Cc_mul_Cc]
  have hinv' : R * (Cc * Rᴴ * Cc) = 1 := mul_eq_one_comm.mp hinv
  have e : R * (outer ψ χ + outer χ ψ) * Rᴴ = R * outer ψ χ * Rᴴ + R * outer χ ψ * Rᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have e2 : R * ((outer ψ χ + outer χ ψ) * Cc) * (Cc * Rᴴ * Cc)
      = R * (outer ψ χ + outer χ ψ) * Rᴴ * Cc := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Cc Cc, Cc_mul_Cc, Matrix.one_mul]
  simp only [mu, outer_mulVec]
  rw [← e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, e2]

end GU.Spinor
