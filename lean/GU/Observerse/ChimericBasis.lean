/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Observerse.Manifold
import GU.Observerse.Chimeric

/-!
# The chimeric metric at `η` as a bilinear form on `ℝ¹⁴`, with an orthogonal basis

On the model space `E14 = ℝ¹⁰ × ℝ⁴` (`Sym²(ℝ⁴)` in `symMat` coordinates, times `H* = ℝ⁴`), the
chimeric metric at `η` with `λ = 1` is the bilinear form `chimB`. `chimB_basis` gives 14 vectors
with diagonal Gram matrix `diag(chimNorms)` (7 positive, 7 negative entries). They are linearly
independent (`chimVec_linIndep`), hence a basis of the 14-dimensional space (`chimVec_basis`).
So the form has an orthogonal basis of signature (7,7).
-/

namespace GU.Chimeric

open Matrix GU.Observerse

/-- `η` over `ℝ`. -/
def ηr : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1, -1, -1, -1]

lemma symMat_add (v w : Fin 10 → ℝ) : symMat (v + w) = symMat v + symMat w := by
  ext i j; simp [symMat]

lemma symMat_smul (c : ℝ) (v : Fin 10 → ℝ) : symMat (c • v) = c • symMat v := by
  ext i j; simp [symMat]

/-- The chimeric bilinear form at `η`, `λ = 1`, in coordinates. -/
noncomputable def chimB : LinearMap.BilinForm ℝ E14 :=
  LinearMap.mk₂ ℝ
    (fun x y => trace (ηr * symMat x.2 * ηr * symMat y.2) - trace (ηr * symMat x.2) * trace (ηr * symMat y.2)
      + x.1 ⬝ᵥ (ηr *ᵥ y.1))
    (fun x x' y => by
      simp only [Prod.snd_add, Prod.fst_add, symMat_add, Matrix.mul_add, Matrix.add_mul, trace_add,
        add_dotProduct]; ring)
    (fun c x y => by
      simp only [Prod.smul_snd, Prod.smul_fst, symMat_smul, Matrix.mul_smul, Matrix.smul_mul, trace_smul,
        smul_dotProduct, smul_eq_mul]; ring)
    (fun x y y' => by
      simp only [Prod.snd_add, Prod.fst_add, symMat_add, Matrix.mul_add, trace_add,
        mulVec_add, dotProduct_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_snd, Prod.smul_fst, symMat_smul, Matrix.mul_smul, trace_smul,
        mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)

/-- Integer coordinates of the 14 basis vectors (`(H*-part, Sym²-part)`). -/
def chimCoord : Fin 14 → (Fin 4 → ℤ) × (Fin 10 → ℤ) :=
  ![(0, Pi.single 1 1), (0, Pi.single 2 1), (0, Pi.single 3 1),
    (0, Pi.single 5 1), (0, Pi.single 6 1), (0, Pi.single 8 1),
    (0, ![1, 0, 0, 0, -1, 0, 0, -1, 0, -1]), (0, ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0]),
    (0, ![1, 0, 0, 0, -1, 0, 0, 2, 0, 0]), (0, ![1, 0, 0, 0, -1, 0, 0, -1, 0, 3]),
    (Pi.single 0 1, 0), (Pi.single 1 1, 0), (Pi.single 2 1, 0), (Pi.single 3 1, 0)]

def chimVec (i : Fin 14) : E14 := (fun k => ((chimCoord i).1 k : ℝ), fun k => ((chimCoord i).2 k : ℝ))

/-- Integer version of `chimB` (computable). -/
def chimBZ (x y : (Fin 4 → ℤ) × (Fin 10 → ℤ)) : ℤ :=
  let sx : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j => x.2 (symIdx i j)
  let sy : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j => y.2 (symIdx i j)
  trace (ηZ * sx * ηZ * sy) - trace (ηZ * sx) * trace (ηZ * sy) + x.1 ⬝ᵥ (ηZ *ᵥ y.1)

theorem chimBZ_gram : ∀ i j : Fin 14,
    chimBZ (chimCoord i) (chimCoord j) = if i = j then chimNorms i else 0 := by decide

lemma chimB_cast (i j : Fin 14) : chimB (chimVec i) (chimVec j) = (chimBZ (chimCoord i) (chimCoord j) : ℝ) := by
  simp only [chimB, LinearMap.mk₂_apply, chimBZ, chimVec, ηr, ηZ, symMat]
  simp [trace, Fin.sum_univ_four, mul_apply, dotProduct, mulVec, diagonal]

/-- Orthogonal basis vectors with the expected norms. -/
theorem chimB_basis (i j : Fin 14) :
    chimB (chimVec i) (chimVec j) = if i = j then (chimNorms i : ℝ) else 0 := by
  rw [chimB_cast, chimBZ_gram]; split_ifs <;> simp

theorem chimVec_linIndep : LinearIndependent ℝ chimVec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun v => chimB v (chimVec j)) hg
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, chimB_basis, map_zero,
    LinearMap.zero_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)] at h
  simp only [ite_true] at h
  have hn : (chimNorms j : ℝ) ≠ 0 := by
    have : chimNorms j ≠ 0 := (by decide : ∀ k : Fin 14, chimNorms k ≠ 0) j
    exact_mod_cast this
  exact (mul_eq_zero.mp h).resolve_right hn

/-- The 14 vectors form a basis of `E14`. -/
noncomputable def chimVec_basis : Module.Basis (Fin 14) ℝ E14 :=
  basisOfLinearIndependentOfCardEqFinrank chimVec_linIndep (by rw [finrank_E14]; simp)

end GU.Chimeric
