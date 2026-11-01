/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.CliffordBianchi
import GU.Spinor.Gamma

/-!
# Einstein tensor from the Shiab contraction (9.3), pointwise

Combining `ricci_term` (commutator bracket) and `scalar_term_anticomm` (anticommutator
brackets), the Clifford-algebra core of (9.3) applied to a Riemann-type curvature is

  `𝒮_b = [Ricci term]_b + ½ · [scalar term] · γ_b = 4 Σ_y w_y G_by γ_y`,

with `G = Ric − ½ R g` the Einstein tensor. This is the precise sense in which (9.3) "makes
the parallel to Einstein's contraction explicit" (§9.1), and the Weyl part drops out.

Caveats:
* The brackets must be mixed: commutator in the Ricci term, anticommutator in the scalar term.
  With a uniform choice, one of the two terms vanishes identically (`ricci_term_anticomm`,
  `scalar_term_comm`).
* Hodge stars, wedges, `ε`-conjugation and the passage from (9.3) to these index sums are
  checked only numerically (experiments/shiab_weyl.py), not in Lean. The theorem covers
  Riemann-type `ξ` (values in `Λ²`), not general `u(64,64)`-valued `ξ`.
* The relative *sign* of the two terms is convention-dependent: it flips with `sign(det η)`
  (from `⋆⋆`), with the Clifford convention `γ² = ±η` (cubic vs quintic in `γ`), and with the
  draft's `i·{,}` anticommutator (8.1). So no conclusion about the printed `−½` is drawn.
* Normalisation: the outer anticommutator `{γ_b, S} = 2Sγ_b` is replaced here by `S·γ_b`, which
  compensates the factor 2 from the draft's `a<c` convention for `Φ₂`. That is how the
  relative `½` matches.
-/

namespace GU.CliffordBianchi

open Finset

variable {A : Type*} [Ring A] [Algebra ℝ A] {n : ℕ} {w : Fin n → ℝ} {γ : Fin n → A}

variable (w) in
/-- Einstein tensor `G_by = Ric_by − ½ R g_by` with `g_by = w_b δ_by`. -/
noncomputable def einstein (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b y : Fin n) : ℝ :=
  ric w R b y - (1 / 2) * scal w R * (if b = y then w b else 0)

/-- **GR emergence, pointwise.** -/
theorem shiab_einstein (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) (b : Fin n) :
    (∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) - γ x * γ y * γ a))
      + (1 / 2 : ℝ) • ((∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
          (γ a * γ c * (γ x * γ y) + γ x * γ y * (γ a * γ c))) * γ b)
      = (4 : ℝ) • ∑ y, (w y * einstein w R b y) • γ y := by
  rw [ricci_term h hw hR b, scalar_term_anticomm h hw hR, smul_mul_assoc, one_mul]
  simp only [einstein, mul_sub, sub_smul, sum_sub_distrib, smul_sub]
  have e : ∑ y, (w y * ((1 / 2) * scal w R * (if b = y then w b else 0))) • γ y
      = ((1 / 2) * scal w R) • γ b := by
    rw [Finset.sum_eq_single b (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
    simp only [ite_true]
    congr 1
    linear_combination ((1 / 2) * scal w R) * hw b
  rw [e, smul_smul]
  have : (1 / 2 : ℝ) * (-4 * scal w R) = -(4 * ((1 / 2) * scal w R)) := by ring
  rw [this, neg_smul, ← sub_eq_add_neg, smul_smul]

/-- On Ricci-flat curvature (in particular pure Weyl) the Shiab core vanishes. -/
theorem shiab_weyl (h : IsClifford w γ) (hw : ∀ a, w a * w a = 1)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : AlgCurv R) (hRic : ∀ b d, ric w R b d = 0)
    (b : Fin n) :
    (∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) • (γ a * (γ x * γ y) - γ x * γ y * γ a))
      + (1 / 2 : ℝ) • ((∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
          (γ a * γ c * (γ x * γ y) + γ x * γ y * (γ a * γ c))) * γ b) = 0 := by
  rw [shiab_einstein h hw hR b]
  have hs : scal w R = 0 := by simp [scal, hRic]
  simp [einstein, hRic, hs]

end GU.CliffordBianchi

namespace GU.Spinor

open GU.CliffordBianchi

/-- The explicit 128×128 Cl(7,7) gammas satisfy the abstract Clifford relations. -/
theorem gamma77_isClifford : IsClifford w (fun i => gamma (gen i)) := by
  intro a b
  rw [anticomm]
  rfl

theorem w77_sq (a : Fin 14) : w a * w a = 1 := by
  unfold w; split_ifs <;> norm_num

/-- Clifford-algebra core of (9.3) at `ℝ^{7,7}` with the draft's own gamma matrices: for every
algebraic curvature tensor, the (mixed-bracket) contraction sums give `4·G·γ`. See the module
caveats: forms and Hodge stars are not modelled. -/
theorem shiab_einstein_77 {R : Fin 14 → Fin 14 → Fin 14 → Fin 14 → ℝ} (hR : AlgCurv R)
    (b : Fin 14) :
    (∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) •
        (gamma (gen a) * (gamma (gen x) * gamma (gen y)) - gamma (gen x) * gamma (gen y) * gamma (gen a)))
      + (1 / 2 : ℝ) • ((∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
          (gamma (gen a) * gamma (gen c) * (gamma (gen x) * gamma (gen y))
            + gamma (gen x) * gamma (gen y) * (gamma (gen a) * gamma (gen c)))) * gamma (gen b))
      = (4 : ℝ) • ∑ y, (w y * einstein w R b y) • gamma (gen y) :=
  shiab_einstein gamma77_isClifford w77_sq hR b

end GU.Spinor
