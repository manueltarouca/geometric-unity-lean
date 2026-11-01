/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.LieU6464

/-!
# The trace pairing behind `‖Υ‖²` (9.11) is indefinite (confirms blueprint §9.2)

The draft's `I₂ᴮ = ‖Υ‖²` (9.11) pairs `Υ ∈ Ω¹³(Y, ad)` via `Tr(· ∧ ⋆ ·)` (cf. (9.4)). Explicit
elements of `ad = u(64,64)` in the draft's own basis (via `Ψu`), with `e₀, e₁` positive and `e₇`
negative basis vectors of `ℝ⁷'⁷`:
* `Zminus = ρ(e₀e₁)`: `tr Zminus² = −128` (`uC_trace_neg`);
* `Zplus = ρ(e₀e₇)`: `tr Zplus² = +128` (`uC_trace_pos`);
* `Nnil = ρ(e₀(e₁ + e₇)) = Zminus + Zplus`, which is nonzero and isotropic; in fact `Nnil² = 0`
  (`uC_nilpotent`), because `e₁ + e₇` is a null vector.

So the Lie-algebra factor of the fibre pairing is an indefinite quadratic form with isotropic
vectors. Pointwise, for any `α ∈ Λ¹³` (in a local trivialisation), `Tr((α⊗Nnil) ∧ ⋆(α⊗Nnil)) = 0`
whatever the Hodge star does, and `α⊗Zminus`, `α⊗Zplus` give opposite signs for fixed `α`. Hence
`‖·‖` is a misnomer and `I₂ᴮ` is not bounded below, consistent with U(64,64) being non-compact.
This is standard; the file is a Lean witness in the draft's basis. **Not shown:** that some field
`ω = (ε, ϖ)` realises such a `Υ_ω = ⧉F + κ⋆T`. The draft uses (9.11) only for its Euler–Lagrange
equations and does not claim `I₂ᴮ = 0 ⇒ Υ = 0`. The (7,7) Hodge star's own indefiniteness, the fact
`tr Nnil = 0`, and the classification of invariant forms (`a·tr XY + b·tr X tr Y`) are standard and
not formalised.
-/

namespace GU.Spinor

open Matrix CliffordAlgebra

lemma Q77_eb14 (i : Fin 14) : Q77 (eb14 i) = if (i : ℕ) < 7 then 1 else -1 := by
  simp [eb14, Q77, QuadraticMap.weightedSumSquares_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- `(ι a ι b)² = −Q(a)Q(b)` for orthogonal `a, b`. -/
lemma bivector_sq {a b : Fin 14 → ℝ} (h : Q77.IsOrtho a b) :
    (ι Q77 a * ι Q77 b) * (ι Q77 a * ι Q77 b) = algebraMap ℝ Cl77 (-(Q77 a * Q77 b)) := by
  calc (ι Q77 a * ι Q77 b) * (ι Q77 a * ι Q77 b)
      = ι Q77 a * (ι Q77 b * ι Q77 a) * ι Q77 b := by simp only [mul_assoc]
    _ = -(ι Q77 a * ι Q77 a * (ι Q77 b * ι Q77 b)) := by
        rw [ι_mul_ι_comm_of_isOrtho h.symm]; simp only [mul_assoc, mul_neg, neg_mul]
    _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, ← map_neg]

lemma star_bivector {a b : Fin 14 → ℝ} (h : Q77.IsOrtho a b) :
    star (ι Q77 a * ι Q77 b) = -(ι Q77 a * ι Q77 b) := by
  rw [star_mul, star_ι, star_ι, neg_mul_neg, ι_mul_ι_comm_of_isOrtho h.symm]

lemma Ψu_of_star_neg {y : Cl77} (h : star y = -y) : Ψu y = toC (cliffordRep y) := by
  have ha : antiP y = y := by
    unfold antiP; rw [h, sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
  have hs : symP y = 0 := by unfold symP; rw [h, add_neg_cancel, smul_zero]
  rw [Ψu, ha, hs, map_zero]
  ext i j; simp [toC]

/-- `toC ρ(r) = r · 1`, so its trace is `128 r`. -/
lemma trace_toC_algebraMap (r : ℝ) : (toC (cliffordRep (algebraMap ℝ Cl77 r))).trace = 128 * r := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  simp [toC, Matrix.trace, Finset.sum_const, Finset.card_univ]

lemma bivector_mem_sq {a b : Fin 14 → ℝ} (h : Q77.IsOrtho a b) :
    toC (cliffordRep (ι Q77 a * ι Q77 b)) ∈ uC ∧
      (toC (cliffordRep (ι Q77 a * ι Q77 b)) * toC (cliffordRep (ι Q77 a * ι Q77 b))).trace =
        128 * (-(Q77 a * Q77 b)) := by
  refine ⟨?_, ?_⟩
  · rw [← Ψu_of_star_neg (star_bivector h)]; exact Ψu_mem _
  · rw [← toC_mul, ← map_mul, bivector_sq h, trace_toC_algebraMap]; push_cast; ring

/-- `ρ(e₀e₁)`, `ρ(e₀e₇)` and `ρ(e₀(e₁+e₇))` as complex matrices. -/
noncomputable def Zminus : Matrix Idx Idx ℂ := toC (cliffordRep (ι Q77 (eb14 0) * ι Q77 (eb14 1)))
noncomputable def Zplus : Matrix Idx Idx ℂ := toC (cliffordRep (ι Q77 (eb14 0) * ι Q77 (eb14 7)))
noncomputable def Nnil : Matrix Idx Idx ℂ :=
  toC (cliffordRep (ι Q77 (eb14 0) * ι Q77 (eb14 1 + eb14 7)))

/-- **Negative direction**: `Zminus ∈ u(64,64)`, `tr Zminus² = −128`. -/
theorem uC_trace_neg : Zminus ∈ uC ∧ (Zminus * Zminus).trace = -128 := by
  unfold Zminus
  obtain ⟨h1, h2⟩ := bivector_mem_sq (eb14_ortho (i := 0) (j := 1) (by decide))
  refine ⟨h1, ?_⟩
  rw [h2, Q77_eb14, Q77_eb14]; norm_num

/-- **Positive direction**: `Zplus ∈ u(64,64)`, `tr Zplus² = +128`. -/
theorem uC_trace_pos : Zplus ∈ uC ∧ (Zplus * Zplus).trace = 128 := by
  unfold Zplus
  obtain ⟨h1, h2⟩ := bivector_mem_sq (eb14_ortho (i := 0) (j := 7) (by decide))
  refine ⟨h1, ?_⟩
  rw [h2, Q77_eb14, Q77_eb14]; norm_num

lemma null_e1e7 : Q77 (eb14 1 + eb14 7) = 0 := by
  rw [show Q77 (eb14 1 + eb14 7) = Q77 (eb14 1) + Q77 (eb14 7) from
    eb14_ortho (i := 1) (j := 7) (by decide), Q77_eb14, Q77_eb14]; norm_num

lemma ortho_e0_null : Q77.IsOrtho (eb14 0) (eb14 1 + eb14 7) := by
  rw [← QuadraticMap.isOrtho_polarBilin, map_add,
    QuadraticMap.isOrtho_polarBilin.mpr (eb14_ortho (i := 0) (j := 1) (by decide)),
    QuadraticMap.isOrtho_polarBilin.mpr (eb14_ortho (i := 0) (j := 7) (by decide)), add_zero]

/-- **An isotropic (indeed nilpotent) element of `u(64,64)`**: `Nnil ≠ 0`, `Nnil² = 0`. -/
theorem uC_nilpotent : Nnil ∈ uC ∧ Nnil ≠ 0 ∧ Nnil * Nnil = 0 := by
  unfold Nnil
  obtain ⟨h1, -⟩ := bivector_mem_sq ortho_e0_null
  refine ⟨h1, ?_, ?_⟩
  · intro h0
    have h := congrArg (fun M => toC (cliffordRep (ι Q77 (eb14 0))) * M) h0
    simp only [Matrix.mul_zero] at h
    rw [← toC_mul, ← map_mul, ← mul_assoc, ι_sq_scalar, Q77_eb14] at h
    norm_num at h
    have hv : cliffordRep (ι Q77 (eb14 1 + eb14 7)) = 0 := by
      ext i j; have := congrFun (congrFun h i) j
      simp only [toC, Matrix.map_apply, Matrix.zero_apply, Complex.ofRealHom_eq_coe,
        Complex.ofReal_eq_zero] at this
      simpa using this
    have hι : ι Q77 (eb14 1 + eb14 7) = 0 :=
      cliffordRep_bijective.1 (hv.trans (map_zero cliffordRep).symm)
    have hpol : QuadraticMap.polar Q77 (eb14 1 + eb14 7) (eb14 1) = 2 := by
      have := QuadraticMap.polarBilin_apply_apply Q77 (eb14 1 + eb14 7) (eb14 1)
      rw [← this, map_add, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
        (eb14_ortho (i := 7) (j := 1) (by decide)).polar_eq_zero, Q77_eb14]
      norm_num
    have h2 := ι_mul_ι_add_swap (Q := Q77) (eb14 1 + eb14 7) (eb14 1)
    rw [hι, zero_mul, mul_zero, add_zero, hpol] at h2
    have h3 := congrArg (fun x => cliffordRep x 0 0) h2
    simp [Algebra.algebraMap_eq_smul_one] at h3
  · rw [← toC_mul, ← map_mul, bivector_sq ortho_e0_null, null_e1e7, mul_zero, neg_zero, map_zero,
      map_zero]
    ext i j; simp [toC]

end GU.Spinor
