import GU.Shiab.Einstein
import GU.Spinor.Faithful

/-!
# GR emergence: the Shiab equation with a cosmological source forces `G = Λ g` ((9.9)–(9.10))

The draft reads `Υ_ω = ⧉F − T = 0` as Einstein's equation with the displaced torsion as source,
`G_μν = Λ g_μν` when the source is metric-proportional (9.10). Using the Clifford core
(`shiab_einstein_77`): if the Shiab contraction of an algebraic curvature tensor `R` on `ℝ^{7,7}`
equals a cosmological source `4Λ Σ_y w_y g_by γ_y` (with `g_by = w_b δ_by`), then
`G_by = Λ g_by` for all `b, y` (`einstein_equation`).

The key input is linear independence of the 14 gamma matrices (`gamma_linIndep`, from the trace
form `tr(γ_iγ_j) = 128 w_i δ_ij`).
-/

namespace GU.Spinor

open Matrix GU.CliffordBianchi

lemma trace_gamma_gamma (i j : Fin 14) :
    trace (gamma (gen i) * gamma (gen j)) = if i = j then 128 * w i else 0 := by
  by_cases h : i = j
  · subst h
    have := anticomm i i
    simp only [ite_true] at this
    rw [← two_smul ℝ, show ((2 : ℝ) * w i) • (1 : M128) = (2 : ℝ) • (w i • 1) by rw [smul_smul]] at this
    have h2 : gamma (gen i) * gamma (gen i) = w i • (1 : M128) :=
      smul_right_injective M128 (two_ne_zero (α := ℝ)) this
    rw [h2, trace_smul, trace_one]; simp; ring
  · have hc : gamma (gen i) * gamma (gen j) = -(gamma (gen j) * gamma (gen i)) := by
      have := anticomm i j; simp only [h, ite_false, zero_smul] at this
      exact eq_neg_of_add_eq_zero_left this
    have ht : trace (gamma (gen i) * gamma (gen j)) = trace (gamma (gen j) * gamma (gen i)) :=
      trace_mul_comm _ _
    simp only [h, ite_false]
    rw [hc, trace_neg] at ht ⊢
    linarith

theorem gamma_linIndep : LinearIndependent ℝ (fun i : Fin 14 => gamma (gen i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun M => trace (M * gamma (gen j))) hc
  simp only [Finset.sum_mul, trace_sum, smul_mul_assoc, trace_smul, trace_gamma_gamma, smul_eq_mul,
    zero_mul, trace_zero] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)] at h
  simp only [ite_true] at h
  have hw : w j ≠ 0 := by unfold w; split_ifs <;> norm_num
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h (mul_ne_zero (by norm_num) hw)

/-- **Einstein's equation with cosmological constant from the Shiab equation.** -/
theorem einstein_equation {R : Fin 14 → Fin 14 → Fin 14 → Fin 14 → ℝ} (Λ : ℝ)
    (hS : ∀ b, (4 : ℝ) • ∑ y, (w y * einstein w R b y) • gamma (gen y) =
      (4 : ℝ) • ∑ y, (w y * (Λ * if b = y then w b else 0)) • gamma (gen y)) :
    ∀ b y, einstein w R b y = Λ * (if b = y then w b else 0) := by
  intro b y
  have h := hS b
  have h4 := smul_right_injective M128 (by norm_num : (4 : ℝ) ≠ 0) h
  have := (Fintype.linearIndependent_iff.mp gamma_linIndep)
    (fun y => w y * einstein w R b y - w y * (Λ * if b = y then w b else 0))
    (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.mpr h4) y
  have hw : w y * w y = 1 := w77_sq y
  have : w y * (einstein w R b y - Λ * if b = y then w b else 0) = 0 := by linarith
  have hy : w y ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  linarith [(mul_eq_zero.mp this).resolve_left hy]

/-- **End to end**: the Shiab equation `⧉(R) = cosmological source` (Clifford core of (9.9), with
the source `4Λ Σ_y w_y g_by γ_y`) implies Einstein's equation `G_by = Λ g_by`. -/
theorem shiab_equation_gives_einstein {R : Fin 14 → Fin 14 → Fin 14 → Fin 14 → ℝ} (hR : AlgCurv R)
    (Λ : ℝ)
    (hS : ∀ b, (∑ a, ∑ x, ∑ y, (w a * w x * w y * R a b x y) •
        (gamma (gen a) * (gamma (gen x) * gamma (gen y)) - gamma (gen x) * gamma (gen y) * gamma (gen a)))
      + (1 / 2 : ℝ) • ((∑ a, ∑ c, ∑ x, ∑ y, (w a * w c * w x * w y * R a c x y) •
          (gamma (gen a) * gamma (gen c) * (gamma (gen x) * gamma (gen y))
            + gamma (gen x) * gamma (gen y) * (gamma (gen a) * gamma (gen c)))) * gamma (gen b))
      = (4 : ℝ) • ∑ y, (w y * (Λ * if b = y then w b else 0)) • gamma (gen y)) :
    ∀ b y, einstein w R b y = Λ * (if b = y then w b else 0) :=
  einstein_equation Λ (fun b => (shiab_einstein_77 hR b).symm.trans (hS b))

end GU.Spinor
