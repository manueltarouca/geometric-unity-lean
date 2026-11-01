/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.SheetLifts
import GU.Bundle.CoverPH
import GU.Bundle.O77Components

/-!
# The deck transformation of the cover and the spin structure

`deck` swaps the two sheets of `Ytilde X` (same metric, opposite future cone). On the pulled-back
frames it acts by `deckT (p, f) = (deck p, f)`.

* **`deckT_not_mem_redT`**: `deckT` maps the `SO₀`-reduction `redT X` into its complement. The key
  facts: a time-reversing Lorentz transformation acts on frames outside `SO₀`
  (`lorO_not_mem_of_neg`, via `lorO_Rpi`: the rotation by `π` in the `(t, x)`-plane acts by the
  holonomy `gHol`), and the future cones of the two sheets are opposite (`not_future_deck`).
* **`no_deck_lift`**: hence **no map of the total space of a `Spin⁺(7,7)` structure on the cover with
  image `redT X` lifts `deckT`** (no equivariance assumed), for any nonempty `X`; instance `coverSpin`
  over `ℝ⁴` (`no_deck_lift_coverSpin`). Only `coverSpin` is formalised; a lift of `deck` to `P_H` or
  the spinor bundle induced from `coverSpin` would need one on `coverSpin`, which does not exist. (A
  bare lift ignoring the frames always exists, since `coverSpin` is a product.)
* **What does lift**: composing with the right action of `gHol` does preserve the reduction
  (`deckT_gHol_mem_redT`), and `gHol` is the image of an element of the non-identity component of the
  two-component group (`gHol_eq_toO`). That component changes the sign of every `Spin⁺`-invariant
  bilinear form on the Dirac module (`flip_nonidentity`, `TwoComponent.lean`).

Reading (informal): the two time orientations are related by no `Spin⁺` map compatible with the
frames; relating them needs the two-component group, and then every invariant spinor pairing changes
sign (via `toO_spec` and `flip_nonidentity`; no lift of `deckT · gHol` to `coverSpin` is constructed
here). This is a corollary of the classical facts that time reversal lies outside `SO₀` and that the
non-identity component negates invariant pairings, stated in the setting of the cover.

**Open, not formalised**: whether the gauge action and the Shiab operator commute with the
two-component comparison `deckT · gHol` (or any spinor-level lift of it). Coverage of the draft's
(9.x): none.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-! ### Time-reversing Lorentz transformations act outside `SO₀` -/

lemma Rpi_eq : Rθ Real.pi = Matrix.diagonal ![-1, -1, 1, 1] := Rθ_pi

lemma isLorentz_Rpi : IsLorentz (Rθ Real.pi) := by
  unfold IsLorentz
  rw [Rpi_eq, GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext i; fin_cases i <;> simp

/-- **The rotation by `π` in the `(t, x)`-plane acts on frames by the holonomy `gHol`.** -/
lemma lorO_Rpi : lorO (Rθ Real.pi) isLorentz_Rpi = gHol := by
  apply Subtype.ext
  show lorM (Rθ Real.pi) = gHolM
  have hL : lorL (Rθ Real.pi) (isUnit_Rθ _) = Matrix.toLin' (Matrix.diagonal dHol) := by
    apply LinearMap.ext; intro v
    have h := congrArg (fun F : HomF => F v) hLoop_pi
    show ΦL.symm (TP (Rθ Real.pi) (isUnit_Rθ _) (ΦL v)) = _
    have e1 : TP (Rθ Real.pi) (isUnit_Rθ _) (ΦL v) = ΦL (matCLM gHolM v) := by
      have := h
      rw [hLoop, hLoop, tpFrame_apply, ContinuousLinearMap.comp_apply, tpFrame_apply, TP_Rθ_zero] at this
      exact this
    rw [e1, ΦL.symm_apply_apply]
    rfl
  have := lorM_of (Rθ Real.pi) (isUnit_Rθ _)
  rw [hL, LinearMap.toMatrix'_toLin'] at this
  rw [gHolM, ← this]; rfl

lemma Rpi_mul_self : Rθ Real.pi * Rθ Real.pi = 1 := by
  rw [Rpi_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; fin_cases i <;> simp

/-- **A Lorentz transformation with `Λ₀₀ < 0` acts on frames outside `SO₀`.** -/
theorem lorO_not_mem_of_neg {Λ : M4} (hL : IsLorentz Λ) (h0 : Λ 0 0 < 0) : lorO Λ hL ∉ SO0 := by
  intro hmem
  have hLR : IsLorentz (Λ * Rθ Real.pi) := by
    unfold IsLorentz at hL ⊢
    have hR := isLorentz_Rpi
    unfold IsLorentz at hR
    rw [transpose_mul]
    calc Λ * Rθ Real.pi * ηR * ((Rθ Real.pi)ᵀ * Λᵀ) = Λ * (Rθ Real.pi * ηR * (Rθ Real.pi)ᵀ) * Λᵀ := by
          simp only [Matrix.mul_assoc]
      _ = ηR := by rw [hR, hL]
  have h00 : 0 < (Λ * Rθ Real.pi) 0 0 := by
    rw [Rpi_eq, Matrix.mul_diagonal]; simp; linarith
  have hpos := lorO_mem_SO0 hLR h00
  have hprod : lorO Λ hL = lorO (Λ * Rθ Real.pi) hLR * gHol := by
    rw [← lorO_Rpi, ← lorO_mul hLR isLorentz_Rpi
      (by rw [Matrix.mul_assoc, Rpi_mul_self, Matrix.mul_one]; exact hL)]
    congr 1
    rw [Matrix.mul_assoc, Rpi_mul_self, Matrix.mul_one]
  have : gHol = (lorO (Λ * Rθ Real.pi) hLR)⁻¹ * lorO Λ hL := by rw [hprod, inv_mul_cancel_left]
  exact gHol_not_mem_SO0 (this ▸ mul_mem (inv_mem hpos) hmem)

/-! ### The deck transformation -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **The deck transformation**: the other sheet over the same metric. -/
def deck (p : Ytilde X) : Ytilde X := ⟨p.proj, !p.2⟩

lemma piT_deck (p : Ytilde X) : piT (deck p) = piT p := rfl

lemma deck_ne (p : Ytilde X) : deck p ≠ p := by
  intro h
  have := congrArg (fun q : Ytilde X => q.2) h
  revert this
  show (!p.2) = p.2 → False
  cases p.2 <;> decide

lemma rep_deck (p : Ytilde X) : rep (deck p) = -rep p := by
  obtain ⟨y, b⟩ := p
  cases b <;> simp [rep, deck, flipIf]

/-- **The future cones of the two sheets are opposite.** -/
lemma lp_neg_of_future_deck {p : Ytilde X} {u v : R4} (hu : u ∈ future p) (hv : v ∈ future (deck p)) :
    lp (Gpt (p.proj : Yobs X)) u v < 0 := by
  obtain ⟨Q, -, hG⟩ := p.proj.2
  have hr := timelike_rep p
  have h1 : 0 < lp (Gpt (p.proj : Yobs X)) u (rep p) := hu.2
  have h2 : lp (Gpt (p.proj : Yobs X)) (rep p) v < 0 := by
    have := hv.2
    rw [show (deck p).proj = p.proj from rfl, rep_deck, lp_neg_right] at this
    rw [lp_comm hG]; linarith
  have hco := lp_sign_cocycle hG hu.1 hr hv.1
  have hf : ¬ lp (Gpt (p.proj : Yobs X)) u (rep p) < 0 := not_lt.mpr h1.le
  rw [decide_eq_false hf, decide_eq_true h2] at hco
  simpa using hco.symm

lemma not_future_deck {p : Ytilde X} {v : R4} (hv : v ∈ future p) : v ∉ future (deck p) := by
  intro h
  have := lp_neg_of_future_deck hv h
  have h2 : 0 < lp (Gpt (p.proj : Yobs X)) v v := hv.1
  linarith

/-- The deck transformation on the pulled-back frames. -/
def deckT (z : OFrT X) : OFrT X := ⟨(deck z.1.1, z.1.2), z.2⟩

/-- **The deck transformation maps the reduction into its complement.** -/
theorem deckT_not_mem_redT {z : OFrT X} (hz : z ∈ redT X) : deckT z ∉ redT X := by
  rintro ⟨P', h', hf', g', hg', hz'⟩
  obtain ⟨P, h, hf, g, hg, hzf⟩ := hz
  have hneg : lp (Gpt (piT z.1.1 : Yobs X)) (tcov P) (tcov P') < 0 :=
    lp_neg_of_future_deck hf hf'
  have hL := isLorentz_frames h h'
  have h00 : (P⁻¹ * P') 0 0 < 0 := by rw [← lp_tcov h h']; exact hneg
  have hact := rawO_act h h'
  -- rawO P · g = rawO P' · g' = rawO P · (lorO · g')
  have e : actOFr' (rawO (piT z.1.1) P h) g =
      actOFr' (rawO (piT z.1.1) P h) (lorO (P⁻¹ * P') hL * g') := by
    rw [hzf, ← actOFr'_mul, hact]; exact hz'.symm
  have hgg := actOFr'_cancel e
  have : lorO (P⁻¹ * P') hL = g * g'⁻¹ := by rw [hgg, mul_inv_cancel_right]
  exact lorO_not_mem_of_neg hL h00 (this ▸ mul_mem hg (inv_mem hg'))

/-- **No lift of the deck transformation** to any `Spin⁺(7,7)` structure on the cover with image the
reduction: no map `L` of its total space satisfies `Φ ∘ L = deckT ∘ Φ`. -/
theorem no_deck_lift (x : X) (S : CoverSpin X) (hS : Set.range S.Φ = redT X) :
    ¬ ∃ L : S.P → S.P, ∀ q, S.Φ (L q) = deckT (S.Φ q) := by
  rintro ⟨L, hL⟩
  obtain ⟨z, hz⟩ := redT_nonempty x
  rw [← hS] at hz
  obtain ⟨q, rfl⟩ := hz
  have h1 : S.Φ (L q) ∈ redT X := hS ▸ ⟨L q, rfl⟩
  rw [hL] at h1
  exact deckT_not_mem_redT (hS ▸ ⟨q, rfl⟩) h1

/-- **Instance**: the deck transformation does not lift to `coverSpin` over `ℝ⁴`. -/
theorem no_deck_lift_coverSpin :
    ¬ ∃ L : coverSpin.P → coverSpin.P, ∀ q, coverSpin.Φ (L q) = deckT (coverSpin.Φ q) :=
  no_deck_lift (0 : R4) coverSpin (by rw [range_coverSpin, QT_eq_redT])

/-! ### What does lift: the deck transformation composed with `gHol` -/

/-- **`deckT` followed by the right action of `gHol` preserves the reduction.** -/
theorem deckT_gHol_mem_redT {z : OFrT X} (hz : z ∈ redT X) : actT (deckT z) gHol ∈ redT X := by
  obtain ⟨P, h, hf, g, hg, hzf⟩ := hz
  have hR : IsLF (Gpt (piT z.1.1 : Yobs X)) (P * Rθ Real.pi) := by
    refine ⟨h.1.mul (isUnit_Rθ _), ?_⟩
    rw [h.2, transpose_mul]
    have hR := isLorentz_Rpi
    unfold IsLorentz at hR
    calc P * ηR * Pᵀ = P * (Rθ Real.pi * ηR * (Rθ Real.pi)ᵀ) * Pᵀ := by rw [hR]
      _ = _ := by simp only [Matrix.mul_assoc]
  have htc : tcov (P * Rθ Real.pi) = -tcov P := by
    have hRT : (Rθ Real.pi)ᵀ = Rθ Real.pi := by rw [Rpi_eq, Matrix.diagonal_transpose]
    have hinv : (Rθ Real.pi)⁻¹ = Rθ Real.pi := Matrix.inv_eq_left_inv Rpi_mul_self
    have hR0 : tcov (Rθ Real.pi) = -(Pi.single 0 1 : R4) := by
      unfold tcov; rw [hRT, hinv, Rpi_eq]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply]
    rw [tcov_mul, hR0, Matrix.mulVec_neg]; rfl
  refine ⟨P * Rθ Real.pi, hR, ?_, gHol⁻¹ * g * gHol, ?_, ?_⟩
  · show tcov (P * Rθ Real.pi) ∈ future (deck z.1.1)
    rw [htc]
    refine ⟨by rw [lp_neg_left, lp_neg_right, neg_neg]; exact hf.1, ?_⟩
    show 0 < lp _ (-tcov P) (rep (deck z.1.1))
    rw [rep_deck, lp_neg_left, lp_neg_right, neg_neg]; exact hf.2
  · refine conj_mem_SO0 gHol⁻¹ ?_
    rw [inv_inv]
    have : gHol * (gHol⁻¹ * g * gHol) * gHol⁻¹ = g := by group
    rw [this]; exact hg
  · show actOFr' (rawO (piT z.1.1) (P * Rθ Real.pi) hR) (gHol⁻¹ * g * gHol) = actOFr' z.1.2 gHol
    have hlor : lorO (P⁻¹ * (P * Rθ Real.pi)) (isLorentz_frames h hR) = gHol := by
      rw [← lorO_Rpi]; congr 1
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h.1),
        Matrix.one_mul]
    rw [← rawO_act h hR, hlor, actOFr'_mul, ← hzf, actOFr'_mul]
    congr 1
    group

/-- **`gHol` comes from the non-identity component** of the two-component group: it is `toO` of an
element `(x, ω)`. -/
theorem gHol_eq_toO : ∃ x : Spin77, toO (x, Multiplicative.ofAdd 1) = gHol := by
  have hdet : (Matrix.of (gHol : Mat 14)).det = 1 := det_gHol
  rcases (SO77_eq gHol).mp hdet with h | h
  · exact absurd h gHol_not_mem_SO0
  · obtain ⟨x, hx'⟩ := spinToSO0_surjective ⟨negO * gHol, h⟩
    have hx : spinToO77 x = negO * gHol := congrArg Subtype.val hx'
    refine ⟨x, ?_⟩
    show spinToO77 x * negPow (Multiplicative.ofAdd 1) = gHol
    rw [negPow_gen, hx, mul_assoc, ← negO_comm, ← mul_assoc, negO_sq, one_mul]

end

end GU.Library
