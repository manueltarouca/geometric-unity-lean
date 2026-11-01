/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.FrameAction

/-!
# The (1,3) part of `Y` is open

For `W : ℝ³ → ℝ⁴` (a `4 × 3` matrix), `NegOn G W` says `G` is negative definite on the image of
`W`, tested on the unit sphere. It is an open condition in `G` (`isOpen_negOn`, compactness of the
sphere). A (1,3) matrix `P η Pᵀ` is negative definite on `P⁻ᵀ span(e₁,e₂,e₃)`; a (3,1) matrix is
positive definite on a 3-plane, and two 3-planes in `ℝ⁴` meet nontrivially, so a Lorentzian matrix
negative definite on a 3-plane is (1,3) (`sig13_of_negOn`). Hence the (1,3) fibre locus is open.
-/

namespace GU.Observerse

open Matrix GU.Chimeric

/-- `G` is negative definite on the image of `W`. -/
def NegOn (G : Matrix (Fin 4) (Fin 4) ℝ) (W : Matrix (Fin 4) (Fin 3) ℝ) : Prop :=
  ∀ x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1, (W *ᵥ x) ⬝ᵥ (G *ᵥ (W *ᵥ x)) < 0

lemma continuous_quad (W : Matrix (Fin 4) (Fin 3) ℝ) :
    Continuous (fun p : (Fin 10 → ℝ) × (Fin 3 → ℝ) =>
      (W *ᵥ p.2) ⬝ᵥ (symMat p.1 *ᵥ (W *ᵥ p.2))) := by
  simp only [dotProduct, mulVec, symMat, Matrix.of_apply]
  fun_prop

/-- **Negative definiteness on a fixed 3-plane is an open condition.** -/
lemma isOpen_negOn (W : Matrix (Fin 4) (Fin 3) ℝ) :
    IsOpen {s : Fin 10 → ℝ | NegOn (symMat s) W} := by
  rw [isOpen_iff_mem_nhds]
  intro s0 hs0
  have hK : IsCompact (Metric.sphere (0 : Fin 3 → ℝ) 1) := isCompact_sphere 0 1
  have := hK.eventually_forall_of_forall_eventually (x₀ := s0)
    (P := fun s x => (W *ᵥ x) ⬝ᵥ (symMat s *ᵥ (W *ᵥ x)) < 0) fun x hx =>
      (continuous_quad W).continuousAt.eventually (gt_mem_nhds (hs0 x hx))
  exact this

/-- The last three basis vectors `e₁, e₂, e₃` as a `4 × 3` matrix. -/
def Elast : Matrix (Fin 4) (Fin 3) ℝ := Matrix.of fun i k => if i = k.succ then 1 else 0

lemma Elast_quad (x : Fin 3 → ℝ) (σ : ℝ) :
    (Elast *ᵥ x) ⬝ᵥ ((σ • ηR) *ᵥ (Elast *ᵥ x)) = -σ * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  simp [Elast, ηR, ηZ, dotProduct, mulVec, Fin.sum_univ_succ, Matrix.diagonal_apply]
  ring

lemma sphere_sq_pos {x : Fin 3 → ℝ} (hx : x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1) :
    0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  have hne : x ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx; exact zero_ne_one hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have : 0 < x i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  fin_cases i <;> simp at this ⊢ <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- A congruence transport of the quadratic form. -/
lemma quad_congr (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → ℝ) :
    ((Pᵀ)⁻¹ *ᵥ v) ⬝ᵥ ((P * M * Pᵀ) *ᵥ ((Pᵀ)⁻¹ *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) := by
  have hPt : IsUnit (Pᵀ).det := by rw [det_transpose]; exact (isUnit_iff_isUnit_det P).mp hP
  have hPw : Pᵀ *ᵥ ((Pᵀ)⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hPt, one_mulVec]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hPw]

/-- **(1,3) ⇒ negative definite on a 3-plane.** -/
lemma negOn_of_sig13 (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) :
    NegOn (P * ηR * Pᵀ) ((Pᵀ)⁻¹ * Elast) := by
  intro x hx
  rw [← mulVec_mulVec, quad_congr P hP, show ηR = (1 : ℝ) • ηR by rw [one_smul], Elast_quad]
  have := sphere_sq_pos hx
  linarith

lemma quad_smul (G : Matrix (Fin 4) (Fin 4) ℝ) (W : Matrix (Fin 4) (Fin 3) ℝ) (c : ℝ)
    (u : Fin 3 → ℝ) :
    (W *ᵥ (c • u)) ⬝ᵥ (G *ᵥ (W *ᵥ (c • u))) = c ^ 2 * ((W *ᵥ u) ⬝ᵥ (G *ᵥ (W *ᵥ u))) := by
  rw [mulVec_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

lemma negOn_ne {G : Matrix (Fin 4) (Fin 4) ℝ} {W : Matrix (Fin 4) (Fin 3) ℝ} (h : NegOn G W)
    {a : Fin 3 → ℝ} (ha : a ≠ 0) : (W *ᵥ a) ⬝ᵥ (G *ᵥ (W *ᵥ a)) < 0 := by
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have := h _ hu
  have ha' : a = ‖a‖ • (‖a‖⁻¹ • a) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [ha', quad_smul]
  exact mul_neg_of_pos_of_neg (by positivity) this

/-- Two 3-planes in `ℝ⁴` meet nontrivially. -/
lemma planes_meet (W V : Matrix (Fin 4) (Fin 3) ℝ) (hW : Function.Injective (Matrix.toLin' W))
    (hV : Function.Injective (Matrix.toLin' V)) :
    ∃ a b : Fin 3 → ℝ, a ≠ 0 ∧ b ≠ 0 ∧ W *ᵥ a = V *ᵥ b := by
  set A := LinearMap.range (Matrix.toLin' W)
  set B := LinearMap.range (Matrix.toLin' V)
  have hA : Module.finrank ℝ A = 3 := by
    rw [LinearMap.finrank_range_of_inj hW]; simp
  have hB : Module.finrank ℝ B = 3 := by
    rw [LinearMap.finrank_range_of_inj hV]; simp
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle : Module.finrank ℝ (A ⊔ B : Submodule ℝ (Fin 4 → ℝ)) ≤ 4 := by
    have := Submodule.finrank_le (A ⊔ B); simpa using this
  have hpos : 0 < Module.finrank ℝ (A ⊓ B : Submodule ℝ (Fin 4 → ℝ)) := by omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hpos)
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hv
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rintro rfl; apply hv0; rw [← ha]; simp
  · rintro rfl; apply hv0; rw [← hb]; simp
  · rw [Matrix.toLin'_apply] at ha hb; rw [ha, hb]

/-- **Negative definite on a 3-plane and Lorentzian ⇒ (1,3).** -/
lemma sig13_of_negOn {G : Matrix (Fin 4) (Fin 4) ℝ} (hs : G.IsSymm) (hd : G.det < 0)
    {W : Matrix (Fin 4) (Fin 3) ℝ} (hW : NegOn G W) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ G = P * ηR * Pᵀ := by
  obtain ⟨P, hP, h | h⟩ := lorentz_dichotomy G hs hd
  · exact ⟨P, hP, h⟩
  exfalso
  set V := (Pᵀ)⁻¹ * Elast
  have hPt : IsUnit (Pᵀ).det := by rw [det_transpose]; exact (isUnit_iff_isUnit_det P).mp hP
  have hposV : ∀ b : Fin 3 → ℝ, b ≠ 0 → 0 < (V *ᵥ b) ⬝ᵥ (G *ᵥ (V *ᵥ b)) := by
    intro b hb
    rw [← mulVec_mulVec, h, show -ηR = (-1 : ℝ) • ηR by rw [neg_one_smul], quad_congr P hP,
      Elast_quad]
    have hb' : 0 < b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      have : 0 < b i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
      fin_cases i <;> simp at this ⊢ <;> nlinarith [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2)]
    linarith
  have hWinj : Function.Injective (Matrix.toLin' W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have := negOn_ne hW hne
    rw [Matrix.toLin'_apply] at ha
    rw [ha] at this; simp at this
  have hVinj : Function.Injective (Matrix.toLin' V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hne
    have := hposV b hne
    rw [Matrix.toLin'_apply] at hb
    rw [hb] at this; simp at this
  obtain ⟨a, b, ha, hb, hab⟩ := planes_meet W V hWinj hVinj
  have h1 := negOn_ne hW ha
  have h2 := hposV b hb
  rw [hab] at h1
  linarith

/-- The (1,3) locus of the fibre `ℝ¹⁰`. -/
def S13 : Set (Fin 10 → ℝ) :=
  {s | (symMat s).det < 0 ∧ ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ symMat s = P * ηR * Pᵀ}

/-- **The (1,3) locus is open.** -/
theorem isOpen_S13 : IsOpen S13 := by
  rw [isOpen_iff_mem_nhds]
  rintro s0 ⟨hd0, P, hP, hs0⟩
  have hdet : IsOpen {s : Fin 10 → ℝ | (symMat s).det < 0} := isOpen_LorFiber
  have hneg : s0 ∈ {s : Fin 10 → ℝ | NegOn (symMat s) ((Pᵀ)⁻¹ * Elast)} := by
    show NegOn (symMat s0) _; rw [hs0]; exact negOn_of_sig13 P hP
  refine Filter.mem_of_superset ((hdet.inter (isOpen_negOn _)).mem_nhds ⟨hd0, hneg⟩) ?_
  rintro s ⟨hd, hn⟩
  exact ⟨hd, sig13_of_negOn (symMat_isSymm s) hd hn⟩

section OnY

open Bundle
open scoped ContDiff

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

lemma sig13_congr {G : Matrix (Fin 4) (Fin 4) ℝ} (Q : Matrix (Fin 4) (Fin 4) ℝ) (hQ : IsUnit Q) :
    (∃ P, IsUnit P ∧ G = P * ηR * Pᵀ) → ∃ P, IsUnit P ∧ Q * G * Qᵀ = P * ηR * Pᵀ := by
  rintro ⟨P, hP, rfl⟩
  exact ⟨Q * P, hQ.mul hP, by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]⟩

/-- **The (1,3) part of `Y` is open.** -/
theorem isOpen_Y13 : IsOpen {y : Yobs X | ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧
    Gpt y = P * ηR * Pᵀ} := by
  rw [isOpen_iff_forall_mem_open]
  intro y0 hy0
  set i := achart (Fin 4 → ℝ) (πY y0)
  set U : Set (Yobs X) := {y | πY y ∈ (Zt X).baseSet i}
  have hU : IsOpen U := ((Zt X).isOpen_baseSet i).preimage contMDiff_πY.continuous
  set fch : Yobs X → (Fin 10 → ℝ) := fun y => ((symCore (Zt X)).localTriv i (y : Sym2TX X)).2
  have hcont : ContinuousOn fch U := by
    have ht := ((symCore (Zt X)).localTriv i).continuousOn
    refine continuous_snd.comp_continuousOn (ht.comp continuous_subtype_val.continuousOn ?_)
    intro y hy
    rw [VectorBundleCore.mem_localTriv_source]
    exact hy
  have hiff : ∀ y ∈ U, ((∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * ηR * Pᵀ) ↔
      fch y ∈ S13) := by
    intro y hy
    have hx : πY y ∈ (Zt X).baseSet ((Zt X).indexAt (πY y)) ∩ (Zt X).baseSet i :=
      ⟨(Zt X).mem_baseSet_at _, hy⟩
    have hPm := Pm_isUnit _ _ _ hx
    have hGi : symMat (fch y) = Gi i y := rfl
    have hdet : (symMat (fch y)).det < 0 := hGi ▸ Gi_det_neg i y hy
    rw [Gi_eq] at hGi
    constructor
    · intro h
      exact ⟨hdet, hGi ▸ sig13_congr _ hPm h⟩
    · rintro ⟨-, h⟩
      rw [hGi] at h
      obtain ⟨Q, hQ, hQe⟩ := h
      set Pm := Pm ((Zt X).indexAt (πY y)) i (πY y)
      have hu : IsUnit Pm⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hPm
      refine ⟨Pm⁻¹ * Q, hu.mul hQ, ?_⟩
      have hdu := (isUnit_iff_isUnit_det Pm).mp hPm
      calc Gpt y = Pm⁻¹ * (Pm * Gpt y * Pmᵀ) * (Pmᵀ)⁻¹ := by
            rw [show Pm⁻¹ * (Pm * Gpt y * Pmᵀ) * (Pmᵀ)⁻¹ =
              (Pm⁻¹ * Pm) * Gpt y * (Pmᵀ * (Pmᵀ)⁻¹) by simp only [Matrix.mul_assoc]]
            rw [nonsing_inv_mul _ hdu, mul_nonsing_inv _ (by rw [det_transpose]; exact hdu),
              Matrix.one_mul, Matrix.mul_one]
        _ = (Pm⁻¹ * Q) * ηR * (Pm⁻¹ * Q)ᵀ := by
            rw [hQe, Matrix.transpose_mul, ← transpose_nonsing_inv]; simp only [Matrix.mul_assoc]
  refine ⟨U ∩ fch ⁻¹' S13, ?_, hcont.isOpen_inter_preimage hU isOpen_S13, ?_⟩
  · rintro y ⟨hyU, hyS⟩; exact (hiff y hyU).mpr hyS
  · have hy0U : y0 ∈ U := (Zt X).mem_baseSet_at (πY y0)
    exact ⟨hy0U, (hiff y0 hy0U).mp hy0⟩

end OnY

end GU.Observerse
