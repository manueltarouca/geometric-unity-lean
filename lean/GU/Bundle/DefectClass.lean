/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.ParallelCover

/-!
# The defect class of the spin lifts (ℤ/2 Čech cohomology on a fixed cover)

For a frame system `Fs` (`SpinGeneric.lean`) and local sections `σ i` over an open cover `V i`,
**`LiftData`** is a choice of continuous lifts `h i j` to `Spin(7,7)` of the transition functions,
with no cocycle condition. Its defect `h i j · h j k · (h i k)⁻¹ ∈ {±1}` gives a `ℤ/2`-valued
function `defZ` on triple overlaps. On the fixed cover:

* `cont_defZ`, `defZ_cocycle`: `defZ` is a continuous (locally constant) Čech 2-cocycle;
* `defZ_indep`: for two choices of lifts, the defects differ by the coboundary `δ b` of a continuous
  1-cochain `b`; so the **class** of `defZ` does not depend on the lifts;
* `isCobdy_defZ_iff`: the class vanishes iff the lifts can be changed (by signs) into **continuous
  cocycle lifts**, i.e. into `SpinLiftData`.

On the sheet cover of `Ytilde X` (`sheetY`, frames `secI`): `sheet_isCobdy_iff` turns this into the
hypothesis of `exists_coverSpin_of_lifts`, so a vanishing class gives a `Spin⁺(7,7)` structure on the
whole cover with image `redT X` (`exists_coverSpin_of_isCobdy`).

The cochains are the full (not alternating, not normalised) Čech cochains of the fixed cover, with
`ℤ/2` coefficients; continuity into the discrete `ℤ/2` means locally constant.

Scope. All statements are relative to one cover and fixed local sections, with lifts given on whole
double overlaps; independence is with respect to the lifts only. Existence of such lifts on the sheet
cover is a hypothesis: **no such lifts are constructed here, not even over `ℝ⁴`**
(`exists_coverSpin_R4'` uses the one-set cover of a global frame instead; for parallelisable `X`,
lifts on a refinement of the sheet cover are constructed in `SheetLifts.lean`). Not formalised: lifts on
the sheet cover or a good refinement of it, independence of refinement and of the local sections, and
a non-coboundary example. Informally, the class is `w₂` of the reduction.

Instances: `trivLD` (the constant lifts `−1` over the global frame of the cover of `ℝ⁴`), whose
defect is the nonzero cocycle `1` and is a coboundary (`defZ_trivLD`, `isCobdy_trivLD`).
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

namespace Gen

/-! ### Signs -/

lemma negOne_mul_negOne : negOne * negOne = 1 := IsSign.mul_self (Or.inr rfl)

/-- `ℤ/2 → {±1} ⊆ Spin(7,7)`. -/
def sgn (a : ZMod 2) : Spin77 := if a = 0 then 1 else negOne

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_one : sgn 1 = negOne := by simp [sgn]

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b
  · show sgn 0 = sgn 0 * sgn 0; rw [sgn_zero, one_mul]
  · show sgn 1 = 1 * sgn 1; rw [one_mul]
  · show sgn 1 = sgn 1 * 1; rw [mul_one]
  · show sgn 0 = sgn 1 * sgn 1; rw [sgn_one, negOne_mul_negOne]; rfl

lemma sgn_comm (a : ZMod 2) (x : Spin77) : sgn a * x = x * sgn a := by
  unfold sgn; split_ifs
  · simp
  · exact negOne_comm x

lemma sgn_inv (a : ZMod 2) : (sgn a)⁻¹ = sgn a := by
  rw [inv_eq_iff_mul_eq_one, ← sgn_add]
  fin_cases a <;> rfl

lemma sgn_injective : Function.Injective sgn := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd ((sgn_one).symm.trans h.symm) negOne_ne_one
  · exact absurd ((sgn_one).symm.trans h) negOne_ne_one
  · rfl

lemma zmod2_neg (x : ZMod 2) : -x = x := by fin_cases x <;> rfl

lemma zmod2_two (x : ZMod 2) : x + x = 0 := by fin_cases x <;> rfl

/-- Central signs pull out of a defect. -/
lemma central3 (a b d : Spin77) (x y z : ZMod 2) :
    (a * sgn x) * (b * sgn y) * (d * sgn z)⁻¹ = a * b * d⁻¹ * sgn (x + y + z) := by
  rw [sgn_add, sgn_add, mul_inv_rev, sgn_inv]
  calc a * sgn x * (b * sgn y) * (sgn z * d⁻¹)
      = a * (sgn x * b) * sgn y * sgn z * d⁻¹ := by simp only [mul_assoc]
    _ = a * b * (sgn x * sgn y * sgn z) * d⁻¹ := by rw [sgn_comm x b]; simp only [mul_assoc]
    _ = a * b * (sgn (x + y + z) * d⁻¹) := by rw [sgn_add, sgn_add]; simp only [mul_assoc]
    _ = _ := by rw [sgn_comm, sgn_add, sgn_add]; simp only [mul_assoc]

lemma spinToO77_sgn (a : ZMod 2) : spinToO77 (sgn a) = 1 := by
  unfold sgn; split_ifs
  · exact map_one _
  · exact spinToO77_negOne

lemma continuous_sgn : Continuous sgn := continuous_of_discreteTopology

open Classical in
/-- The sign of an element of `{±1}`. -/
def sgnInv (x : Spin77) : ZMod 2 := if x = 1 then 0 else 1

lemma sgn_sgnInv {x : Spin77} (hx : x = 1 ∨ x = negOne) : sgn (sgnInv x) = x := by
  rcases hx with rfl | rfl
  · simp [sgnInv]; rfl
  · simp [sgnInv, negOne_ne_one, sgn_one]

/-- `sgnInv` is continuous on `{±1}` (a discrete subset). -/
lemma continuousOn_sgnInv : ContinuousOn sgnInv {x | x = 1 ∨ x = negOne} := by
  intro x hx
  have hloc : ∀ᶠ z in 𝓝[{x | x = 1 ∨ x = negOne}] x, sgnInv z = sgnInv x := by
    rcases hx with rfl | rfl
    · have ho : IsOpen ({negOne}ᶜ : Set Spin77) := isOpen_compl_singleton
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (ho.mem_nhds (Ne.symm negOne_ne_one))] with z hz hz'
      rcases hz with rfl | rfl
      · rfl
      · exact absurd rfl hz'
    · have ho : IsOpen ({1}ᶜ : Set Spin77) := isOpen_compl_singleton
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (ho.mem_nhds negOne_ne_one)] with z hz hz'
      rcases hz with rfl | rfl
      · exact absurd rfl hz'
      · rfl
  exact (continuousWithinAt_const.congr_of_eventuallyEq hloc rfl)

/-- A `{±1}`-valued function continuous on `S` has a continuous sign. -/
lemma continuousOn_sgnInv_comp {Z : Type*} [TopologicalSpace Z] {S : Set Z} {f : Z → Spin77}
    (hf : ContinuousOn f S) (hv : ∀ z ∈ S, f z = 1 ∨ f z = negOne) :
    ContinuousOn (fun z => sgnInv (f z)) S :=
  continuousOn_sgnInv.comp hf hv

variable {Fs : FrameSys}

/-! ### Lifts without the cocycle condition -/

/-- **Lift data**: local sections over an open cover with continuous `Spin(7,7)` lifts of their
transition functions, with no cocycle condition. -/
structure LiftData (Fs : FrameSys) where
  ι : Type
  V : ι → Set (Fs.B)
  isOpen_V : ∀ i, IsOpen (V i)
  cover : ∀ y, ∃ i, y ∈ V i
  σ : ι → Fs.B → Fs.Fr
  cont_σ : ∀ i, ContinuousOn (σ i) (V i)
  proj_σ : ∀ i, ∀ y ∈ V i, Fs.proj (σ i y) = y
  h : ι → ι → Fs.B → Spin77
  cont_h : ∀ i j, ContinuousOn (h i j) (V i ∩ V j)
  lift : ∀ i j, ∀ y ∈ V i ∩ V j, σ j y = Fs.act (σ i y) (spinToO77 (h i j y))

namespace LiftData

variable (L : LiftData Fs)

/-- Triple overlaps. -/
def V3 (i j k : L.ι) : Set (Fs.B) := L.V i ∩ L.V j ∩ L.V k

/-- **The defect as a `ℤ/2`-valued Čech 2-cochain.** -/
def defZ (i j k : L.ι) (y : Fs.B) : ZMod 2 := sgnInv (L.h i j y * L.h j k y * (L.h i k y)⁻¹)

lemma defect_mem {i j k : L.ι} {y : Fs.B} (hy : y ∈ L.V3 i j k) :
    L.h i j y * L.h j k y * (L.h i k y)⁻¹ = 1 ∨ L.h i j y * L.h j k y * (L.h i k y)⁻¹ = negOne :=
  spinLift_defect_mem L.lift hy

lemma sgn_defZ {i j k : L.ι} {y : Fs.B} (hy : y ∈ L.V3 i j k) :
    sgn (L.defZ i j k y) = L.h i j y * L.h j k y * (L.h i k y)⁻¹ :=
  sgn_sgnInv (L.defect_mem hy)

/-- `h i j · h j k = sgn (defZ i j k) · h i k`. -/
lemma hh_eq {i j k : L.ι} {y : Fs.B} (hy : y ∈ L.V3 i j k) :
    L.h i j y * L.h j k y = sgn (L.defZ i j k y) * L.h i k y := by
  rw [L.sgn_defZ hy, inv_mul_cancel_right]

/-- **The defect is continuous (locally constant) on triple overlaps.** -/
theorem cont_defZ (i j k : L.ι) : ContinuousOn (L.defZ i j k) (L.V3 i j k) := by
  have h1 := (L.cont_h i j).mono fun y (hy : y ∈ L.V3 i j k) => hy.1
  have h2 := (L.cont_h j k).mono fun y (hy : y ∈ L.V3 i j k) => ⟨hy.1.2, hy.2⟩
  have h3 := (L.cont_h i k).mono fun y (hy : y ∈ L.V3 i j k) => ⟨hy.1.1, hy.2⟩
  exact continuousOn_sgnInv_comp ((h1.mul h2).mul h3.inv) fun y hy => L.defect_mem hy

end LiftData

/-! ### Čech cochains with `ℤ/2` coefficients on a fixed cover -/

/-- The Čech differential of a 1-cochain. -/
def δ1 {ι B : Type} (b : ι → ι → B → ZMod 2) (i j k : ι) (y : B) : ZMod 2 :=
  b j k y - b i k y + b i j y

variable {B : Type} [TopologicalSpace B] {ι : Type} {V : ι → Set B}

/-- Continuous 1-cochains on the cover `V`. -/
def Cont1 (V : ι → Set B) (b : ι → ι → B → ZMod 2) : Prop :=
  ∀ i j, ContinuousOn (b i j) (V i ∩ V j)

/-- Čech 2-cocycles on `V`: `δ c = 0` on quadruple overlaps. -/
def IsCocycle2 (V : ι → Set B) (c : ι → ι → ι → B → ZMod 2) : Prop :=
  ∀ i j k l, ∀ y ∈ V i ∩ V j ∩ V k ∩ V l, c j k l y - c i k l y + c i j l y - c i j k y = 0

/-- Cohomologous 2-cochains: they differ by `δ b`, `b` continuous, on triple overlaps. -/
def Cohom (V : ι → Set B) (c c' : ι → ι → ι → B → ZMod 2) : Prop :=
  ∃ b, Cont1 V b ∧ ∀ i j k, ∀ y ∈ V i ∩ V j ∩ V k, c' i j k y = c i j k y + δ1 b i j k y

/-- Coboundaries: cohomologous to `0`. -/
def IsCobdy (V : ι → Set B) (c : ι → ι → ι → B → ZMod 2) : Prop := Cohom V 0 c

lemma Cohom.refl (c : ι → ι → ι → B → ZMod 2) : Cohom V c c :=
  ⟨fun _ _ _ => 0, fun _ _ => continuousOn_const, fun i j k y _ => by simp [δ1]⟩

lemma Cohom.symm {c c' : ι → ι → ι → B → ZMod 2} (h : Cohom V c c') : Cohom V c' c := by
  obtain ⟨b, hb, he⟩ := h
  refine ⟨fun i j y => -b i j y, fun i j => (hb i j).neg, fun i j k y hy => ?_⟩
  rw [he i j k y hy]; simp only [δ1]; ring

lemma Cohom.trans {c c' c'' : ι → ι → ι → B → ZMod 2} (h : Cohom V c c') (h' : Cohom V c' c'') :
    Cohom V c c'' := by
  obtain ⟨b, hb, he⟩ := h
  obtain ⟨b', hb', he'⟩ := h'
  refine ⟨fun i j y => b i j y + b' i j y, fun i j => (hb i j).add (hb' i j), fun i j k y hy => ?_⟩
  rw [he' i j k y hy, he i j k y hy]; simp only [δ1]; ring

namespace LiftData

variable (L : LiftData Fs)

/-- **The defect is a Čech 2-cocycle.** -/
theorem defZ_cocycle : IsCocycle2 L.V L.defZ := by
  intro i j k l y hy
  have h4 : y ∈ L.V i ∧ y ∈ L.V j ∧ y ∈ L.V k ∧ y ∈ L.V l :=
    ⟨hy.1.1.1, hy.1.1.2, hy.1.2, hy.2⟩
  obtain ⟨hi, hj, hk, hl⟩ := h4
  have eijk := L.hh_eq (i := i) (j := j) (k := k) ⟨⟨hi, hj⟩, hk⟩
  have eikl := L.hh_eq (i := i) (j := k) (k := l) ⟨⟨hi, hk⟩, hl⟩
  have ejkl := L.hh_eq (i := j) (j := k) (k := l) ⟨⟨hj, hk⟩, hl⟩
  have eijl := L.hh_eq (i := i) (j := j) (k := l) ⟨⟨hi, hj⟩, hl⟩
  -- `h_ij h_jk h_kl` two ways
  have e1 : L.h i j y * L.h j k y * L.h k l y =
      sgn (L.defZ i j k y + L.defZ i k l y) * L.h i l y := by
    rw [eijk, mul_assoc, eikl, sgn_add, ← mul_assoc]
  have e2 : L.h i j y * L.h j k y * L.h k l y =
      sgn (L.defZ j k l y + L.defZ i j l y) * L.h i l y := by
    rw [mul_assoc, ejkl, ← mul_assoc, ← sgn_comm, mul_assoc, eijl, sgn_add, mul_assoc]
  have he := sgn_injective (mul_right_cancel (e1.symm.trans e2))
  linear_combination he.symm

/-- The same sections with other lifts `h'` of the same transition functions. -/
def withH (h' : L.ι → L.ι → Fs.B → Spin77) (hc : ∀ i j, ContinuousOn (h' i j) (L.V i ∩ L.V j))
    (hl : ∀ i j, ∀ y ∈ L.V i ∩ L.V j, spinToO77 (h' i j y) = spinToO77 (L.h i j y)) : LiftData Fs :=
  ⟨L.ι, L.V, L.isOpen_V, L.cover, L.σ, L.cont_σ, L.proj_σ, h', hc,
    fun i j y hy => by rw [hl i j y hy]; exact L.lift i j y hy⟩

/-- **The class of the defect does not depend on the lifts**: for other lifts `h'` of the same
transition functions, the defects are cohomologous. -/
theorem defZ_indep (h' : L.ι → L.ι → Fs.B → Spin77) (hc : ∀ i j, ContinuousOn (h' i j) (L.V i ∩ L.V j))
    (hl : ∀ i j, ∀ y ∈ L.V i ∩ L.V j, spinToO77 (h' i j y) = spinToO77 (L.h i j y)) :
    Cohom L.V L.defZ (L.withH h' hc hl).defZ := by
  set L' := L.withH h' hc hl
  have hV' : L'.V = L.V := rfl
  -- the ratio of the lifts is a continuous sign
  have hrat : ∀ i j, ∀ y ∈ L.V i ∩ L.V j, (L.h i j y)⁻¹ * L'.h i j y = 1 ∨
      (L.h i j y)⁻¹ * L'.h i j y = negOne := by
    intro i j y hy
    rw [← spinToO77_eq_one_iff, map_mul, map_inv, inv_mul_eq_one]
    exact (hl i j y hy).symm
  set b : L.ι → L.ι → Fs.B → ZMod 2 := fun i j y => sgnInv ((L.h i j y)⁻¹ * L'.h i j y)
  have hb : Cont1 L.V b := fun i j =>
    continuousOn_sgnInv_comp ((L.cont_h i j).inv.mul (by rw [← hV']; exact L'.cont_h i j)) (hrat i j)
  have hh' : ∀ i j, ∀ y ∈ L.V i ∩ L.V j, L'.h i j y = L.h i j y * sgn (b i j y) := by
    intro i j y hy
    rw [sgn_sgnInv (hrat i j y hy), mul_inv_cancel_left]
  refine ⟨b, hb, fun i j k y hy => ?_⟩
  have hy' : y ∈ L'.V3 i j k := by show y ∈ L'.V i ∩ L'.V j ∩ L'.V k; rw [hV']; exact hy
  apply sgn_injective
  rw [L'.sgn_defZ hy', hh' i j y hy.1, hh' j k y ⟨hy.1.2, hy.2⟩, hh' i k y ⟨hy.1.1, hy.2⟩, central3,
    ← L.sgn_defZ hy, ← sgn_add]
  congr 1
  simp only [δ1, sub_eq_add_neg, zmod2_neg]
  ring

/-- **The class vanishes iff the lifts can be corrected into continuous cocycle lifts.** -/
theorem isCobdy_defZ_iff : IsCobdy L.V L.defZ ↔
    ∃ h' : L.ι → L.ι → Fs.B → Spin77, (∀ i j, ContinuousOn (h' i j) (L.V i ∩ L.V j)) ∧
      (∀ i j, ∀ y ∈ L.V i ∩ L.V j, spinToO77 (h' i j y) = spinToO77 (L.h i j y)) ∧
      (∀ i j k, ∀ y ∈ L.V3 i j k, h' i j y * h' j k y = h' i k y) := by
  constructor
  · rintro ⟨b, hb, he⟩
    refine ⟨fun i j y => L.h i j y * sgn (b i j y), fun i j =>
      (L.cont_h i j).mul (continuous_sgn.comp_continuousOn (hb i j)), fun i j y _ => by
        rw [map_mul, spinToO77_sgn, mul_one], fun i j k y hy => ?_⟩
    have hd := he i j k y hy
    simp only [Pi.zero_apply, zero_add] at hd
    rw [← mul_inv_eq_one, central3, ← L.sgn_defZ hy, ← sgn_add, hd]
    have : δ1 b i j k y + (b i j y + b j k y + b i k y) = 0 := by
      simp only [δ1, sub_eq_add_neg, zmod2_neg]
      linear_combination zmod2_two (b i j y) + zmod2_two (b j k y) + zmod2_two (b i k y)
    rw [this]; rfl
  · rintro ⟨h', hc, hl, hco⟩
    obtain ⟨b, hb, he⟩ := L.defZ_indep h' hc hl
    refine ⟨b, hb, fun i j k y hy => ?_⟩
    have h0 : (L.withH h' hc hl).defZ i j k y = 0 := by
      show sgnInv (h' i j y * h' j k y * (h' i k y)⁻¹) = 0
      rw [hco i j k y hy, mul_inv_cancel]; simp [sgnInv]
    have := he i j k y hy
    rw [h0] at this
    simp only [Pi.zero_apply, zero_add]
    rw [eq_neg_of_add_eq_zero_left this.symm, zmod2_neg]

end LiftData

end Gen

/-! ### The sheet cover of `Ytilde X` -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **Lift data on the sheet cover**, from continuous lifts of the transition functions `transI`. -/
def sheetLD (h : TimeIdx X → TimeIdx X → Ytilde X → Spin77)
    (hh : ∀ I J, ContinuousOn (h I J) (sheetY I ∩ sheetY J))
    (hl : ∀ I J, ∀ p ∈ sheetY I ∩ sheetY J, spinToO77 (h I J p) = transI I J p) :
    Gen.LiftData (coverFS X) :=
  ⟨TimeIdx X, sheetY, isOpen_sheetY, exists_sheetY, secI, fun I => (continuousOn_secI I).mono fun q hq => hq.1,
    fun I q _ => proj_secI I q, h, hh, fun I J p hp => by rw [hl I J p hp]; exact secI_act_transI I J p⟩

/-- **On the sheet cover, the defect class vanishes iff the hypotheses of
`exists_coverSpin_of_lifts` hold** (continuous cocycle lifts of `transI`). -/
theorem sheet_isCobdy_iff (h : TimeIdx X → TimeIdx X → Ytilde X → Spin77)
    (hh : ∀ I J, ContinuousOn (h I J) (sheetY I ∩ sheetY J))
    (hl : ∀ I J, ∀ p ∈ sheetY I ∩ sheetY J, spinToO77 (h I J p) = transI I J p) :
    Gen.IsCobdy (sheetLD h hh hl).V (sheetLD h hh hl).defZ ↔
      ∃ h' : TimeIdx X → TimeIdx X → Ytilde X → Spin77,
        (∀ I J, ContinuousOn (h' I J) (sheetY I ∩ sheetY J)) ∧
        (∀ I J, ∀ p ∈ sheetY I ∩ sheetY J, spinToO77 (h' I J p) = transI I J p) ∧
        (∀ I J K, ∀ p ∈ sheetY I ∩ sheetY J ∩ sheetY K, h' I J p * h' J K p = h' I K p) := by
  rw [Gen.LiftData.isCobdy_defZ_iff]
  constructor
  · rintro ⟨h', hc, hl', hco⟩
    exact ⟨h', hc, fun I J p hp => (hl' I J p hp).trans (hl I J p hp), hco⟩
  · rintro ⟨h', hc, hl', hco⟩
    exact ⟨h', hc, fun I J p hp => (hl' I J p hp).trans (hl I J p hp).symm, hco⟩

/-- **A vanishing defect class gives a `Spin⁺(7,7)` structure over the whole cover** with image
`redT X`. -/
theorem exists_coverSpin_of_isCobdy (h : TimeIdx X → TimeIdx X → Ytilde X → Spin77)
    (hh : ∀ I J, ContinuousOn (h I J) (sheetY I ∩ sheetY J))
    (hl : ∀ I J, ∀ p ∈ sheetY I ∩ sheetY J, spinToO77 (h I J p) = transI I J p)
    (hc : Gen.IsCobdy (sheetLD h hh hl).V (sheetLD h hh hl).defZ) :
    ∃ S : CoverSpin X, Set.range S.Φ = redT X := by
  obtain ⟨h', hc', hl', hco⟩ := (sheet_isCobdy_iff h hh hl).mp hc
  exact exists_coverSpin_of_lifts h' hc' hl' fun I J K p hp => hco I J K p hp

/-! ### Instance -/

/-- Lift data with the constant lifts `−1` over the global frame of the cover of `ℝ⁴` (two copies of
the whole cover). Its lifts are not a cocycle. -/
def trivLD : Gen.LiftData (coverFS R4) :=
  ⟨Bool, fun _ => Set.univ, fun _ => isOpen_univ, fun _ => ⟨true, Set.mem_univ _⟩,
    fun _ => frameR4.secX,
    fun _ => frameR4.continuous_secX.continuousOn, fun _ _ _ => rfl, fun _ _ _ => negOne,
    fun _ _ => continuousOn_const, fun _ _ y _ => by
      rw [spinToO77_negOne]
      exact ((coverFS R4).act_one _).symm⟩

lemma trivLD_not_cocycle (i j k : trivLD.ι) (y : (coverFS R4).B) :
    trivLD.h i j y * trivLD.h j k y ≠ trivLD.h i k y := by
  show negOne * negOne ≠ negOne
  rw [Gen.negOne_mul_negOne]; exact negOne_ne_one.symm

/-- Its defect is the nonzero cocycle `1`. -/
lemma defZ_trivLD (i j k : trivLD.ι) (y : (coverFS R4).B) : trivLD.defZ i j k y = 1 := by
  show Gen.sgnInv (negOne * negOne * negOne⁻¹) = 1
  rw [mul_inv_cancel_right]
  simp [Gen.sgnInv, negOne_ne_one]

/-- …and a coboundary (of the constant 1-cochain `1`), so it can be corrected into cocycle lifts. -/
lemma isCobdy_trivLD : Gen.IsCobdy trivLD.V trivLD.defZ :=
  ⟨fun _ _ _ => 1, fun _ _ => continuousOn_const, fun i j k y _ => by
    rw [defZ_trivLD]; simp [Gen.δ1]⟩

end

end GU.Library
