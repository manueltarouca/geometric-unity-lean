/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.DefectClass

/-!
# Genuine lifts of the sheet transitions for parallelisable `X`

`DefectClass.lean` defines the ℤ/2 defect class for any lifts of the transition functions, but never
constructs lifts on the sheet cover. Here, for `X` with a global frame `T : TXFrame X`:

* **`gaugeO I p`**: the transition from the global frame `secX p` to the chart frame `secI I p`; it is
  `SO₀`-valued on the sheet (`gaugeO_mem`), continuous there (`continuousOn_gaugeO`), and
  `transI I J = (gaugeO I)⁻¹ · gaugeO J` (`transI_eq_gauge`).
* **The refinement** `refV (I, p₀) ⊆ sheetY I`: the part of the sheet of `I` where `gaugeO I` stays in
  one evenly covered neighbourhood of `gaugeO I p₀` for the covering `Spin(7,7) → SO₀(7,7)`
  (`isCoveringMap_spinToSO0`); they cover `Ytilde X` (`refLD.cover`, `mem_refV`). On it `gaugeO I` has a continuous
  lift `lam` (`spinToO77_lam`), and **`refLD T`** is lift data whose sections are the chart frames
  `secI I` (refinement map `(I, p₀) ↦ I`, `refV_sub`, `refLD_σ`) and whose lifts `lam⁻¹ · lam` lift
  `transI` (`refLD_lift`).
* The lifts are a cocycle by construction (`lam⁻¹ · lam`), so the defect is identically `0`
  (`defZ_refLD`) and the class vanishes trivially (`isCobdy_refLD`); the substance is the existence of the
  continuous lifts. They give a `Spin⁺(7,7)` structure with image `redT X` (`exists_coverSpin_refLD`,
  the same statement as `exists_coverSpin_parallel`, re-derived from these lifts; the two structures are
  not compared).

Instances: `ℝ⁴` and `ℝ⁴` minus a plane (`isCobdy_refLD_R4`, `isCobdy_refLD_hole`).
The lifts are on a refinement of the sheet cover, not on the sheets themselves: an instance of
`sheetLD` itself would need lifts of `gaugeO I` on the whole sheet, a π₁ question not formalised.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### Local sections of `Spin(7,7) → SO₀(7,7)` -/

/-- A local homeomorphism chart of the covering near a preimage of `g`. -/
def locChart (g : SO0) : OpenPartialHomeomorph Spin77 SO0 :=
  (isCoveringMap_spinToSO0.isLocalHomeomorph (spinToSO0_surjective g).choose).choose

lemma locChart_spec (g : SO0) : g ∈ (locChart g).target ∧ ∀ x, spinToSO0 x = locChart g x := by
  obtain ⟨hx, he⟩ := (isCoveringMap_spinToSO0.isLocalHomeomorph (spinToSO0_surjective g).choose).choose_spec
  refine ⟨?_, fun x => by unfold locChart; exact congrFun he x⟩
  have := (locChart g).map_source hx
  have hg : (locChart g) (spinToSO0_surjective g).choose = g := by
    unfold locChart; rw [← congrFun he]; exact (spinToSO0_surjective g).choose_spec
  rwa [hg] at this

namespace TXFrame

variable (T : TXFrame X)

lemma proj_secX_snd (p : Ytilde X) : projOFr (T.secX p).1.2 = piT p := (T.secX p).2.symm

/-- The gauge: from the global frame to the chart frame. -/
def gaugeO (I : TimeIdx X) (p : Ytilde X) : O77 := transO (T.secX p).1.2 (secI I p).1.2

lemma gaugeO_spec (I : TimeIdx X) (p : Ytilde X) :
    actOFr' (T.secX p).1.2 (T.gaugeO I p) = (secI I p).1.2 :=
  transO_spec ((T.proj_secX_snd p).trans (proj_secI_snd I p).symm)

lemma gaugeO_mem {I : TimeIdx X} {p : Ytilde X} (hp : p ∈ sheetY I) : T.gaugeO I p ∈ SO0 := by
  obtain ⟨g, hg, hge⟩ := redT_reduction.2.2.2 _ (T.secX_mem_redT p) _ (secI_mem_redT hp) rfl
  have : T.gaugeO I p = g := transO_unique ((T.proj_secX_snd p).trans (proj_secI_snd I p).symm)
    (congrArg (fun z : OFrT X => z.1.2) hge)
  rw [this]; exact hg

lemma continuousOn_gaugeO (I : TimeIdx X) : ContinuousOn (T.gaugeO I) (sheetY I) := by
  have ha : ContinuousOn (fun p => (T.secX p).1.2) (sheetY I) :=
    (continuous_OFrT_snd.comp T.continuous_secX).continuousOn
  have hb : ContinuousOn (fun p => (secI I p).1.2) (sheetY I) :=
    (continuous_OFrT_snd.comp_continuousOn (continuousOn_secI I)).mono fun p hp => hp.1
  exact continuousOn_transO' (isOpen_sheetY I) ha hb fun p _ =>
    (T.proj_secX_snd p).trans (proj_secI_snd I p).symm

/-- **The transitions factor through the gauge.** -/
lemma transI_eq_gauge (I J : TimeIdx X) (p : Ytilde X) :
    transI I J p = (T.gaugeO I p)⁻¹ * T.gaugeO J p := by
  apply transO_unique ((proj_secI_snd I p).trans (proj_secI_snd J p).symm)
  rw [← T.gaugeO_spec I p, actOFr'_mul, mul_inv_cancel_left, T.gaugeO_spec]

open Classical in
/-- The gauge as an `SO₀`-valued map (`1` off the sheet). -/
def gaugeS (I : TimeIdx X) (p : Ytilde X) : SO0 :=
  if h : p ∈ sheetY I then ⟨T.gaugeO I p, T.gaugeO_mem h⟩ else 1

lemma gaugeS_val {I : TimeIdx X} {p : Ytilde X} (h : p ∈ sheetY I) :
    (T.gaugeS I p : O77) = T.gaugeO I p := by
  rw [gaugeS, dite_eq_left_of_eq_true (eq_true h)]

lemma continuousOn_gaugeS (I : TimeIdx X) : ContinuousOn (T.gaugeS I) (sheetY I) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (sheetY I).domRestrict (T.gaugeS I) = fun q => ⟨T.gaugeO I q, T.gaugeO_mem q.2⟩ :=
    funext fun q => Subtype.ext (T.gaugeS_val q.2)
  rw [e]
  exact (continuousOn_iff_continuous_domRestrict.mp (T.continuousOn_gaugeO I)).subtype_mk _

/-! ### The refinement and its lifts -/

/-- Indices of the refinement: a sheet and a base point. -/
abbrev RefIdx (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] := TimeIdx X × Ytilde X

/-- The refined open sets. -/
def refV (a : RefIdx X) : Set (Ytilde X) :=
  sheetY a.1 ∩ T.gaugeS a.1 ⁻¹' (locChart (T.gaugeS a.1 a.2)).target

lemma refV_sub (a : RefIdx X) : T.refV a ⊆ sheetY a.1 := fun _ h => h.1

lemma isOpen_refV (a : RefIdx X) : IsOpen (T.refV a) :=
  (T.continuousOn_gaugeS a.1).isOpen_inter_preimage (isOpen_sheetY a.1) (locChart _).open_target

lemma mem_refV {I : TimeIdx X} {p : Ytilde X} (hp : p ∈ sheetY I) : p ∈ T.refV (I, p) :=
  ⟨hp, (locChart_spec _).1⟩

/-- The local lift of the gauge. -/
def lam (a : RefIdx X) (p : Ytilde X) : Spin77 := (locChart (T.gaugeS a.1 a.2)).symm (T.gaugeS a.1 p)

lemma continuousOn_lam (a : RefIdx X) : ContinuousOn (T.lam a) (T.refV a) :=
  (locChart _).continuousOn_symm.comp ((T.continuousOn_gaugeS a.1).mono fun _ h => h.1) fun _ h => h.2

lemma spinToO77_lam {a : RefIdx X} {p : Ytilde X} (hp : p ∈ T.refV a) :
    spinToO77 (T.lam a p) = T.gaugeO a.1 p := by
  have h1 : spinToSO0 (T.lam a p) = T.gaugeS a.1 p := by
    rw [(locChart_spec _).2, lam, (locChart _).right_inv hp.2]
  have h2 := congrArg Subtype.val h1
  rw [T.gaugeS_val hp.1] at h2
  exact h2

/-- The lifts of the transitions. -/
def hRef (a b : RefIdx X) (p : Ytilde X) : Spin77 := (T.lam a p)⁻¹ * T.lam b p

lemma refLD_lift_eq {a b : RefIdx X} {p : Ytilde X} (hp : p ∈ T.refV a ∩ T.refV b) :
    spinToO77 (T.hRef a b p) = transI a.1 b.1 p := by
  rw [hRef, map_mul, map_inv, T.spinToO77_lam hp.1, T.spinToO77_lam hp.2, T.transI_eq_gauge]

/-- **Lift data on the refinement of the sheet cover**, with the chart frames as sections. -/
def refLD : Gen.LiftData (coverFS X) where
  ι := RefIdx X
  V := T.refV
  isOpen_V := T.isOpen_refV
  cover p := by
    obtain ⟨I, hI⟩ := exists_sheetY p
    exact ⟨(I, p), T.mem_refV hI⟩
  σ a := secI a.1
  cont_σ a := (continuousOn_secI a.1).mono fun _ h => (T.refV_sub a h).1
  proj_σ a q _ := proj_secI a.1 q
  h := T.hRef
  cont_h a b := ((T.continuousOn_lam a).mono Set.inter_subset_left).inv.mul
    ((T.continuousOn_lam b).mono Set.inter_subset_right)
  lift a b p hp := by
    show secI b.1 p = actT (secI a.1 p) (spinToO77 (T.hRef a b p))
    rw [T.refLD_lift_eq hp]
    exact secI_act_transI a.1 b.1 p

/-- The refinement map. -/
def refMap (a : RefIdx X) : TimeIdx X := a.1

lemma refV_sub_map (a : RefIdx X) : T.refV a ⊆ sheetY (refMap a) := T.refV_sub a

/-- The refinement map: each refined set lies in a sheet, with that sheet's chart frame. -/
lemma refLD_σ (a : RefIdx X) : (T.refLD).σ a = secI a.1 := rfl

/-- **The lifts lift the sheet transitions.** -/
lemma refLD_lift (a b : RefIdx X) (p : Ytilde X) (hp : p ∈ T.refV a ∩ T.refV b) :
    spinToO77 ((T.refLD).h a b p) = transI a.1 b.1 p := T.refLD_lift_eq hp

lemma refLD_cocycle (a b c : (T.refLD).ι) (p : (coverFS X).B) :
    (T.refLD).h a b p * (T.refLD).h b c p = (T.refLD).h a c p := by
  show (T.lam a p)⁻¹ * T.lam b p * ((T.lam b p)⁻¹ * T.lam c p) = (T.lam a p)⁻¹ * T.lam c p
  group

/-- **The defect vanishes**: these lifts are a cocycle. -/
lemma defZ_refLD (a b c : (T.refLD).ι) (p : (coverFS X).B) : (T.refLD).defZ a b c p = 0 := by
  show Gen.sgnInv ((T.refLD).h a b p * (T.refLD).h b c p * ((T.refLD).h a c p)⁻¹) = 0
  rw [T.refLD_cocycle, mul_inv_cancel]
  simp [Gen.sgnInv]

/-- The defect class vanishes (trivially: the lifts are a cocycle by construction). -/
theorem isCobdy_refLD : Gen.IsCobdy (T.refLD).V (T.refLD).defZ :=
  ⟨fun _ _ _ => 0, fun _ _ => continuousOn_const, fun a b c y _ => by
    rw [T.defZ_refLD]; simp [Gen.δ1]⟩

include T in
/-- **Consistency with `exists_coverSpin_parallel`**: the cocycle lifts on the refinement give a
`Spin⁺(7,7)` structure over the whole cover with image `redT X`. -/
theorem exists_coverSpin_refLD : ∃ S : CoverSpin X, Set.range S.Φ = redT X := by
  rw [coverSpin_iff_data]
  let D : Gen.SpinLiftData (coverFS X) :=
    ⟨Set.univ, isOpen_univ, RefIdx X, T.refV, T.isOpen_refV, fun _ => Set.subset_univ _,
      fun p _ => (T.refLD).cover p, fun a => secI a.1, (T.refLD).cont_σ, (T.refLD).proj_σ, T.hRef,
      (T.refLD).cont_h, (T.refLD).lift, fun a b c p _ => T.refLD_cocycle a b c p⟩
  refine ⟨D, rfl, ?_⟩
  rw [D.range_Φ]
  ext q
  constructor
  · rintro ⟨-, hq⟩
    obtain ⟨a, ha⟩ := (T.refLD).cover ((coverFS X).proj q)
    obtain ⟨g, hg, e⟩ := hq a ha
    rw [e]
    exact redT_reduction.2.1 _ (secI_mem_redT (T.refV_sub a ha)) _ hg
  · intro hq
    refine ⟨Set.mem_univ _, fun a ha => ?_⟩
    obtain ⟨g, hg, e⟩ := redT_reduction.2.2.2 _ (secI_mem_redT (T.refV_sub a ha)) _ hq rfl
    exact ⟨g, hg, e.symm⟩

end TXFrame

/-! ### Instances -/

lemma isCobdy_refLD_R4 : Gen.IsCobdy (frameR4.refLD).V (frameR4.refLD).defZ := frameR4.isCobdy_refLD

lemma isCobdy_refLD_hole : Gen.IsCobdy (frameHole.refLD).V (frameHole.refLD).defZ :=
  frameHole.isCobdy_refLD

end

end GU.Library
