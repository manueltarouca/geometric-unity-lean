import GU.Bundle.CoverSpinAPI
import GU.Bundle.TimeCoverReduction

/-!
# Phase 6, item 5: spin structures on the cover for general `X` (local, and the global obstruction)

For every `X`:

* **`sheetY I`**: the sheet of the cover over the chart domain of a chart covector `I`; these are open and
  cover `Ytilde X` (`exists_sheetY`).
* **`secI I`**: a continuous frame of the pulled-back bundle over `sheetY I` (the chart-local gauge
  frame), with values in the reduction `redT X` (`secI_mem_redT`).
* **`exists_local_spin_cover`**: over a neighbourhood of every point of the cover there are spin-lift data
  (hence a spin structure, `Gen.SpinLiftData.toStructure`) whose image lies in `redT X`.
* **`transI_mem_SO0`**, **`continuousOn_transI`**, **`transI_cocycle`**: the transition functions
  between these frames are continuous `SO₀`-valued and form a cocycle. Lifts to `Spin(7,7)` exist
  pointwise on overlaps (`exists_lift_transI`, `exists_defect`), and any lifts have defect in `{±1}`
  (`cover_defect_mem`). That defect is, informally, a Čech representative of `w₂` of the reduction.
* **`exists_coverSpin_of_lifts`**: if the transitions admit continuous cocycle lifts, there is a global
  spin structure on the cover with image exactly `redT X` (the formal half of "global iff the defect can
  be made trivial").

Not formalised (path (b)): the global question for general `X` is whether `w₂` of `redT X` (the class of
the defect) vanishes in `H²(Ytilde X; ℤ/2)`. This may fail for some `X` (informal: it involves `w₂` of
`X`), and neither the class nor `H²(·; ℤ/2)` is in Mathlib. Over `ℝ⁴` it holds: `coverSpin`.
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- The sheet of the chart covector `I`. -/
def sheetY (I : TimeIdx X) : Set (Ytilde X) :=
  {p | p.proj ∈ tV I ∧ ((tildeCore X).localTriv I p).2 = false}

lemma isOpen_sheetY (I : TimeIdx X) : IsOpen (sheetY I) := by
  have hcont : ContinuousOn (fun p : Ytilde X => ((tildeCore X).localTriv I p).2)
      {p : Ytilde X | p.proj ∈ tV I} := by
    refine continuous_snd.comp_continuousOn (((tildeCore X).localTriv I).continuousOn.mono fun p hp => ?_)
    rw [Trivialization.mem_source]; exact hp
  exact hcont.isOpen_inter_preimage ((isOpen_tV I).preimage continuous_piT) (isOpen_discrete {false})

lemma exists_sheetY (p : Ytilde X) : ∃ I : TimeIdx X, p ∈ sheetY I := by
  have hc : cov ((Zt X).indexAt (baseX p.proj), rep p) (baseX p.proj) = rep p := by
    show (transMat _ _)ᵀ *ᵥ rep p = rep p
    rw [Acc_self, Matrix.transpose_one, Matrix.one_mulVec]
  have hd : p.proj ∈ tV ((Zt X).indexAt (baseX p.proj), rep p) := by
    refine ⟨(Zt X).mem_baseSet_at _, ?_⟩
    show 0 < lp _ (cov _ (baseX p.proj)) (cov _ (baseX p.proj))
    rw [hc]; exact timelike_rep p
  refine ⟨((Zt X).indexAt (baseX p.proj), rep p), hd, (mem_future_iff_localTriv _ p hd).mp ?_⟩
  rw [hc]
  exact ⟨timelike_rep p, timelike_rep p⟩

lemma exists_frame_at (y : Y13o X) : ∃ q : OFr X, projOFr q = y := (ofrFS X).proj_surj y

/-- Some frame over `y`. -/
def someFrame (y : Y13o X) : OFr X := (exists_frame_at y).choose

lemma proj_someFrame (y : Y13o X) : projOFr (someFrame y) = y := (exists_frame_at y).choose_spec

open Classical in
/-- The second component of the chart-local frame. -/
def secI2 (I : TimeIdx X) (p : Ytilde X) : OFr X :=
  if h : p.proj ∈ tV I then rawO p.proj (locP I p.proj) (isLF_locP h) else someFrame (piT p)

lemma proj_secI2 (I : TimeIdx X) (p : Ytilde X) : projOFr (secI2 I p) = piT p := by
  unfold secI2
  split_ifs with h
  · rfl
  · exact proj_someFrame _

/-- The chart-local frame of the pulled-back bundle over the sheet `I`. -/
def secI (I : TimeIdx X) (p : Ytilde X) : OFrT X := ⟨(p, secI2 I p), (proj_secI2 I p).symm⟩

lemma secI_fst (I : TimeIdx X) (p : Ytilde X) : (secI I p).1.1 = p := rfl

lemma secI_snd {I : TimeIdx X} {p : Ytilde X} (h : p.proj ∈ tV I) :
    (secI I p).1.2 = rawO p.proj (locP I p.proj) (isLF_locP h) := by
  show secI2 I p = _
  exact dif_pos h

lemma continuousOn_secI (I : TimeIdx X) : ContinuousOn (secI I) {p : Ytilde X | p.proj ∈ tV I} := by
  have hO : IsOpen {p : Ytilde X | p.proj ∈ tV I} := (isOpen_tV I).preimage continuous_piT
  have hraw := continuousOn_rawF hO (y := fun p : Ytilde X => ((piT p : Y13o X) : Yobs X))
    (continuous_subtype_val.comp continuous_piT) I.1 (fun p hp => hp.1)
    (Q := fun p => hatP I (piT p))
    (by
      have hc : ContinuousOn (fun p : Ytilde X => chartG I.1 (piT p)) {p : Ytilde X | p.proj ∈ tV I} :=
        (continuousOn_chartG I.1).comp continuous_piT.continuousOn fun p hp => hp.1
      exact continuousOn_const.mul (continuousOn_gaugeP.comp ((continuousOn_const.mul hc).mul
        continuousOn_const) fun p hp => conj_mem_gaugeSet hp))
    (fun p hp => isUnit_hatP hp)
  have h2 : ContinuousOn (secI2 I) {p : Ytilde X | p.proj ∈ tV I} := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hraw.congr fun p hp => ?_
    show ((secI2 I p : OFr X) : HomTotM X) = _
    have e : secI2 I p = rawO p.proj (locP I p.proj) (isLF_locP hp) := dif_pos hp
    rw [e]; rfl
  exact (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr (continuousOn_id.prodMk h2)

lemma proj_secI (I : TimeIdx X) (p : Ytilde X) : (coverFS X).proj (secI I p) = p := secI_fst I p

/-- **The local frame lies in the reduction** on its sheet. -/
lemma secI_mem_redT {I : TimeIdx X} {p : Ytilde X} (hp : p ∈ sheetY I) : secI I p ∈ redT X := by
  have hfut : cov I (baseX p.proj) ∈ future p := (mem_future_iff_localTriv I p hp.1).mpr hp.2
  have hf : tcov (locP I p.proj) ∈ future p := by
    rw [tcov_locP hp.1]
    exact smul_mem_future hfut (inv_pos.mpr (gaugeP_00_pos (conj_mem_gaugeSet hp.1)))
  refine ⟨locP I p.proj, ?_, ?_, 1, one_mem _, ?_⟩
  · rw [secI_fst]; exact isLF_locP hp.1
  · rw [secI_fst]; exact hf
  · rw [actOFr'_one, secI_snd hp.1]; rfl

/-- **Local spin structures on the cover, compatible with the reduction**, near every point. -/
theorem exists_local_spin_cover (p : Ytilde X) :
    ∃ D : Gen.SpinLiftData (coverFS X), p ∈ D.W ∧ Set.range D.Φ ⊆ redT X := by
  obtain ⟨I, hI⟩ := exists_sheetY p
  refine ⟨Gen.SpinLiftData.ofSection (sheetY I) (isOpen_sheetY I) (secI I)
    ((continuousOn_secI I).mono fun q hq => hq.1) (fun q _ => proj_secI I q), hI, ?_⟩
  rintro z ⟨w, rfl⟩
  exact redT_reduction.2.1 _ (secI_mem_redT w.proj.2) _ (spinToO77_mem _)

/-! ### Transition functions and the defect -/

/-- The transition between two frames continuous on an open set is continuous there. -/
theorem continuousOn_transO' {Z : Type*} [TopologicalSpace Z] {S : Set Z} (hS : IsOpen S)
    {a b : Z → OFr X} (ha : ContinuousOn a S) (hb : ContinuousOn b S)
    (hab : ∀ z ∈ S, projOFr (a z) = projOFr (b z)) :
    ContinuousOn (fun z => transO (a z) (b z)) S := by
  intro z0 hz0
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨V', hV', hz₀, σ', τ', hτc, hrec⟩ := (ofrFS X).locTriv (projOFr (b z0))
  set N : Set Z := S ∩ b ⁻¹' (projOFr ⁻¹' V')
  have hN : IsOpen N := hb.isOpen_inter_preimage hS (hV'.preimage continuous_projOFr)
  have hmem : N ∈ 𝓝 z0 := hN.mem_nhds ⟨hz0, hz₀⟩
  have hform : ∀ z ∈ N, transO (a z) (b z) = (τ' (a z))⁻¹ * τ' (b z) := by
    intro z hz
    apply transO_unique (hab z hz.1)
    set y := projOFr (b z)
    have hy : projOFr (a z) = y := hab z hz.1
    have e1 : actOFr' (σ' y) (τ' (a z)) = a z := by
      have := hrec (a z) (by show projOFr (a z) ∈ V'; rw [hy]; exact hz.2)
      rw [show (ofrFS X).proj (a z) = y from hy] at this
      exact this
    calc actOFr' (a z) ((τ' (a z))⁻¹ * τ' (b z))
        = actOFr' (actOFr' (σ' y) (τ' (a z))) ((τ' (a z))⁻¹ * τ' (b z)) := by rw [e1]
      _ = actOFr' (σ' y) (τ' (b z)) := by
          have := actOFr'_mul (σ' y) (τ' (a z)) ((τ' (a z))⁻¹ * τ' (b z))
          rw [mul_inv_cancel_left] at this
          exact this
      _ = b z := hrec (b z) hz.2
  have h1 : ContinuousOn (fun z => τ' (a z)) N :=
    hτc.comp (ha.mono Set.inter_subset_left) fun z hz => by
      show projOFr (a z) ∈ V'
      rw [hab z hz.1]; exact hz.2
  have h2 : ContinuousOn (fun z => τ' (b z)) N :=
    hτc.comp (hb.mono Set.inter_subset_left) fun z hz => hz.2
  exact ((h1.inv.mul h2).congr hform).continuousAt hmem

/-- The transition function between two local frames. -/
def transI (I J : TimeIdx X) (p : Ytilde X) : O77 := transO (secI I p).1.2 (secI J p).1.2

lemma proj_secI_snd (I : TimeIdx X) (p : Ytilde X) : projOFr (secI I p).1.2 = piT p := by
  rw [← (secI I p).2, secI_fst]

lemma transI_spec (I J : TimeIdx X) (p : Ytilde X) :
    actOFr' (secI I p).1.2 (transI I J p) = (secI J p).1.2 :=
  transO_spec ((proj_secI_snd I p).trans (proj_secI_snd J p).symm)

/-- **The transition functions are `SO₀`-valued.** -/
theorem transI_mem_SO0 {I J : TimeIdx X} {p : Ytilde X} (hI : p ∈ sheetY I) (hJ : p ∈ sheetY J) :
    transI I J p ∈ SO0 := by
  have h1 := secI_mem_redT hI
  have h2 := secI_mem_redT hJ
  obtain ⟨g, hg, hge⟩ := redT_reduction.2.2.2 _ h1 _ h2 (by rw [secI_fst, secI_fst])
  have : transI I J p = g := transO_unique ((proj_secI_snd I p).trans (proj_secI_snd J p).symm)
    (congrArg (fun z : OFrT X => z.1.2) hge)
  rw [this]; exact hg

/-- **The transition functions are continuous.** -/
theorem continuousOn_transI (I J : TimeIdx X) : ContinuousOn (transI I J) (sheetY I ∩ sheetY J) := by
  have hO : IsOpen (sheetY I ∩ sheetY J) := (isOpen_sheetY I).inter (isOpen_sheetY J)
  have ha : ContinuousOn (fun p => (secI I p).1.2) (sheetY I ∩ sheetY J) :=
    (continuous_OFrT_snd.comp_continuousOn (continuousOn_secI I)).mono fun p hp => hp.1.1
  have hb : ContinuousOn (fun p => (secI J p).1.2) (sheetY I ∩ sheetY J) :=
    (continuous_OFrT_snd.comp_continuousOn (continuousOn_secI J)).mono fun p hp => hp.2.1
  exact continuousOn_transO' hO ha hb fun p _ =>
    (proj_secI_snd I p).trans (proj_secI_snd J p).symm

/-- **They form a cocycle.** -/
theorem transI_cocycle (I J K : TimeIdx X) (p : Ytilde X) :
    transI I J p * transI J K p = transI I K p := by
  apply (transO_unique ((proj_secI_snd I p).trans (proj_secI_snd K p).symm) ?_).symm
  rw [← actOFr'_mul, transI_spec, transI_spec]

/-- **Lifts of the transitions to `Spin(7,7)` exist pointwise on overlaps** (`transI` is `SO₀`-valued
there and `Spin(7,7) → SO₀(7,7)` is onto). -/
lemma exists_lift_transI {I J : TimeIdx X} {p : Ytilde X} (hI : p ∈ sheetY I) (hJ : p ∈ sheetY J) :
    ∃ t : Spin77, spinToO77 t = transI I J p := by
  obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨transI I J p, transI_mem_SO0 hI hJ⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- **Any lifts of the transitions to `Spin(7,7)` have defect in `{±1}`**, at any point where the three
transitions lift (which is the case on triple overlaps, `exists_defect`). Informally, this is the Čech
cocycle of `w₂` of the reduction. -/
theorem cover_defect_mem {I J K : TimeIdx X} {p : Ytilde X} {tIJ tJK tIK : Spin77}
    (hIJ : spinToO77 tIJ = transI I J p) (hJK : spinToO77 tJK = transI J K p)
    (hIK : spinToO77 tIK = transI I K p) :
    tIJ * tJK * tIK⁻¹ = 1 ∨ tIJ * tJK * tIK⁻¹ = negOne := by
  rw [← spinToO77_eq_one_iff, map_mul, map_mul, map_inv, hIJ, hJK, hIK, transI_cocycle, mul_inv_cancel]

/-- Non-vacuity: at every point of a triple overlap the defect is defined. -/
theorem exists_defect {I J K : TimeIdx X} {p : Ytilde X} (hI : p ∈ sheetY I) (hJ : p ∈ sheetY J)
    (hK : p ∈ sheetY K) : ∃ tIJ tJK tIK : Spin77, spinToO77 tIJ = transI I J p ∧
      spinToO77 tJK = transI J K p ∧ spinToO77 tIK = transI I K p := by
  obtain ⟨a, ha⟩ := exists_lift_transI hI hJ
  obtain ⟨b, hb⟩ := exists_lift_transI hJ hK
  obtain ⟨c, hc⟩ := exists_lift_transI hI hK
  exact ⟨a, b, c, ha, hb, hc⟩

lemma secI_act_transI (I J : TimeIdx X) (p : Ytilde X) :
    secI J p = actT (secI I p) (transI I J p) := by
  apply Subtype.ext
  show (p, (secI J p).1.2) = (p, actOFr' (secI I p).1.2 (transI I J p))
  rw [transI_spec]

/-- **From continuous cocycle lifts of the transitions, a global spin structure on the cover** whose
image is exactly the reduction `redT X`. -/
theorem exists_coverSpin_of_lifts (h : TimeIdx X → TimeIdx X → Ytilde X → Spin77)
    (hh : ∀ I J, ContinuousOn (h I J) (sheetY I ∩ sheetY J))
    (hl : ∀ I J, ∀ p ∈ sheetY I ∩ sheetY J, spinToO77 (h I J p) = transI I J p)
    (hc : ∀ I J K, ∀ p ∈ sheetY I ∩ sheetY J ∩ sheetY K, h I J p * h J K p = h I K p) :
    ∃ S : CoverSpin X, Set.range S.Φ = redT X := by
  rw [coverSpin_iff_data]
  let D : Gen.SpinLiftData (coverFS X) :=
    ⟨Set.univ, isOpen_univ, TimeIdx X, sheetY, isOpen_sheetY, fun _ => Set.subset_univ _,
      fun p _ => exists_sheetY p, secI, fun I => (continuousOn_secI I).mono fun q hq => hq.1,
      fun I q _ => proj_secI I q, h, hh,
      fun I J p hp => by rw [hl I J p hp]; exact secI_act_transI I J p, hc⟩
  refine ⟨D, rfl, ?_⟩
  rw [D.range_Φ]
  ext q
  constructor
  · rintro ⟨-, hq⟩
    obtain ⟨I, hI⟩ := exists_sheetY ((coverFS X).proj q)
    obtain ⟨g, hg, e⟩ := hq I hI
    rw [e]
    exact redT_reduction.2.1 _ (secI_mem_redT hI) _ hg
  · intro hq
    refine ⟨Set.mem_univ _, fun I hI => ?_⟩
    obtain ⟨g, hg, e⟩ := redT_reduction.2.2.2 _ (secI_mem_redT hI) _ hq rfl
    exact ⟨g, hg, e.symm⟩

end

end GU.Library
