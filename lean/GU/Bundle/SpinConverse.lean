import GU.Bundle.SpinStructure

/-!
# Phase 4, item 1: spin structures ⇔ cocycle lifts

`SpinStructure X`: a topological principal `Spin(7,7)`-bundle over an open `W ⊆ Y13` with equivariant local
trivialisations and a continuous, base-preserving, `ρ`-equivariant map `Φ` to the frame bundle.
(The double-cover properties of `Φ` are not assumed; they follow.)

* `SpinStructure.toData`: the sections `sᵢ = eᵢ⁻¹(y, 1)` of the trivialisations give local frames
  `σᵢ = Φ ∘ sᵢ` and lifts `hᵢⱼ = (eᵢ (sⱼ y)).2` of their transition functions, with trivial defect.
* `SpinLiftData.toStructure`: the construction of `SpinStructure.lean`.
* **`exists_data_iff_exists_structure`**: for any set `Q` of frames, cocycle lifts with image `Q`
  exist iff a spin structure with image `Q` exists.
* **`SpinStructure.isoToData`**: every spin structure is isomorphic (`SpinIso`: an equivariant
  homeomorphism over `Y13` commuting with `Φ`) to the one glued from its own cocycle.
-/

namespace GU.Library

open Bundle GU GU.Observerse GU.Spinor TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **A spin structure on the frame bundle over an open `W ⊆ Y13`** (`W` cannot be all of `Y13`:
`no_spinStructure`): a principal `Spin(7,7)`-bundle `P → W`
(local trivialisations `e i` over an open cover in which the action is right multiplication) with a
continuous, base-preserving, `ρ`-equivariant map `Φ : P → OFr`. Not assumed, but derived: freeness
(`act_free`), the two-point fibres of `Φ` (`Φ_eq_iff`), that `Φ` covers an `SO₀`-reduction
(`range_Φ_eq`, `isCoveringMap_Φ`). `act_one`, `act_mul`, `proj_act`, `continuous_act` are in fact
redundant given `e_act`; they are kept for convenience. -/
structure SpinStructure (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] where
  W : Set (Y13o X)
  isOpen_W : IsOpen W
  P : Type
  top : TopologicalSpace P
  projS : P → W
  actS : P → Spin77 → P
  Φ : P → OFr X
  act_one : ∀ p, actS p 1 = p
  act_mul : ∀ p s t, actS (actS p s) t = actS p (s * t)
  proj_act : ∀ p t, projS (actS p t) = projS p
  continuous_act : Continuous fun pt : P × Spin77 => actS pt.1 pt.2
  ι : Type
  V : ι → Set (Y13o X)
  V_sub : ∀ i, V i ⊆ W
  cover : ∀ y ∈ W, ∃ i, y ∈ V i
  e : ι → Trivialization Spin77 projS
  baseSet_e : ∀ i, (e i).baseSet = Subtype.val ⁻¹' V i
  e_act : ∀ i, ∀ p ∈ (e i).source, ∀ t, e i (actS p t) = ((e i p).1, (e i p).2 * t)
  continuous_Φ : Continuous Φ
  proj_Φ : ∀ p, projOFr (Φ p) = (projS p : Y13o X)
  Φ_act : ∀ p t, Φ (actS p t) = actOFr' (Φ p) (spinToO77 t)

attribute [instance] SpinStructure.top

/-- **Isomorphism of spin structures**: an equivariant homeomorphism over `Y13` commuting with
the maps to the frame bundle. -/
structure SpinIso (S S' : SpinStructure X) where
  F : S.P ≃ₜ S'.P
  proj_F : ∀ p, (S'.projS (F p) : Y13o X) = S.projS p
  act_F : ∀ p t, F (S.actS p t) = S'.actS (F p) t
  Φ_F : ∀ p, S'.Φ (F p) = S.Φ p

namespace SpinStructure

variable (S : SpinStructure X)

/-- The section of the trivialisation `i`. -/
def sec (i : S.ι) (y : S.W) : S.P := (S.e i).toOpenPartialHomeomorph.symm (y, 1)

lemma mem_target (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) (t : Spin77) :
    (y, t) ∈ (S.e i).target := by
  rw [Trivialization.mem_target, S.baseSet_e]; exact hy

lemma mem_source_iff (i : S.ι) (p : S.P) : p ∈ (S.e i).source ↔ (S.projS p : Y13o X) ∈ S.V i := by
  rw [Trivialization.mem_source, S.baseSet_e]; rfl

lemma e_symm (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) (t : Spin77) :
    S.e i ((S.e i).toOpenPartialHomeomorph.symm (y, t)) = (y, t) :=
  (S.e i).right_inv (S.mem_target i hy t)

lemma e_sec (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) : S.e i (S.sec i y) = (y, 1) :=
  S.e_symm i hy 1

lemma proj_sec (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) : S.projS (S.sec i y) = y :=
  (S.e i).proj_symm_apply (S.mem_target i hy 1)

lemma sec_mem (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) : S.sec i y ∈ (S.e i).source :=
  (S.mem_source_iff i _).mpr (by rw [S.proj_sec i hy]; exact hy)

lemma continuousOn_sec (i : S.ι) : ContinuousOn (S.sec i) (Subtype.val ⁻¹' S.V i) :=
  (S.e i).toOpenPartialHomeomorph.continuousOn_symm.comp
    (continuousOn_id.prodMk continuousOn_const) fun _ hy => S.mem_target i hy 1

lemma fst_e (i : S.ι) {p : S.P} (hp : (S.projS p : Y13o X) ∈ S.V i) : (S.e i p).1 = S.projS p :=
  (S.e i).coe_fst ((S.mem_source_iff i p).mpr hp)

lemma act_mem (i : S.ι) {p : S.P} (hp : (S.projS p : Y13o X) ∈ S.V i) (t : Spin77) :
    S.actS p t ∈ (S.e i).source :=
  (S.mem_source_iff i _).mpr (by rw [S.proj_act]; exact hp)

/-- The coordinate of `sᵢ · t` is `t`. -/
lemma e_sec_act (i : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i) (t : Spin77) :
    S.e i (S.actS (S.sec i y) t) = (y, t) := by
  rw [S.e_act i _ (S.sec_mem i hy), S.e_sec i hy, one_mul]

/-- **Every point is `sᵢ · (its coordinate)`.** -/
lemma sec_act_coord (i : S.ι) {p : S.P} (hp : (S.projS p : Y13o X) ∈ S.V i) :
    S.actS (S.sec i (S.projS p)) (S.e i p).2 = p := by
  apply (S.e i).injOn (S.act_mem i (by rw [S.proj_sec i hp]; exact hp) _)
    ((S.mem_source_iff i p).mpr hp)
  show S.e i _ = S.e i p
  rw [S.e_sec_act i hp]
  exact Prod.ext (S.fst_e i hp).symm rfl

/-- The action is free. -/
lemma act_free (p : S.P) (t : Spin77) (h : S.actS p t = p) : t = 1 := by
  obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
  have hs := (S.mem_source_iff i p).mpr hi
  have := congrArg (fun q => (S.e i q).2) h
  simp only [S.e_act i p hs] at this
  exact mul_eq_left.mp this

/-- The transition lift `sⱼ = sᵢ · hᵢⱼ`. -/
def lift (i j : S.ι) (y : S.W) : Spin77 := (S.e i (S.sec j y)).2

lemma sec_eq (i j : S.ι) {y : S.W} (hy : (y : Y13o X) ∈ S.V i ∩ S.V j) :
    S.sec j y = S.actS (S.sec i y) (S.lift i j y) := by
  have h := S.sec_act_coord i (p := S.sec j y) (by rw [S.proj_sec j hy.2]; exact hy.1)
  rw [S.proj_sec j hy.2] at h
  exact h.symm

lemma isOpen_V (i : S.ι) : IsOpen (S.V i) := by
  have h : S.V i = Subtype.val '' (Subtype.val ⁻¹' S.V i : Set S.W) := by
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.mpr (S.V_sub i)]
  rw [h]
  refine S.isOpen_W.isOpenMap_subtype_val _ ?_
  rw [← S.baseSet_e]; exact (S.e i).open_baseSet

/-- A map on `Y13` is continuous on `V i` if its restriction to `W` is. -/
lemma continuousOn_of_val {Z : Type*} [TopologicalSpace Z] (i : S.ι) {g : Y13o X → Z}
    (h : ContinuousOn (g ∘ Subtype.val : S.W → Z) (Subtype.val ⁻¹' S.V i)) :
    ContinuousOn g (S.V i) := by
  intro y hy
  have hW : y ∈ S.W := S.V_sub i hy
  have hO : IsOpen (Subtype.val ⁻¹' S.V i : Set S.W) := (S.isOpen_V i).preimage continuous_subtype_val
  have hat := h.continuousAt (x := ⟨y, hW⟩) (hO.mem_nhds hy)
  exact ((S.isOpen_W.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hat).continuousWithinAt

open Classical in
/-- The local frame `Φ ∘ sᵢ`, extended to `Y13`. -/
def σd (i : S.ι) (y : Y13o X) : OFr X :=
  if hy : y ∈ S.W then S.Φ (S.sec i ⟨y, hy⟩)
  else
    let q := (orthoM_iff_13 (y : Yobs X)).mpr y.2
    ⟨q.choose, by rw [OFr, levelSet_Fframe]; exact q.choose_spec.2⟩

open Classical in
/-- The lift, extended to `Y13`. -/
def hd (i j : S.ι) (y : Y13o X) : Spin77 := if hy : y ∈ S.W then S.lift i j ⟨y, hy⟩ else 1

lemma σd_val (i : S.ι) (y : S.W) : S.σd i y = S.Φ (S.sec i y) := dif_pos y.2

lemma hd_val (i j : S.ι) (y : S.W) : S.hd i j y = S.lift i j y := dif_pos y.2

/-- **The cocycle of a spin structure.** -/
def toData : SpinLiftData X where
  W := S.W
  isOpen_W := S.isOpen_W
  ι := S.ι
  V := S.V
  isOpen_V := S.isOpen_V
  V_sub := S.V_sub
  cover := S.cover
  σ := S.σd
  cont_σ i := S.continuousOn_of_val i (by
    refine (S.continuous_Φ.comp_continuousOn (S.continuousOn_sec i)).congr fun y _ => S.σd_val i y)
  proj_σ i y hy := by
    have hW := S.V_sub i hy
    have e : S.σd i y = S.Φ (S.sec i ⟨y, hW⟩) := S.σd_val i ⟨y, hW⟩
    rw [e, S.proj_Φ, S.proj_sec i (y := ⟨y, hW⟩) hy]
  h := S.hd
  cont_h i j := by
    intro y hy
    have hW := S.V_sub i hy.1
    have hO : IsOpen (Subtype.val ⁻¹' (S.V i ∩ S.V j) : Set S.W) :=
      ((S.isOpen_V i).inter (S.isOpen_V j)).preimage continuous_subtype_val
    have h0 : ContinuousOn (S.e i) (S.e i).source := (S.e i).toOpenPartialHomeomorph.continuousOn
    have hc : ContinuousOn (fun y : S.W => S.e i (S.sec j y)) (Subtype.val ⁻¹' (S.V i ∩ S.V j)) :=
      ContinuousOn.comp h0 ((S.continuousOn_sec j).mono fun y hy => hy.2) fun y hy =>
        (S.mem_source_iff i _).mpr (by rw [S.proj_sec j hy.2]; exact hy.1)
    have hc2 : ContinuousOn (S.hd i j ∘ Subtype.val : S.W → Spin77)
        (Subtype.val ⁻¹' (S.V i ∩ S.V j)) :=
      (continuous_snd.comp_continuousOn hc).congr fun y _ => S.hd_val i j y
    have hat := hc2.continuousAt (x := ⟨y, hW⟩) (hO.mem_nhds hy)
    exact ((S.isOpen_W.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hat).continuousWithinAt
  lift i j y hy := by
    have hW := S.V_sub i hy.1
    let y' : S.W := ⟨y, hW⟩
    show S.σd j (y' : Y13o X) = actOFr' (S.σd i (y' : Y13o X)) (spinToO77 (S.hd i j (y' : Y13o X)))
    rw [S.σd_val, S.σd_val, S.hd_val, S.sec_eq i j (y := y') hy, S.Φ_act]
  cocycle i j k y hy := by
    have hW := S.V_sub i hy.1.1
    let y' : S.W := ⟨y, hW⟩
    show S.hd i j (y' : Y13o X) * S.hd j k (y' : Y13o X) = S.hd i k (y' : Y13o X)
    rw [S.hd_val, S.hd_val, S.hd_val]
    have h1 := S.sec_eq i k (y := y') ⟨hy.1.1, hy.2⟩
    have h2 := S.sec_eq j k (y := y') ⟨hy.1.2, hy.2⟩
    rw [S.sec_eq i j (y := y') hy.1, S.act_mul] at h2
    have := congrArg (fun q => (S.e i q).2) (h2.symm.trans h1)
    simpa only [S.e_sec_act i (y := y') hy.1.1] using this

end SpinStructure

namespace SpinLiftData

variable (D : SpinLiftData X)

/-- The spin structure glued from a cocycle. -/
def toStructure : SpinStructure X where
  W := D.W
  isOpen_W := D.isOpen_W
  P := D.P
  top := inferInstance
  projS := D.core.proj
  actS := D.actS
  Φ := D.Φ
  act_one := D.actS_one
  act_mul := D.actS_mul
  proj_act := D.proj_actS
  continuous_act := D.continuous_actS₂
  ι := D.ι
  V := D.V
  V_sub := D.V_sub
  cover := D.cover
  e := D.core.localTriv
  baseSet_e _ := rfl
  e_act i p _ t := D.localTriv_actS i p t
  continuous_Φ := D.continuous_Φ
  proj_Φ := D.proj_Φ
  Φ_act := D.Φ_actS

end SpinLiftData

namespace SpinStructure

variable (S : SpinStructure X)

/-- The image of `Φ` in terms of the local frames. -/
lemma range_Φ_eq : Set.range S.Φ = Set.range S.toData.Φ := by
  rw [S.toData.range_Φ]
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨by rw [S.proj_Φ]; exact (S.projS p).2, fun (i : S.ι) hi => ?_⟩
    have hp : (S.projS p : Y13o X) ∈ S.V i := by rw [S.proj_Φ] at hi; exact hi
    refine ⟨spinToO77 (S.e i p).2, spinToO77_mem _, ?_⟩
    rw [S.proj_Φ]
    show S.Φ p = actOFr' (S.σd i (S.projS p : Y13o X)) _
    have e := S.σd_val i (S.projS p)
    rw [e, ← S.Φ_act, S.sec_act_coord i hp]
  · rintro ⟨hW, hq⟩
    obtain ⟨i, hi⟩ := S.cover (projOFr q) hW
    obtain ⟨g, hg, hqg⟩ := hq i hi
    obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨g, hg⟩
    let y : S.W := ⟨projOFr q, hW⟩
    refine ⟨S.actS (S.sec i y) t, ?_⟩
    rw [S.Φ_act, show spinToO77 t = g from congrArg Subtype.val ht, hqg]
    show actOFr' (S.Φ (S.sec i y)) g = actOFr' (S.σd i (y : Y13o X)) g
    rw [S.σd_val]

/-- The chart index of the glued bundle. -/
def idx (y : S.W) : S.ι := S.toData.core.indexAt y

lemma mem_idx (y : S.W) : (y : Y13o X) ∈ S.V (S.idx y) := S.toData.core.mem_baseSet_at y

/-- From the glued bundle to `S`. -/
def glueTo (q : S.toData.P) : S.P :=
  S.actS (S.sec (S.idx q.proj) q.proj) (S.toData.sp q)

/-- From `S` to the glued bundle. -/
def glueFrom (p : S.P) : S.toData.P :=
  ⟨S.projS p, (S.e (S.idx (S.projS p)) p).2⟩

lemma glueTo_chart (i : S.ι) {q : S.toData.P} (hq : ((q.proj : S.W) : Y13o X) ∈ S.V i) :
    S.glueTo q = S.actS (S.sec i q.proj) (S.toData.core.localTriv i q).2 := by
  let y : S.W := q.proj
  set a := S.idx y
  have ha : (y : Y13o X) ∈ S.V a := S.mem_idx y
  show _ = S.actS (S.sec i y) ((S.hd a i (y : Y13o X))⁻¹ * S.toData.sp q)
  rw [S.hd_val, S.sec_eq a i (y := y) ⟨ha, hq⟩, S.act_mul, mul_inv_cancel_left]; rfl

lemma localTriv_glueFrom (i : S.ι) {p : S.P} (hp : (S.projS p : Y13o X) ∈ S.V i) :
    S.toData.core.localTriv i (S.glueFrom p) = S.e i p := by
  set a := S.idx (S.projS p)
  have ha : (S.projS p : Y13o X) ∈ S.V a := S.mem_idx _
  have h1 := S.sec_act_coord i hp
  rw [S.sec_eq a i ⟨ha, hp⟩, S.act_mul] at h1
  have h2 := congrArg (fun r => (S.e a r).2) h1
  simp only [S.e_sec_act a ha] at h2
  refine Prod.ext (S.fst_e i hp).symm ?_
  show (S.hd a i (S.projS p : Y13o X))⁻¹ * (S.e a p).2 = (S.e i p).2
  rw [S.hd_val, ← h2, inv_mul_cancel_left]

lemma continuous_glueTo : Continuous S.glueTo := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  set i := S.idx q.proj
  set t := S.toData.core.localTriv i
  have hq : q ∈ t.source := S.mem_idx q.proj
  have h0 : ContinuousOn t t.source := t.toOpenPartialHomeomorph.continuousOn
  have hF : ContinuousOn (fun z : S.W × Spin77 => S.actS (S.sec i z.1) z.2)
      ((Subtype.val ⁻¹' S.V i) ×ˢ Set.univ) :=
    S.continuous_act.comp_continuousOn
      (((S.continuousOn_sec i).comp continuousOn_fst fun z hz => hz.1).prodMk continuousOn_snd)
  have hc : ContinuousOn S.glueTo t.source := by
    refine (ContinuousOn.comp hF h0 fun r hr => ?_).congr fun r hr => S.glueTo_chart i hr
    exact ⟨(t.coe_fst hr).symm ▸ hr, Set.mem_univ _⟩
  exact hc.continuousAt (t.open_source.mem_nhds hq)

lemma continuous_glueFrom : Continuous S.glueFrom := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
  set t := S.toData.core.localTriv i
  have hps : p ∈ (S.e i).source := (S.mem_source_iff i p).mpr hi
  have h0 : ContinuousOn (S.e i) (S.e i).source := (S.e i).toOpenPartialHomeomorph.continuousOn
  have hc : ContinuousOn S.glueFrom (S.e i).source := by
    have h1 : ContinuousOn (fun r => t.toOpenPartialHomeomorph.symm (S.e i r)) (S.e i).source :=
      ContinuousOn.comp t.toOpenPartialHomeomorph.continuousOn_symm h0 fun r hr => by
        show _ ∈ t.target
        rw [t.target_eq]
        have hr' := (S.mem_source_iff i r).mp hr
        refine ⟨?_, Set.mem_univ _⟩
        show (((S.e i r).1 : S.W) : Y13o X) ∈ S.V i
        rw [S.fst_e i hr']; exact hr'
    refine h1.congr fun r hr => ?_
    have hr' := (S.mem_source_iff i r).mp hr
    have hmem : S.glueFrom r ∈ t.source := hr'
    have := t.left_inv hmem
    have h2 : t.toOpenPartialHomeomorph (S.glueFrom r) = S.e i r := S.localTriv_glueFrom i hr'
    rw [h2] at this
    exact this.symm
  exact hc.continuousAt ((S.e i).open_source.mem_nhds hps)

lemma proj_glueTo (q : S.toData.P) : S.projS (S.glueTo q) = q.proj := by
  unfold glueTo; rw [S.proj_act, S.proj_sec _ (S.mem_idx q.proj)]

/-- **Every spin structure is isomorphic to the one glued from its own cocycle.** -/
def isoToData : SpinIso S.toData.toStructure S where
  F :=
    { toFun := S.glueTo
      invFun := S.glueFrom
      left_inv := fun (q : S.toData.P) => by
        have hp := S.proj_glueTo q
        refine S.toData.ext' hp ?_
        show (S.e (S.idx (S.projS (S.glueTo q))) (S.glueTo q)).2 = S.toData.sp q
        rw [hp]; unfold glueTo
        rw [S.e_sec_act _ (S.mem_idx q.proj)]
      right_inv := fun p => S.sec_act_coord _ (S.mem_idx (S.projS p))
      continuous_toFun := S.continuous_glueTo
      continuous_invFun := S.continuous_glueFrom }
  proj_F q := congrArg Subtype.val (S.proj_glueTo q)
  act_F q t := by
    show S.glueTo (S.toData.actS q t) = S.actS (S.glueTo q) t
    unfold glueTo; rw [S.act_mul]; rfl
  Φ_F := fun (q : S.toData.P) => by
    show S.Φ (S.glueTo q) = S.toData.Φ q
    unfold glueTo; rw [S.Φ_act]
    exact congrArg (fun r => actOFr' r (spinToO77 (S.toData.sp q))) (S.σd_val _ _).symm

/-- **The fibres of `Φ` are the two points `{p, p·(−1)}`.** -/
theorem Φ_eq_iff (p q : S.P) : S.Φ p = S.Φ q ↔ q = p ∨ q = S.actS p negOne := by
  constructor
  · intro hpq
    have hproj : S.projS p = S.projS q :=
      Subtype.ext (by rw [← S.proj_Φ p, ← S.proj_Φ q, hpq])
    obtain ⟨i, hi⟩ := S.cover (S.projS p) (S.projS p).2
    have hq : (S.projS q : Y13o X) ∈ S.V i := hproj ▸ hi
    have hP := S.sec_act_coord i hi
    have hQ := S.sec_act_coord i hq
    rw [← hproj] at hQ
    have e : spinToO77 (S.e i p).2 = spinToO77 (S.e i q).2 := by
      apply actOFr'_cancel (q := S.Φ (S.sec i (S.projS p)))
      rw [← S.Φ_act, ← S.Φ_act, hP, hQ, hpq]
    have e' : spinToO77 ((S.e i p).2⁻¹ * (S.e i q).2) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    rcases (spinToO77_eq_one_iff _).mp e' with h1 | h1
    · left
      rw [inv_mul_eq_one] at h1
      rw [← hQ, ← h1, hP]
    · right
      have h2 : (S.e i q).2 = (S.e i p).2 * negOne := by rw [← h1]; group
      rw [← hQ, h2, ← S.act_mul, hP]
  · rintro (rfl | rfl)
    · rfl
    · rw [S.Φ_act, spinToO77_negOne, actOFr'_one]

/-- The two sheets are distinct. -/
lemma act_negOne_ne (p : S.P) : S.actS p negOne ≠ p := fun h => negOne_ne_one (S.act_free p _ h)

/-- **`Φ` is a covering map onto its image.** -/
theorem isCoveringMap_Φ : IsCoveringMap (Set.rangeFactorization S.Φ) := by
  have hc := S.toData.isCoveringMap_Φ
  let I := S.isoToData
  have h1 := hc.comp_homeomorph I.F.symm
  have h2 := h1.homeomorph_comp (Homeomorph.setCongr S.range_Φ_eq.symm)
  convert h2 using 1
  funext p
  apply Subtype.ext
  show S.Φ p = S.toData.Φ (I.F.symm p)
  have := I.Φ_F (I.F.symm p)
  rw [Homeomorph.apply_symm_apply] at this
  exact this

end SpinStructure

/-- **Cocycle lifts exist iff a spin structure exists** (with the same image in the frames). -/
theorem exists_data_iff_exists_structure (Q : Set (OFr X)) :
    (∃ D : SpinLiftData X, Set.range D.Φ = Q) ↔ ∃ S : SpinStructure X, Set.range S.Φ = Q :=
  ⟨fun ⟨D, hD⟩ => ⟨D.toStructure, hD⟩,
   fun ⟨S, hS⟩ => ⟨S.toData, S.range_Φ_eq.symm.trans hS⟩⟩

/-- **Cocycle lifts exist iff a spin structure exists.** -/
theorem nonempty_data_iff_nonempty_structure :
    Nonempty (SpinLiftData X) ↔ Nonempty (SpinStructure X) :=
  ⟨fun ⟨D⟩ => ⟨D.toStructure⟩, fun ⟨S⟩ => ⟨S.toData⟩⟩

end

end GU.Library
