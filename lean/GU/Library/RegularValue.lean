import GU.Library.LevelOpen

/-!
# L4f: the regular value theorem on manifold domains

`M` is a smooth manifold modelled on `E` (no boundary), `f : M → F`. Assume that in every chart,
`f ∘ φ⁻¹` is `C^∞` on the chart target and submersive at the level points (`RegularLevel`). Then
`f⁻¹{c}` is a smooth manifold of dimension `dim E − dim F` (**`isManifold_regularLevel`**). The
charts are `φ` restricted to the level set (`levelRestr`), followed by the open-set level-set charts
of `f ∘ φ⁻¹` (`LevelOpen.lean`). Transitions are smooth because the chart changes of `M` are.
The topology is the subspace topology of `M`.

`[Nontrivial F]` is only used to extend `f ∘ φ⁻¹` by a value `≠ c` off the chart target; if
`F = 0`, the level set is `M` itself. Not yet proved: `RegularLevel` from the textbook hypothesis
(`f` is `C^∞` with `mfderiv` onto along `f⁻¹{c}`), and smoothness of the inclusion into `M` is `contMDiff_regularLevel_val`.
Not in the pinned Mathlib: `Geometry/Manifold/Submersion.lean` lists the preimage theorem as TODO.
-/

namespace GU.Library

open scoped ContDiff Manifold Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

lemma chartTrans_contDiffOn (a b : M) :
    ContDiffOn ℝ ∞ ((chartAt E a).symm.trans (chartAt E b))
      ((chartAt E a).symm.trans (chartAt E b)).source := by
  have h := (HasGroupoid.compatible (G := contDiffGroupoid ∞ 𝓘(ℝ, E))
    (chart_mem_atlas E a) (chart_mem_atlas E b)).1
  simpa [contDiffPregroupoid, Function.comp_def] using h

section Restr

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Classical in
/-- Restriction of `φ` to subsets `S → T` it maps into each other (junk off the domain). -/
noncomputable def levelRestr (φ : OpenPartialHomeomorph X Y) (S : Set X) (T : Set Y)
    (hST : ∀ x ∈ S, x ∈ φ.source → φ x ∈ T) (hTS : ∀ y ∈ T, y ∈ φ.target → φ.symm y ∈ S)
    (s0 : S) (t0 : T) : OpenPartialHomeomorph S T where
  toFun x := if h : (x : X) ∈ φ.source then ⟨φ x, hST x x.2 h⟩ else t0
  invFun y := if h : (y : Y) ∈ φ.target then ⟨φ.symm y, hTS y y.2 h⟩ else s0
  source := {x | (x : X) ∈ φ.source}
  target := {y | (y : Y) ∈ φ.target}
  map_source' x hx := by
    rw [Set.mem_setOf_eq, dif_pos (show (x : X) ∈ φ.source from hx)]; exact φ.map_source hx
  map_target' y hy := by
    rw [Set.mem_setOf_eq, dif_pos (show (y : Y) ∈ φ.target from hy)]; exact φ.map_target hy
  left_inv' x hx := by
    have hx' : (x : X) ∈ φ.source := hx
    apply Subtype.ext
    simp only [dif_pos hx', dif_pos (φ.map_source hx')]
    exact φ.left_inv hx'
  right_inv' y hy := by
    have hy' : (y : Y) ∈ φ.target := hy
    apply Subtype.ext
    simp only [dif_pos hy', dif_pos (φ.map_target hy')]
    exact φ.right_inv hy'
  open_source := φ.open_source.preimage continuous_subtype_val
  open_target := φ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (φ.continuousOn.comp continuous_subtype_val.continuousOn fun _ h => h).congr
      fun x hx => ?_
    simp only [Function.comp_apply, dif_pos (show (x : X) ∈ φ.source from hx)]
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (φ.continuousOn_symm.comp continuous_subtype_val.continuousOn fun _ h => h).congr
      fun y hy => ?_
    simp only [Function.comp_apply, dif_pos (show (y : Y) ∈ φ.target from hy)]

lemma levelRestr_val {φ : OpenPartialHomeomorph X Y} {S : Set X} {T : Set Y} {hST hTS s0 t0}
    {x : S} (hx : (x : X) ∈ φ.source) :
    ((levelRestr φ S T hST hTS s0 t0 x : T) : Y) = φ x := by
  classical
  simp [levelRestr, hx]

lemma levelRestr_symm_val {φ : OpenPartialHomeomorph X Y} {S : Set X} {T : Set Y} {hST hTS s0 t0}
    {y : T} (hy : (y : Y) ∈ φ.target) :
    (((levelRestr φ S T hST hTS s0 t0).symm y : S) : X) = φ.symm y := by
  classical
  simp [levelRestr, hy]

end Restr

section Regular

variable [Nontrivial F] {f : M → F} {c : F}

variable (E) in
/-- `f⁻¹{c}` is a regular level set: in every chart `f ∘ φ⁻¹` is smooth on the chart target and
submersive at the level points. -/
structure RegularLevel (f : M → F) (c : F) : Prop where
  smooth : ∀ a : M, ContDiffOn ℝ ∞ (f ∘ (chartAt E a).symm) (chartAt E a).target
  surj : ∀ a x, x ∈ (chartAt E a).source → f x = c →
    (fderiv ℝ (f ∘ (chartAt E a).symm) (chartAt E a x)).range = ⊤

/-- A value different from `c`. -/
noncomputable def dval (c : F) : F := (exists_ne c).choose

lemma dval_ne (c : F) : dval c ≠ c := (exists_ne c).choose_spec

open Classical in
/-- `f` in the chart at `a`, extended by `dval c` off the chart target. -/
noncomputable def gch (f : M → F) (c : F) (a : M) : E → F :=
  fun e => if e ∈ (chartAt E a).target then (f ∘ (chartAt E a).symm) e else dval c

lemma gch_sub (h : RegularLevel E f c) (a : M) :
    SmoothSubmersiveOn (gch (E := E) f c a) c (chartAt E a).target := by
  classical
  refine smoothSubmersiveOn_extend (chartAt E a).open_target (h.smooth a) (fun e he hfe => ?_)
    (dval c) (dval_ne c)
  have hx : (chartAt E a).symm e ∈ (chartAt E a).source := (chartAt E a).map_target he
  have := h.surj a _ hx hfe
  rwa [(chartAt E a).right_inv he] at this

lemma mem_level_gch_iff (a : M) (e : E) :
    e ∈ levelSet (gch (E := E) f c a) c ↔ e ∈ (chartAt E a).target ∧ f ((chartAt E a).symm e) = c := by
  classical
  exact mem_levelSet_extend_iff (U := (chartAt E a).target) (f := f ∘ (chartAt E a).symm)
    (dval c) (dval_ne c) e

lemma levelST (a : M) (x : M) (hx : x ∈ levelSet f c) (hs : x ∈ (chartAt E a).source) :
    chartAt E a x ∈ levelSet (gch (E := E) f c a) c :=
  (mem_level_gch_iff a _).mpr ⟨(chartAt E a).map_source hs, by rw [(chartAt E a).left_inv hs]; exact hx⟩

lemma levelTS (a : M) (e : E) (he : e ∈ levelSet (gch (E := E) f c a) c) (_ : e ∈ (chartAt E a).target) :
    (chartAt E a).symm e ∈ levelSet f c :=
  ((mem_level_gch_iff a e).mp he).2

variable (E) in
/-- The base point `φₐ(a)` of the chart-level level set. -/
noncomputable def basePt (a : levelSet f c) : levelSet (gch (E := E) f c (a : M)) c :=
  ⟨chartAt E (a : M) a, levelST _ _ a.2 (mem_chart_source E _)⟩

variable (E) in
/-- `φₐ` restricted to the level sets. -/
noncomputable def restrA (a : levelSet f c) :
    OpenPartialHomeomorph (levelSet f c) (levelSet (gch (E := E) f c (a : M)) c) :=
  levelRestr (chartAt E (a : M)) _ _ (levelST (E := E) (a : M)) (levelTS (E := E) (a : M)) a (basePt E a)

/-- **The chart at `a`** of the regular level set. -/
noncomputable def regChart (h : RegularLevel E f c) (a : levelSet f c) :
    OpenPartialHomeomorph (levelSet f c) (Fin (fibreDim E F) → ℝ) :=
  (restrA E a).trans (smoothLevelChartOn (gch_sub h (a : M)) (basePt E a))

lemma restrA_self (a : levelSet f c) : restrA E a a = basePt E a :=
  Subtype.ext (levelRestr_val (mem_chart_source E (a : M)))

/-- **Charted structure** on a regular level set. -/
@[instance_reducible] noncomputable def regCharted (h : RegularLevel E f c) :
    ChartedSpace (Fin (fibreDim E F) → ℝ) (levelSet f c) where
  atlas := Set.range (regChart h)
  chartAt := regChart h
  mem_chart_source a := by
    rw [regChart, OpenPartialHomeomorph.trans_source]
    refine ⟨mem_chart_source E (a : M), ?_⟩
    show restrA E a a ∈ (smoothLevelChartOn (gch_sub h (a : M)) (basePt E a)).source
    rw [restrA_self]
    exact (smoothLevelChartedOn (gch_sub h (a : M))).mem_chart_source (basePt E a)
  chart_mem_atlas a := ⟨a, rfl⟩

end Regular

section RegularManifold

variable [Nontrivial F] {f : M → F} {c : F}

/-- The transition formula between regular-level charts. -/
noncomputable def regTrans (h : RegularLevel E f c) (a b : levelSet f c) :
    (Fin (fibreDim E F) → ℝ) → (Fin (fibreDim E F) → ℝ) := fun v =>
  kerEquiv ((gch_sub h (b : M)).surj _ (basePt E b).2)
    (kerProj (fderiv ℝ (gch (E := E) f c (b : M)) (basePt E b))
      ((chartAt E (b : M)) ((chartAt E (a : M)).symm
        ((smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) (gch_sub h (a : M)).isOpen
          (gch_sub h (a : M)).smooth ((gch_sub h (a : M)).sub _ (basePt E a).2)
          ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm
          (c, (kerEquiv ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm v))) -
        ((basePt E b : levelSet _ c) : E)))

lemma regTrans_eq (h : RegularLevel E f c) (a b : levelSet f c) {v : Fin (fibreDim E F) → ℝ}
    (hv : v ∈ ((regChart h a).symm.trans (regChart h b)).source) :
    ((regChart h a).symm.trans (regChart h b)) v = regTrans h a b v := by
  set La := smoothLevelChartOn (gch_sub h (a : M)) (basePt E a)
  set Lb := smoothLevelChartOn (gch_sub h (b : M)) (basePt E b)
  have hea : regChart h a = (restrA E a).trans La := rfl
  have heb : regChart h b = (restrA E b).trans Lb := rfl
  rw [hea, heb] at hv ⊢
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_target] at hv
  obtain ⟨⟨hvL, hvR⟩, hv2⟩ := hv
  rw [Set.mem_preimage, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, OpenPartialHomeomorph.trans_source] at hv2
  have ht : ((La.symm v : levelSet _ c) : E) ∈ (chartAt E (a : M)).target := hvR
  have hxb : (((restrA E a).symm (La.symm v) : levelSet f c) : M) ∈ (chartAt E (b : M)).source :=
    hv2.1
  rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans]
  simp only [Function.comp_apply]
  show kerEquiv _ (kerProj _ ((((restrA E b) ((restrA E a).symm (La.symm v)) : levelSet _ c) : E) -
    ((basePt E b : levelSet _ c) : E))) = _
  rw [restrA, levelRestr_val hxb, restrA, levelRestr_symm_val ht,
    smoothLevelChartOn_symm_val (gch_sub h (a : M)) (basePt E a) hvL]
  rfl

/-- **The regular value theorem**: a regular level set of a map on a smooth manifold is a smooth
manifold of dimension `dim E − dim F`. -/
theorem isManifold_regularLevel (h : RegularLevel E f c) :
    letI := regCharted h
    IsManifold 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ (levelSet f c) := by
  let _ := regCharted h
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ]
  intro v hv
  -- the pieces of the formula
  set ha := gch_sub h (a : M)
  set La := smoothLevelChartOn ha (basePt E a)
  set Ka := kerEquiv (ha.surj _ (basePt E a).2)
  set Ψa := smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) ha.isOpen ha.smooth
    (ha.sub _ (basePt E a).2) (ha.surj _ (basePt E a).2)
  have hv' := hv
  have hea : regChart h a = (restrA E a).trans La := rfl
  rw [hea, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_target] at hv'
  obtain ⟨⟨hvL, hvR⟩, hv2⟩ := hv'
  have hw := mem_smoothChartOn_target_of ha (basePt E a) hvL
  have hwval : ((La.symm v : levelSet _ c) : E) = Ψa.symm (c, Ka.symm v) :=
    smoothLevelChartOn_symm_val ha (basePt E a) hvL
  have ht : Ψa.symm (c, Ka.symm v) ∈ (chartAt E (a : M)).target := hwval ▸ hvR
  have hxb : (chartAt E (a : M)).symm (Ψa.symm (c, Ka.symm v)) ∈ (chartAt E (b : M)).source := by
    have heb : regChart h b = (restrA E b).trans (smoothLevelChartOn (gch_sub h (b : M)) (basePt E b)) := rfl
    rw [heb, Set.mem_preimage, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, OpenPartialHomeomorph.trans_source] at hv2
    have this : (((restrA E a).symm (La.symm v) : levelSet f c) : M) ∈ (chartAt E (b : M)).source :=
      hv2.1
    have hr : (((restrA E a).symm (La.symm v) : levelSet f c) : M) =
        (chartAt E (a : M)).symm (La.symm v : E) := levelRestr_symm_val hvR
    rw [hr, hwval] at this
    exact this
  have hG : ContDiffAt ℝ ∞ (regTrans h a b) v := by
    have h1 : ContDiffAt ℝ ∞ (fun v => (c, Ka.symm v)) v :=
      (contDiff_const.prodMk Ka.symm.contDiff).contDiffAt
    have h2 := (contDiffAt_smoothChartOn_symm ha.isOpen ha.smooth (ha.sub _ (basePt E a).2)
      (ha.surj _ (basePt E a).2) hw).comp v h1
    have hsrc : Ψa.symm (c, Ka.symm v) ∈
        ((chartAt E (a : M)).symm.trans (chartAt E (b : M))).source := ⟨ht, hxb⟩
    have h3 := ((chartTrans_contDiffOn (a : M) (b : M)).contDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hsrc)).comp v h2
    have h4 : ContDiff ℝ ∞ (fun z : E =>
        kerEquiv ((gch_sub h (b : M)).surj _ (basePt E b).2)
          (kerProj (fderiv ℝ (gch (E := E) f c (b : M)) (basePt E b))
            (z - ((basePt E b : levelSet _ c) : E)))) :=
      ((kerEquiv ((gch_sub h (b : M)).surj _ (basePt E b).2)).contDiff.comp
        ((kerProj (fderiv ℝ (gch (E := E) f c (b : M)) (basePt E b))).contDiff.comp
          (contDiff_id.sub contDiff_const)) :)
    exact h4.contDiffAt.comp v h3
  refine hG.contDiffWithinAt.congr (fun w hw' => regTrans_eq h a b hw') (regTrans_eq h a b hv)

/-- The value in `M` of the inverse regular chart. -/
lemma regChart_symm_val (h : RegularLevel E f c) (a : levelSet f c) {v : Fin (fibreDim E F) → ℝ}
    (hv : v ∈ (regChart h a).target) :
    (((regChart h a).symm v : levelSet f c) : M) =
      (chartAt E (a : M)).symm
        ((smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) (gch_sub h (a : M)).isOpen
          (gch_sub h (a : M)).smooth ((gch_sub h (a : M)).sub _ (basePt E a).2)
          ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm
          (c, (kerEquiv ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm v)) := by
  set La := smoothLevelChartOn (gch_sub h (a : M)) (basePt E a)
  have hea : regChart h a = (restrA E a).trans La := rfl
  rw [hea, OpenPartialHomeomorph.trans_target] at hv
  obtain ⟨hvL, hvR⟩ := hv
  rw [hea, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
    Function.comp_apply]
  rw [show (((restrA E a).symm (La.symm v) : levelSet f c) : M) =
      (chartAt E (a : M)).symm (La.symm v : E) from levelRestr_symm_val hvR,
    smoothLevelChartOn_symm_val (gch_sub h (a : M)) (basePt E a) hvL]

lemma regChart_target_chart (h : RegularLevel E f c) (a : levelSet f c) {v : Fin (fibreDim E F) → ℝ}
    (hv : v ∈ (regChart h a).target) :
    (smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) (gch_sub h (a : M)).isOpen
      (gch_sub h (a : M)).smooth ((gch_sub h (a : M)).sub _ (basePt E a).2)
      ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm
      (c, (kerEquiv ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm v) ∈
        (chartAt E (a : M)).target ∧
      (c, (kerEquiv ((gch_sub h (a : M)).surj _ (basePt E a).2)).symm v) ∈
        (smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) (gch_sub h (a : M)).isOpen
          (gch_sub h (a : M)).smooth ((gch_sub h (a : M)).sub _ (basePt E a).2)
          ((gch_sub h (a : M)).surj _ (basePt E a).2)).target := by
  set La := smoothLevelChartOn (gch_sub h (a : M)) (basePt E a)
  have hea : regChart h a = (restrA E a).trans La := rfl
  rw [hea, OpenPartialHomeomorph.trans_target] at hv
  obtain ⟨hvL, hvR⟩ := hv
  refine ⟨?_, mem_smoothChartOn_target_of _ _ hvL⟩
  have ht : ((La.symm v : levelSet _ c) : E) ∈ (chartAt E (a : M)).target := hvR
  rwa [smoothLevelChartOn_symm_val (gch_sub h (a : M)) (basePt E a) hvL] at ht

/-- **The inclusion of a regular level set is smooth**: it is a submanifold of `M`. -/
theorem contMDiff_regularLevel_val (h : RegularLevel E f c) :
    letI := regCharted h
    haveI := isManifold_regularLevel h
    ContMDiff 𝓘(ℝ, Fin (fibreDim E F) → ℝ) 𝓘(ℝ, E) ∞ (Subtype.val : levelSet f c → M) := by
  let _ := regCharted h
  have _ := isManifold_regularLevel h
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun a y => ?_⟩
  intro v hv
  have hvt : v ∈ (regChart h a).target := by
    have : v ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hv.1
    exact this
  have hvy : (((regChart h a).symm v : levelSet f c) : M) ∈ (chartAt E y).source := by
    have : (((chartAt (Fin (fibreDim E F) → ℝ) a).symm v : levelSet f c) : M) ∈ (chartAt E y).source := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hv.2
    exact this
  obtain ⟨ht, htgt⟩ := regChart_target_chart h a hvt
  set ha := gch_sub h (a : M)
  set Ψa := smoothChartOn (a := ((basePt E a : levelSet _ c) : E)) ha.isOpen ha.smooth
    (ha.sub _ (basePt E a).2) (ha.surj _ (basePt E a).2)
  set Ka := kerEquiv (ha.surj _ (basePt E a).2)
  have hsrc : Ψa.symm (c, Ka.symm v) ∈ ((chartAt E (a : M)).symm.trans (chartAt E y)).source :=
    ⟨ht, by
      show (chartAt E (a : M)).symm (Ψa.symm (c, Ka.symm v)) ∈ (chartAt E y).source
      rw [← regChart_symm_val h a hvt]; exact hvy⟩
  have hG : ContDiffAt ℝ ∞
      (fun v => ((chartAt E (a : M)).symm.trans (chartAt E y)) (Ψa.symm (c, Ka.symm v))) v :=
    ((chartTrans_contDiffOn (a : M) y).contDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hsrc)).comp v
      ((contDiffAt_smoothChartOn_symm ha.isOpen ha.smooth (ha.sub _ (basePt E a).2)
        (ha.surj _ (basePt E a).2) htgt).comp v
        (contDiff_const.prodMk Ka.symm.contDiff).contDiffAt)
  refine hG.contDiffWithinAt.congr (fun w hw => ?_) ?_
  · have hwt : w ∈ (regChart h a).target := by
      have : w ∈ (chartAt (Fin (fibreDim E F) → ℝ) a).target := by
        simpa [extChartAt, OpenPartialHomeomorph.extend] using hw.1
      exact this
    show chartAt E y (((regChart h a).symm w : levelSet f c) : M) = _
    rw [regChart_symm_val h a hwt]; rfl
  · show chartAt E y (((regChart h a).symm v : levelSet f c) : M) = _
    rw [regChart_symm_val h a hvt]; rfl

/-- The regular chart in formulas. -/
lemma regChart_apply (h : RegularLevel E f c) (a s : levelSet f c)
    (hs : (s : M) ∈ (chartAt E (a : M)).source) :
    regChart h a s = kerEquiv ((gch_sub h (a : M)).surj _ (basePt E a).2)
      (kerProj (fderiv ℝ (gch (E := E) f c (a : M)) (basePt E a))
        (chartAt E (a : M) s - chartAt E (a : M) a)) := by
  have hea : regChart h a = (restrA E a).trans (smoothLevelChartOn (gch_sub h (a : M)) (basePt E a)) := rfl
  rw [hea, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  show kerEquiv _ (kerProj _ ((((restrA E a) s : levelSet _ c) : E) - ((basePt E a : levelSet _ c) : E))) = _
  rw [restrA, levelRestr_val hs]; rfl

section Universal

variable {EM HM N : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  [TopologicalSpace N] [ChartedSpace HM N] {I : ModelWithCorners ℝ EM HM} [IsManifold I ∞ N]

/-- **Universal property**: a map into a regular level set is smooth iff it is smooth into `M`. -/
theorem contMDiff_regularLevel_iff (h : RegularLevel E f c) {g : N → levelSet f c} :
    letI := regCharted h
    haveI := isManifold_regularLevel h
    ContMDiff I 𝓘(ℝ, Fin (fibreDim E F) → ℝ) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (fun x => (g x : M)) := by
  let _ := regCharted h
  have _ := isManifold_regularLevel h
  refine ⟨fun hg => (contMDiff_regularLevel_val h).comp hg, fun hg => ?_⟩
  rw [contMDiff_iff] at hg ⊢
  refine ⟨Topology.IsInducing.subtypeVal.continuous_iff.mpr hg.1, fun x y => ?_⟩
  have hx := hg.2 x (y : M)
  have hL : ContDiff ℝ ∞ (fun z : E => kerEquiv ((gch_sub h (y : M)).surj _ (basePt E y).2)
      (kerProj (fderiv ℝ (gch (E := E) f c (y : M)) (basePt E y)) (z - chartAt E (y : M) y))) :=
    ((kerEquiv ((gch_sub h (y : M)).surj _ (basePt E y).2)).contDiff.comp
      ((kerProj (fderiv ℝ (gch (E := E) f c (y : M)) (basePt E y))).contDiff.comp
        (contDiff_id.sub contDiff_const)) :)
  refine (hL.comp_contDiffOn (hx.mono ?_)).congr fun w hw => ?_
  · intro w hw
    refine ⟨hw.1, ?_⟩
    have := hw.2
    simp only [Set.mem_preimage, extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_source,
      Set.mem_inter_iff, modelWithCornersSelf_partialEquiv, PartialEquiv.refl_source, Set.mem_univ,
      and_true, OpenPartialHomeomorph.toFun_eq_coe] at this ⊢
    have h2 : (g ((extChartAt I x).symm w) : M) ∈ (chartAt E (y : M)).source := by
      have : g ((extChartAt I x).symm w) ∈ (chartAt (Fin (fibreDim E F) → ℝ) y).source := this
      exact this.1
    exact h2
  · have hw2 := hw.2
    have hsrc : g ((extChartAt I x).symm w) ∈ (chartAt (Fin (fibreDim E F) → ℝ) y).source := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hw2
    have h2 : (g ((extChartAt I x).symm w) : M) ∈ (chartAt E (y : M)).source := hsrc.1
    show regChart h y (g ((extChartAt I x).symm w)) = _
    rw [regChart_apply h y _ h2]
    rfl

end Universal

end RegularManifold

end GU.Library
