import GU.Bundle.SO0Reduction

/-!
# Phase 5, item 3: two spin structures on the same frames that are not isomorphic

The first gluing here that is not trivial (the earlier two-chart instance `twoChart` glues trivially,
`twoCharts_iso`). `holeW ⊂ Y13(ℝ⁴)` is the part of the time-gauge locus `{G₀₀ > 0}` lying
over `ℝ⁴` minus the plane `x⁰ = x¹ = 0`. It is open and nonempty, and the loop `holeLoop` around the plane is **not null-homotopic**
(`holeLoop_not_nullhomotopic`, by the angle map to the circle), so `holeW` is not simply connected
(`not_simplyConnected_holeW`). Path-connectedness of `holeW` is not formalised.

Two slit charts `holeV false`, `holeV true` cover it, with one frame `holeσ`. Their overlap is
`{G₀₀ > 0} ∩ {x¹ ≠ 0}` (informally the two half-spaces `x¹ > 0` and `x¹ < 0`). `holeData` is the lift `h = 1`. `holeSign` is the lift equal to `+1`
on `x¹ > 0` and `−1` on `x¹ < 0`. This sign cocycle is **not a coboundary** (`holeSign_not_coboundary`),
since a continuous sign on a chart is constant along an arc of the circle of base points, and so by
`iso_iff_coboundary` the two are **not isomorphic as spin structures** (`not_iso_holeSpin`). The notion
is `SpinIso`: an equivariant homeomorphism over the base commuting with the maps to the frame bundle. As
abstract principal bundles they may be isomorphic (informal, not formalised).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- The base point of a point of `Y13(ℝ⁴)`. -/
def xOf (y : Y13o R4) : R4 := ((y : Yobs R4) : Sym2TX R4).proj

lemma continuous_xOf : Continuous xOf :=
  (FiberBundle.continuous_proj _ _).comp (continuous_subtype_val.comp continuous_subtype_val)

lemma isOpen_timeGaugeLocus : IsOpen timeGaugeLocus := by
  rw [← gaugeW_R4 (pLoop (0 : R4) 0 : HomTotM R4)]
  exact isOpen_gaugeW _

/-- Over `ℝ⁴` a fixed fibre coordinate gives a continuous section. -/
lemma continuous_mkSym (s : Fin 10 → ℝ) :
    Continuous fun x : R4 => (⟨x, s⟩ : Sym2TX R4) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_id.continuousAt, ?_⟩
  have h : ∀ x : R4, ((trivializationAt (Fin 10 → ℝ) (symCore (Zt R4)).Fiber x₀)
      (⟨x, s⟩ : Sym2TX R4)).2 = s := fun x =>
    (symCore (Zt R4)).coordChange_self ((symCore (Zt R4)).indexAt x) x
      ((symCore (Zt R4)).mem_baseSet_at _) s
  simp only [h]
  exact continuousAt_const

/-- The unit circle in the `x⁰x¹`-plane. -/
def xCirc (θ : ℝ) : R4 := ![Real.cos θ, Real.sin θ, 0, 0]

/-- The loop in `Y13(ℝ⁴)` over the circle of base points, with the metric fixed. -/
def ℓ (θ : ℝ) : Y13o R4 := mkY (xCirc θ) 1 isUnit_one

lemma continuous_ℓ : Continuous ℓ := by
  have hx : Continuous xCirc := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [xCirc] <;> fun_prop
  exact (((continuous_mkSym _).comp hx).subtype_mk _).subtype_mk _

lemma xOf_ℓ (θ : ℝ) : xOf (ℓ θ) = xCirc θ := rfl

lemma ℓ_mem_locus (θ : ℝ) : ℓ θ ∈ timeGaugeLocus := by
  show 0 < Gpt (mkY (xCirc θ) 1 isUnit_one : Yobs R4) 0 0
  rw [Gpt_mkY, GU.Iso77.ηR_eq, ηr]
  simp

/-- The time-gauge locus off the plane `x⁰ = x¹ = 0`. -/
def holeW : Set (Y13o R4) := timeGaugeLocus ∩ {y | xOf y 0 ≠ 0 ∨ xOf y 1 ≠ 0}

/-- The two slit charts. -/
def holeV : Bool → Set (Y13o R4)
  | false => timeGaugeLocus ∩ {y | xOf y 1 ≠ 0 ∨ 0 < xOf y 0}
  | true => timeGaugeLocus ∩ {y | xOf y 1 ≠ 0 ∨ xOf y 0 < 0}

lemma continuous_xOf_apply (k : Fin 4) : Continuous fun y => xOf y k :=
  (continuous_apply k).comp continuous_xOf

lemma isOpen_holeW : IsOpen holeW :=
  isOpen_timeGaugeLocus.inter
    ((isOpen_ne_fun (continuous_xOf_apply 0) continuous_const).union
      (isOpen_ne_fun (continuous_xOf_apply 1) continuous_const))

lemma isOpen_holeV (i : Bool) : IsOpen (holeV i) := by
  cases i
  · exact isOpen_timeGaugeLocus.inter ((isOpen_ne_fun (continuous_xOf_apply 1) continuous_const).union
      (isOpen_lt continuous_const (continuous_xOf_apply 0)))
  · exact isOpen_timeGaugeLocus.inter ((isOpen_ne_fun (continuous_xOf_apply 1) continuous_const).union
      (isOpen_lt (continuous_xOf_apply 0) continuous_const))

lemma holeV_sub (i : Bool) : holeV i ⊆ holeW := by
  cases i <;> rintro y ⟨hl, h⟩ <;> refine ⟨hl, ?_⟩ <;> rcases h with h | h
  · exact Or.inr h
  · exact Or.inl (ne_of_gt h)
  · exact Or.inr h
  · exact Or.inl (ne_of_lt h)

lemma holeV_cover (y : Y13o R4) (hy : y ∈ holeW) : ∃ i, y ∈ holeV i := by
  obtain ⟨hl, h⟩ := hy
  by_cases h1 : xOf y 1 ≠ 0
  · exact ⟨false, hl, Or.inl h1⟩
  · have h0 : xOf y 0 ≠ 0 := by simpa [h1] using h
    rcases lt_or_gt_of_ne h0 with h0 | h0
    · exact ⟨true, hl, Or.inr h0⟩
    · exact ⟨false, hl, Or.inr h0⟩

lemma holeV_sub_locus (i : Bool) : holeV i ⊆ timeGaugeLocus := by
  cases i <;> exact fun _ hy => hy.1

/-- The frame over the time-gauge locus. -/
def holeσ : Y13o R4 → OFr R4 := exists_frame_timeGaugeLocus.choose

lemma continuousOn_holeσ : ContinuousOn holeσ timeGaugeLocus :=
  exists_frame_timeGaugeLocus.choose_spec.1

lemma proj_holeσ (y : Y13o R4) (hy : y ∈ timeGaugeLocus) : projOFr (holeσ y) = y :=
  exists_frame_timeGaugeLocus.choose_spec.2 y hy

/-- **The trivial lift**: two slit charts, one frame, `h = 1`. -/
def holeData : SpinLiftData R4 where
  W := holeW
  isOpen_W := isOpen_holeW
  ι := Bool
  V := holeV
  isOpen_V := isOpen_holeV
  V_sub := holeV_sub
  cover := holeV_cover
  σ _ := holeσ
  cont_σ i := continuousOn_holeσ.mono (holeV_sub_locus i)
  proj_σ i y hy := proj_holeσ y (holeV_sub_locus i hy)
  h _ _ _ := 1
  cont_h _ _ := continuousOn_const
  lift _ _ y _ := by simp [actOFr'_one]
  cocycle _ _ _ _ _ := by simp

/-- The sign on the overlap: `+1` on `x¹ > 0`, `−1` otherwise. The value at `x¹ = 0` is off every
overlap and irrelevant. -/
def overlapSign (y : Y13o R4) : Spin77 := if 0 < xOf y 1 then 1 else negOne

/-- **The twisted lift**. -/
def holeSign (i j : Bool) (y : Y13o R4) : Spin77 := if i = j then 1 else overlapSign y

lemma isSign_overlapSign (y : Y13o R4) : IsSign (overlapSign y) := by
  unfold overlapSign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma isSign_holeSign (i j : Bool) (y : Y13o R4) : IsSign (holeSign i j y) := by
  unfold holeSign
  split_ifs
  · exact Or.inl rfl
  · exact isSign_overlapSign y

lemma ne_zero_of_overlap {i j : Bool} (hij : i ≠ j) {y : Y13o R4}
    (hy : y ∈ holeV i ∩ holeV j) : xOf y 1 ≠ 0 := by
  cases i <;> cases j <;> try exact absurd rfl hij
  · obtain ⟨⟨-, hi⟩, ⟨-, hj⟩⟩ := hy
    rcases hi with hi | hi
    · exact hi
    rcases hj with hj | hj
    · exact hj
    exact absurd hi (not_lt.mpr hj.le)
  · obtain ⟨⟨-, hi⟩, ⟨-, hj⟩⟩ := hy
    rcases hi with hi | hi
    · exact hi
    rcases hj with hj | hj
    · exact hj
    exact absurd hi (not_lt.mpr hj.le)

lemma continuousOn_holeSign (i j : Bool) : ContinuousOn (holeSign i j) (holeV i ∩ holeV j) := by
  by_cases hij : i = j
  · have hval : holeSign i j = fun _ => (1 : Spin77) := funext fun y => by simp [holeSign, hij]
    rw [hval]
    exact continuousOn_const
  · have hval : ∀ y, holeSign i j y = overlapSign y := fun y => by simp [holeSign, hij]
    intro y hy
    rw [show holeSign i j = overlapSign from funext hval]
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_gt_of_ne (ne_zero_of_overlap hij hy) with h | h
    · have hev : ∀ᶠ z in 𝓝 y, overlapSign z = negOne := by
        filter_upwards [(continuous_xOf_apply 1).continuousAt.eventually (gt_mem_nhds h)] with z hz
        simp [overlapSign, not_lt.mpr hz.le]
      exact (continuousAt_const.congr (hev.mono fun _ h => h.symm))
    · have hev : ∀ᶠ z in 𝓝 y, overlapSign z = 1 := by
        filter_upwards [(continuous_xOf_apply 1).continuousAt.eventually (lt_mem_nhds h)] with z hz
        simp [overlapSign, hz]
      exact (continuousAt_const.congr (hev.mono fun _ h => h.symm))

lemma holeSign_lift (i j : Bool) (y : Y13o R4) (_ : y ∈ holeV i ∩ holeV j) :
    holeσ y = actOFr' (holeσ y) (spinToO77 (holeSign i j y)) := by
  rw [(isSign_iff _).mp (isSign_holeSign i j y), actOFr'_one]

lemma holeSign_cocycle (i j k : Bool) (y : Y13o R4) :
    holeSign i j y * holeSign j k y = holeSign i k y := by
  have h2 := (isSign_overlapSign y).mul_self
  cases i <;> cases j <;> cases k <;> simp [holeSign, h2]

/-- **The twisted spin structure data**: the same frames, cover and base as `holeData`. -/
def holeSpin : SpinLiftData R4 :=
  holeData.withH holeSign continuousOn_holeSign holeSign_lift
    (fun i j k y _ => holeSign_cocycle i j k y)

/-- A continuous sign on a chart takes the same value at the ends of an arc in that chart. -/
lemma sign_const_of_arc {V : Set (Y13o R4)} {ε : Y13o R4 → Spin77}
    (hs : ∀ y ∈ V, IsSign (ε y)) (hc : ContinuousOn ε V) {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ θ ∈ Set.Icc a b, ℓ θ ∈ V) : ε (ℓ a) = ε (ℓ b) := by
  have hfin : ({1, negOne} : Set Spin77).Finite := Set.toFinite _
  exact isPreconnected_Icc.constant_of_mapsTo (T := ({1, negOne} : Set Spin77)) hfin.isDiscrete
    (hc.comp continuous_ℓ.continuousOn hV)
    (fun θ hθ => by
      rcases hs _ (hV θ hθ) with h | h
      · exact Or.inl h
      · exact Or.inr h)
    ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩

lemma xCirc_0 (θ : ℝ) : xCirc θ 0 = Real.cos θ := rfl
lemma xCirc_1 (θ : ℝ) : xCirc θ 1 = Real.sin θ := rfl

lemma ℓ_mem_false {θ : ℝ} (h : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) : ℓ θ ∈ holeV false := by
  refine ⟨ℓ_mem_locus θ, ?_⟩
  show Real.sin θ ≠ 0 ∨ 0 < Real.cos θ
  by_cases hs : Real.sin θ = 0
  · refine Or.inr ?_
    have hc := Real.cos_nonneg_of_mem_Icc h
    have := Real.sin_sq_add_cos_sq θ
    rw [hs] at this
    nlinarith
  · exact Or.inl hs

lemma ℓ_mem_true {θ : ℝ} (h : θ ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2)) :
    ℓ θ ∈ holeV true := by
  refine ⟨ℓ_mem_locus θ, ?_⟩
  show Real.sin θ ≠ 0 ∨ Real.cos θ < 0
  by_cases hs : Real.sin θ = 0
  · refine Or.inr ?_
    have hc := Real.cos_nonpos_of_pi_div_two_le_of_le h.1 h.2
    have := Real.sin_sq_add_cos_sq θ
    rw [hs] at this
    nlinarith
  · exact Or.inl hs

lemma ℓ_three_halves : ℓ (Real.pi + Real.pi / 2) = ℓ (-(Real.pi / 2)) := by
  have e : Real.pi + Real.pi / 2 = -(Real.pi / 2) + 2 * Real.pi := by ring
  unfold ℓ xCirc
  rw [e, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **The sign cocycle is not a coboundary.** -/
theorem holeSign_not_coboundary (ε : Bool → Y13o R4 → Spin77)
    (hs : ∀ i, ∀ y ∈ holeV i, IsSign (ε i y)) (hc : ∀ i, ContinuousOn (ε i) (holeV i))
    (hrel : ∀ i j, ∀ y ∈ holeV i ∩ holeV j, holeSign i j y = ε i y * holeData.h i j y * ε j y) : False := by
  have hpi2 : 0 < Real.pi / 2 := by positivity
  have mem_f : ℓ (Real.pi / 2) ∈ holeV false := ℓ_mem_false ⟨by linarith, le_refl _⟩
  have mem_t : ℓ (Real.pi / 2) ∈ holeV true := ℓ_mem_true ⟨le_refl _, by linarith [Real.pi_pos]⟩
  have mem_f' : ℓ (-(Real.pi / 2)) ∈ holeV false := ℓ_mem_false ⟨le_refl _, by linarith⟩
  have mem_t' : ℓ (-(Real.pi / 2)) ∈ holeV true := by
    rw [← ℓ_three_halves]
    exact ℓ_mem_true ⟨by linarith [Real.pi_pos], le_refl _⟩
  have ef := sign_const_of_arc (hs false) (hc false) (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (by linarith) fun θ h => ℓ_mem_false h
  have et := sign_const_of_arc (hs true) (hc true) (a := Real.pi / 2) (b := Real.pi + Real.pi / 2)
    (by linarith [Real.pi_pos]) fun θ h => ℓ_mem_true h
  rw [ℓ_three_halves] at et
  have hrel' : ∀ y ∈ holeV false ∩ holeV true, holeSign false true y = ε false y * 1 * ε true y :=
    hrel false true
  have hp := hrel' _ ⟨mem_f, mem_t⟩
  have hm := hrel' _ ⟨mem_f', mem_t'⟩
  have vp : holeSign false true (ℓ (Real.pi / 2)) = 1 := by
    simp [holeSign, overlapSign, xOf_ℓ, xCirc_1]
  have vm : holeSign false true (ℓ (-(Real.pi / 2))) = negOne := by
    simp [holeSign, overlapSign, xOf_ℓ, xCirc_1]
  rw [vp] at hp
  rw [vm, ef, ← et] at hm
  exact negOne_ne_one (hm.trans hp.symm)

/-- **Two spin structures on the same frames over `holeW` that are not isomorphic** (as `SpinIso`). -/
theorem not_iso_holeSpin : IsEmpty (SpinIso holeData.toStructure holeSpin.toStructure) := by
  refine ⟨fun I => ?_⟩
  obtain ⟨ε, hs, hc, hrel⟩ := (SpinLiftData.iso_iff_coboundary holeData holeSign
    continuousOn_holeSign holeSign_lift (fun i j k y _ => holeSign_cocycle i j k y)).mp ⟨I⟩
  exact holeSign_not_coboundary ε hs hc hrel

/-- The base is nonempty. -/
lemma holeW_nonempty : holeW.Nonempty :=
  ⟨ℓ 0, ℓ_mem_locus 0, Or.inl (by simp [xOf_ℓ, xCirc_0])⟩

/-! ### `holeW` is not simply connected -/

section Angle

/-- `x⁰ + i x¹`. -/
def zOf (y : holeW) : ℂ := ⟨xOf y 0, xOf y 1⟩

lemma zOf_ne (y : holeW) : zOf y ≠ 0 := by
  intro h
  have h0 : xOf y 0 = 0 := congrArg Complex.re h
  have h1 : xOf y 1 = 0 := congrArg Complex.im h
  rcases y.2.2 with h' | h'
  · exact h' h0
  · exact h' h1

lemma continuous_zOf : Continuous zOf := by
  have h0 : Continuous fun y : holeW => xOf y 0 := (continuous_xOf_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun y : holeW => xOf y 1 := (continuous_xOf_apply 1).comp continuous_subtype_val
  exact Complex.equivRealProdCLM.symm.continuous.comp (h0.prodMk h1)

/-- The angle map to the circle. -/
def angle (y : holeW) : Circle :=
  ⟨zOf y / ‖zOf y‖, by simp [Submonoid.unitSphere, zOf_ne y]⟩

lemma continuous_angle : Continuous angle :=
  Continuous.subtype_mk (continuous_zOf.div (Complex.continuous_ofReal.comp continuous_zOf.norm)
    fun y => by simpa using zOf_ne y) _

lemma ℓ_mem_holeW (θ : ℝ) : ℓ θ ∈ holeW := by
  refine ⟨ℓ_mem_locus θ, ?_⟩
  by_cases h : Real.cos θ = 0
  · refine Or.inr ?_
    show Real.sin θ ≠ 0
    intro hs
    have := Real.sin_sq_add_cos_sq θ
    rw [h, hs] at this
    norm_num at this
  · exact Or.inl h

lemma angle_ℓ (θ : ℝ) : angle ⟨ℓ θ, ℓ_mem_holeW θ⟩ = Circle.exp θ := by
  have hz : zOf ⟨ℓ θ, ℓ_mem_holeW θ⟩ = Complex.exp (θ * Complex.I) := by
    rw [Complex.exp_mul_I]
    refine Complex.ext ?_ ?_
    · simp [zOf, xOf_ℓ, xCirc_0, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · simp [zOf, xOf_ℓ, xCirc_1, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Subtype.ext
  show zOf _ / ‖zOf _‖ = _
  rw [hz, Complex.norm_exp_ofReal_mul_I]
  simp [Circle.coe_exp]

lemma ℓ_two_pi : ℓ (2 * Real.pi) = ℓ 0 := by
  unfold ℓ xCirc
  simp

/-- The base point of the loop. -/
def holeBase : holeW := ⟨ℓ 0, ℓ_mem_holeW 0⟩

/-- The loop around the plane, with the metric fixed. -/
def holeLoop : Path holeBase holeBase where
  toFun t := ⟨ℓ (2 * Real.pi * t), ℓ_mem_holeW _⟩
  continuous_toFun := (continuous_ℓ.comp (continuous_const.mul continuous_subtype_val)).subtype_mk _
  source' := by apply Subtype.ext; simp [holeBase]
  target' := by apply Subtype.ext; simpa [holeBase] using ℓ_two_pi

/-- **The loop around the plane is not null-homotopic in `holeW`.** -/
theorem holeLoop_not_nullhomotopic : ¬ Path.Homotopic holeLoop (Path.refl holeBase) := by
  intro hhom
  let A : C(holeW, Circle) := ⟨angle, continuous_angle⟩
  obtain ⟨H⟩ := hhom.map A
  let γ₀ : C(unitInterval, Circle) := (holeLoop.map A.continuous).toContinuousMap
  let γ₁ : C(unitInterval, Circle) := ((Path.refl holeBase).map A.continuous).toContinuousMap
  have hrel : γ₀.HomotopicRel γ₁ {0, 1} := ⟨H⟩
  have h1 : γ₀ 0 = Circle.exp (0 : ℝ) := by
    show angle (holeLoop 0) = _
    rw [holeLoop.source]; exact angle_ℓ 0
  have h2 : γ₁ 0 = Circle.exp (0 : ℝ) := by
    show angle holeBase = _
    exact angle_ℓ 0
  have hend := Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel hrel 0 h1 h2
  let Γ₀ : C(unitInterval, ℝ) := ⟨fun t => 2 * Real.pi * t, continuous_const.mul continuous_subtype_val⟩
  let Γ₁ : C(unitInterval, ℝ) := ContinuousMap.const _ 0
  have e₀ : Γ₀ = Circle.isCoveringMap_exp.liftPath γ₀ 0 h1 := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, by simp [Γ₀]⟩
    exact (angle_ℓ (2 * Real.pi * t)).symm
  have e₁ : Γ₁ = Circle.isCoveringMap_exp.liftPath γ₁ 0 h2 := by
    refine (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, rfl⟩
    exact (angle_ℓ 0).symm
  rw [← e₀, ← e₁] at hend
  have : (2 * Real.pi * ((1 : unitInterval) : ℝ)) = 0 := hend
  simp at this

/-- **`holeW` is not simply connected.** -/
theorem not_simplyConnected_holeW : ¬ SimplyConnectedSpace holeW := fun _ =>
  holeLoop_not_nullhomotopic (SimplyConnectedSpace.paths_homotopic _ _)

end Angle

end

end GU.Library
