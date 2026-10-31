import GU.Observerse.ChimericBundle
import GU.Bundle.Principal

/-!
# The GL(14) frame bundle of `C` as a genuine smooth manifold

Over the global smooth `Y`, with tangent transitions `T_ij` of `X` (`T_ij = (Zt X).coordChange i j`,
chart-`i` coordinates → chart-`j` coordinates):
* `gX i j x = symAct(T_ij) × (p ↦ p ∘ T_ji)`: the transitions of `C = Sym²(TX) ⊕ T*X`
  (`gX_self`, `gX_comp`: identity and cocycle);
* `frameCore`: the vector bundle core over `Y` with fiber `End(ℝ¹⁴)` and transitions `A ↦ g_ij ∘ A`
  (the bundle `Hom(Y × ℝ¹⁴, C)`). It is smooth (`frameCore_isContMDiff`);
* `FrY`: the frames, the open set of invertible elements (`isOpen_frames`). **`frames_isManifold`**:
  the frame bundle is a smooth manifold modelled on `ℝ¹⁴ × End(ℝ¹⁴)` (dimension 14 + 196,
  `finrank_EndC`). That theorem is an instance lookup (any open subset of a manifold is one); the
  content is `frameCore_isContMDiff` and `isOpen_frames`.

CAVEATS. `frameCore` is built from the cocycle `gX` directly. `FramesCb.lean` shows that the
bundle `Cb` of `ChimericBundle.lean` has the same transition cocycle (`Cb_coordChange`) and that
`frameCore`'s trivialisations are fibrewise post-composition with `Cb`'s (`frameCore_localTriv_eq`);
a bundle isomorphism with Mathlib's hom bundle `Hom(Y × ℝ¹⁴, Cb)` is not constructed. The right
action `A ↦ A ∘ g` is free and fibre-transitive (`frYBundle`, a set-level `GU.PrincipalBundle`), and
the local trivialisations are equivariant and carry frames onto `U_i × GL(14)` (`localTriv_ract`,
`localTriv_frames`). Smoothness is proved jointly in `(A, g)` on the ambient `Hom(ℝ¹⁴, C) × End(ℝ¹⁴)`
(`contMDiff_ract_joint`) and, restricted, on `FrY × GL(14)` with `GL(14)` the Lie group of units
(`contMDiff_smul_FrY`). The comparison with the set-level `frameBundle` is not formalised.

This replaces the set-level product of `FrameBundle.lean` with a topological and smooth object.
(Orthonormal frames: a closed, chart-invariant subset, `SmoothOrtho.lean`; not shown to be a
submanifold. Over (3,1) points of `Y` the chimeric metric is not isometric to the (7,7) model (orthogonal basis
with 9 positive norms; convention `+DeWitt ⊕ +g⁻¹` of `Chimeric.lean`), so there the fibres are
empty (`no_ortho_31`) and the O(7,7) reduction can only live over the (1,3) part.)
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

abbrev E4 := Fin 4 → ℝ

-- Shortcut instances (local): without them instance search for `EndC` exceeds the heartbeat budget.
local instance : SequentialSpace CFib := inferInstance
/-- `End(ℝ¹⁴)`. -/
abbrev EndC := CFib →L[ℝ] CFib
noncomputable local instance : NormedAddCommGroup EndC := inferInstance
noncomputable local instance : NormedSpace ℝ EndC := inferInstance
local instance : CompleteSpace EndC := ContinuousLinearMap.instCompleteSpace

lemma finrank_EndC : Module.finrank ℝ EndC = 196 := by
  have hd : Module.finrank ℝ ((Fin 4 → ℝ) →L[ℝ] ℝ) = 4 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin 4 → ℝ) (F' := ℝ)).finrank_eq]
    simp
  have hC : Module.finrank ℝ CFib = 14 := by rw [Module.finrank_prod, hd]; simp
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := CFib) (F' := CFib)).finrank_eq,
    Module.finrank_linearMap, hC]

/-- Covector transport `p ↦ p ∘ T`. -/
noncomputable def covT (T : E4 →L[ℝ] E4) : (E4 →L[ℝ] ℝ) →L[ℝ] (E4 →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E4 E4 ℝ).flip T

/-- Transition of `C` at `x` between charts `i, j`. -/
noncomputable def gX (i j : atlas (Fin 4 → ℝ) X) (x : X) : CFib →L[ℝ] CFib :=
  ContinuousLinearMap.prodMap (symAct ((Zt X).coordChange i j x)) (covT ((Zt X).coordChange j i x))

lemma gX_self (i : atlas (Fin 4 → ℝ) X) (x : X) (hx : x ∈ (Zt X).baseSet i) (v : CFib) :
    gX i i x v = v := by
  have hT : (Zt X).coordChange i i x = ContinuousLinearMap.id ℝ _ :=
    ContinuousLinearMap.ext fun w => (Zt X).coordChange_self i x hx w
  change (symAct ((Zt X).coordChange i i x) v.1, covT ((Zt X).coordChange i i x) v.2) = v
  rw [hT]
  refine Prod.ext (symAct_id v.1) ?_
  ext w; rfl

lemma gX_comp (i j k : atlas (Fin 4 → ℝ) X) (x : X)
    (hx : x ∈ (Zt X).baseSet i ∩ (Zt X).baseSet j ∩ (Zt X).baseSet k) (v : CFib) :
    gX j k x (gX i j x v) = gX i k x v := by
  have hV : ((Zt X).coordChange j k x).comp ((Zt X).coordChange i j x) = (Zt X).coordChange i k x :=
    ContinuousLinearMap.ext fun w => (Zt X).coordChange_comp i j k x hx w
  have hx' : x ∈ (Zt X).baseSet k ∩ (Zt X).baseSet j ∩ (Zt X).baseSet i :=
    ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩
  change (symAct ((Zt X).coordChange j k x) (symAct ((Zt X).coordChange i j x) v.1),
      covT ((Zt X).coordChange k j x) (covT ((Zt X).coordChange j i x) v.2))
    = (symAct ((Zt X).coordChange i k x) v.1, covT ((Zt X).coordChange k i x) v.2)
  refine Prod.ext ?_ ?_
  · show symAct _ (symAct _ v.1) = _
    rw [symAct_comp, hV]
  · ext w
    show v.2 ((Zt X).coordChange j i x ((Zt X).coordChange k j x w)) = v.2 ((Zt X).coordChange k i x w)
    rw [(Zt X).coordChange_comp k j i x hx' w]

lemma covT_contDiff : ContDiff ℝ ∞ (fun T : E4 →L[ℝ] E4 => covT T) := by
  rw [contDiff_clm_apply_iff]
  intro p
  rw [contDiff_clm_apply_iff]
  intro v
  simp only [covT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply]
  exact (p.contDiff).comp ((ContinuousLinearMap.apply ℝ E4 v).contDiff)

/-- `gX` as a function of the transition pair, through the continuous bilinear `prodMapL`. -/
lemma gX_eq (i j : atlas (Fin 4 → ℝ) X) (x : X) :
    gX i j x = ContinuousLinearMap.prodMapL ℝ (Fin 10 → ℝ) (Fin 10 → ℝ) (E4 →L[ℝ] ℝ) (E4 →L[ℝ] ℝ)
      (symAct ((Zt X).coordChange i j x), covT ((Zt X).coordChange j i x)) := rfl

/-- `π : Y → X`. -/
noncomputable def πY : Yobs X → X := fun y => (y : Sym2TX X).proj

lemma contMDiff_πY : ContMDiff ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
    (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ (πY (X := X)) := contMDiff_Yobs_proj

lemma gX_contMDiffOn (i j : atlas (Fin 4 → ℝ) X) :
    ContMDiffOn (modelWithCornersSelf ℝ (Fin 4 → ℝ)) (modelWithCornersSelf ℝ (CFib →L[ℝ] CFib)) ∞
      (gX i j) ((Zt X).baseSet i ∩ (Zt X).baseSet j) := by
  have h1 : IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) (∞ + 1) X := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ by rfl]; infer_instance
  have hZ : (Zt X).IsContMDiff (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ :=
    tangentBundleCore.isContMDiff (I := modelWithCornersSelf ℝ (Fin 4 → ℝ)) (M := X) (n := ∞)
  have hij := (Zt X).contMDiffOn_coordChange (n := ∞) (modelWithCornersSelf ℝ (Fin 4 → ℝ)) i j
  have hji := ((Zt X).contMDiffOn_coordChange (n := ∞) (modelWithCornersSelf ℝ (Fin 4 → ℝ)) j i).mono
    (Set.inter_comm _ _).subset
  have hs := (symAct_contDiff.of_le le_top).contMDiff.comp_contMDiffOn hij
  have hc := covT_contDiff.contMDiff.comp_contMDiffOn hji
  have hp := (ContinuousLinearMap.prodMapL ℝ (Fin 10 → ℝ) (Fin 10 → ℝ) (E4 →L[ℝ] ℝ)
    (E4 →L[ℝ] ℝ)).contMDiff.comp_contMDiffOn (hs.prodMk_space hc)
  exact hp.congr fun x _ => rfl

/-- **The frame core**: `Hom(Y × ℝ¹⁴, C)` with transitions `A ↦ g_ij ∘ A`. -/
noncomputable def frameCore : VectorBundleCore ℝ (Yobs X) EndC (atlas (Fin 4 → ℝ) X) where
  baseSet i := πY ⁻¹' (Zt X).baseSet i
  isOpen_baseSet i := ((Zt X).isOpen_baseSet i).preimage contMDiff_πY.continuous
  indexAt y := (Zt X).indexAt (πY y)
  mem_baseSet_at y := (Zt X).mem_baseSet_at (πY y)
  coordChange i j y := ContinuousLinearMap.compL ℝ CFib CFib CFib (gX i j (πY y))
  coordChange_self i y hy A :=
    ContinuousLinearMap.ext fun v => gX_self i (πY y) hy (A v)
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.compL ℝ CFib CFib CFib).continuous.comp_continuousOn
      ((gX_contMDiffOn i j).continuousOn.comp contMDiff_πY.continuous.continuousOn
        (fun y hy => hy))
  coordChange_comp i j k y hy A :=
    ContinuousLinearMap.ext fun v => gX_comp i j k (πY y) hy (A v)

instance frameCore_isContMDiff :
    (frameCore (X := X)).IsContMDiff
      ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞ where
  contMDiffOn_coordChange i j :=
    (ContinuousLinearMap.compL ℝ CFib CFib CFib).contMDiff.comp_contMDiffOn
      ((gX_contMDiffOn i j).comp contMDiff_πY.contMDiffOn (fun y hy => hy))

lemma gX_isUnit (i j : atlas (Fin 4 → ℝ) X) (x : X) (hx : x ∈ (Zt X).baseSet i ∩ (Zt X).baseSet j) :
    IsUnit (gX i j x) := by
  refine ⟨⟨gX i j x, gX j i x, ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    exact (gX_comp j i j x ⟨⟨hx.2, hx.1⟩, hx.2⟩ v).trans (gX_self j x hx.2 v)
  · refine ContinuousLinearMap.ext fun v => ?_
    exact (gX_comp i j i x ⟨hx, hx.1⟩ v).trans (gX_self i x hx.1 v)

/-- Total space of `Hom(Y × ℝ¹⁴, C)`. -/
abbrev HomTot (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] :=
  TotalSpace EndC (frameCore (X := X)).Fiber

/-- Frames: invertible points. -/
def frameSet : Set (HomTot X) := {p | IsUnit (M := EndC) p.2}

lemma isUnit_comp_iff {g A : EndC} (hg : IsUnit g) : IsUnit (g.comp A) ↔ IsUnit A := by
  show IsUnit (g * A) ↔ IsUnit A
  obtain ⟨u, rfl⟩ := hg
  exact Units.isUnit_units_mul u A

theorem isOpen_frames : IsOpen (frameSet (X := X)) := by
  have hU : IsOpen {A : EndC | IsUnit A} := by convert Units.isOpen (R := EndC)
  have key : frameSet (X := X) = ⋃ i, ((frameCore (X := X)).localTriv i).source ∩
      ((frameCore (X := X)).localTriv i) ⁻¹' (Set.univ ×ˢ {A : EndC | IsUnit A}) := by
    ext p
    simp only [frameSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_prod, Set.mem_univ, true_and, VectorBundleCore.localTriv_apply,
      VectorBundleCore.mem_localTriv_source]
    have hg : ∀ i, πY p.1 ∈ (Zt X).baseSet i →
        IsUnit (gX ((Zt X).indexAt (πY p.1)) i (πY p.1)) := fun i hi =>
      gX_isUnit _ i _ ⟨(Zt X).mem_baseSet_at _, hi⟩
    constructor
    · intro h
      refine ⟨(Zt X).indexAt (πY p.1), (Zt X).mem_baseSet_at _, ?_⟩
      exact (isUnit_comp_iff (hg _ ((Zt X).mem_baseSet_at _))).mpr h
    · rintro ⟨i, hi, h⟩
      exact (isUnit_comp_iff (hg i hi)).mp h
  rw [key]
  exact isOpen_iUnion fun i => ((frameCore (X := X)).localTriv i).continuousOn.isOpen_inter_preimage
    ((frameCore (X := X)).localTriv i).open_source (isOpen_univ.prod hU)

/-- **The GL(14) frame bundle of `C`**, an open subset of `Hom(Y × ℝ¹⁴, C)`. -/
def FrY (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : TopologicalSpace.Opens (HomTot X) :=
  ⟨frameSet, isOpen_frames⟩

/-- **The frame bundle is a smooth manifold** (model `(ℝ⁴ × ℝ¹⁰) × End(ℝ¹⁴)`). -/
theorem frames_isManifold :
    IsManifold (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)) ∞ (FrY X) := inferInstance

/-- Its projection to `Y` is smooth. -/
theorem contMDiff_frames_proj :
    ContMDiff (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
      ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞
      (fun f : FrY X => (f : HomTot X).proj) :=
  (Bundle.contMDiff_proj _).comp contMDiff_subtype_val

/-! ### The right `GL(14)` action `A ↦ A ∘ g` -/

/-- Right action on `Hom(ℝ¹⁴, C)`. -/
noncomputable def ract (p : HomTot X) (g : EndC) : HomTot X := ⟨p.1, (show EndC from p.2).comp g⟩

lemma ract_mem {p : HomTot X} (hp : p ∈ frameSet (X := X)) (g : EndCˣ) :
    ract p g ∈ frameSet (X := X) :=
  show IsUnit ((show EndC from p.2) * g) from hp.mul g.isUnit

lemma ract_proj (p : HomTot X) (g : EndC) : (ract p g).proj = p.proj := rfl

lemma ract_mul (p : HomTot X) (g h : EndC) : ract (ract p g) h = ract p (g * h) := rfl

lemma ract_one (p : HomTot X) : ract p 1 = p := rfl

/-- **Free**: on frames, `A ∘ g = A` forces `g = 1`. -/
theorem ract_free {p : HomTot X} (hp : p ∈ frameSet (X := X)) (g : EndC) (h : ract p g = p) :
    g = 1 := by
  obtain ⟨u, hu⟩ := hp
  have e : (show EndC from p.2) * g = (show EndC from p.2) := by
    have := congrArg (fun q : HomTot X => (show EndC from q.2)) h
    exact this
  rw [← hu] at e
  calc g = ↑u⁻¹ * (↑u * g) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 1 := by rw [e, Units.inv_mul]

/-- **Fibre-transitive**: two frames over the same point differ by some `g ∈ GL(14)` (unique by
`ract_free`, see `ract_unique`). -/
theorem ract_transitive {p q : HomTot X} (hp : p ∈ frameSet (X := X)) (hq : q ∈ frameSet (X := X))
    (h : p.proj = q.proj) : ∃ g : EndCˣ, ract p g = q := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  obtain ⟨b, A⟩ := p
  obtain ⟨b', B⟩ := q
  simp only at h; subst h
  refine ⟨u⁻¹ * v, ?_⟩
  show (⟨b, (show EndC from A) * ((u⁻¹ * v : EndCˣ) : EndC)⟩ : HomTot X) = ⟨b, B⟩
  congr 1
  change (show EndC from A) * _ = (show EndC from B)
  have hA : (show EndC from A) = (u : EndC) := hu.symm
  have hB : (show EndC from B) = (v : EndC) := hv.symm
  rw [hA, hB, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]

/-- Uniqueness of the transition element. -/
theorem ract_unique {p : HomTot X} (hp : p ∈ frameSet (X := X)) {g h : EndC}
    (e : ract p g = ract p h) : g = h := by
  obtain ⟨u, hu⟩ := hp
  have e' : (show EndC from p.2) * g = (show EndC from p.2) * h :=
    congrArg (fun q : HomTot X => (show EndC from q.2)) e
  rw [← hu] at e'
  calc g = ↑u⁻¹ * (↑u * g) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = h := by rw [e', ← mul_assoc, Units.inv_mul, one_mul]

/-- **Local triviality, equivariantly**: each local trivialisation intertwines `ract` with right
composition on the fibre `End(ℝ¹⁴)`, and carries frames to `U_i × GL(14)`. -/
theorem localTriv_ract (i : atlas (Fin 4 → ℝ) X) (p : HomTot X) (g : EndC) :
    (frameCore (X := X)).localTriv i (ract p g)
      = (((frameCore (X := X)).localTriv i p).1, (((frameCore (X := X)).localTriv i p).2).comp g) :=
  rfl

theorem localTriv_frames (i : atlas (Fin 4 → ℝ) X) {p : HomTot X}
    (hs : p ∈ ((frameCore (X := X)).localTriv i).source) :
    p ∈ frameSet (X := X) ↔ IsUnit (((frameCore (X := X)).localTriv i p).2) := by
  simp only [VectorBundleCore.localTriv_apply]
  rw [VectorBundleCore.mem_localTriv_source] at hs
  exact (isUnit_comp_iff (gX_isUnit _ i _ ⟨(Zt X).mem_baseSet_at _, hs⟩)).symm

/-- **The action is smooth** (for each fixed `g`): in a trivialisation it is `(y, A) ↦ (y, A ∘ g)`. -/
theorem contMDiff_ract (g : EndC) :
    ContMDiff (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)) ∞ (fun p : HomTot X => ract p g) := by
  intro p₀
  have hid := (contMDiffAt_totalSpace (n := ∞)
    (IM := ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
    (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
    (E := (frameCore (X := X)).Fiber) (F := EndC)
    (f := fun p : HomTot X => p) (x₀ := p₀)).mp contMDiffAt_id
  rw [contMDiffAt_totalSpace (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
    (modelWithCornersSelf ℝ (Fin 10 → ℝ)))]
  refine ⟨hid.1, ?_⟩
  have hR : ContDiff ℝ ∞ (fun A : EndC => A.comp g) :=
    ((ContinuousLinearMap.compL ℝ CFib CFib CFib).flip g).contDiff
  convert hR.contMDiff.contMDiffAt.comp p₀ hid.2 using 1
  funext x
  simp only [Function.comp, ract_proj, FiberBundle.trivializationAt, VectorBundleCore.localTriv_apply]
  rfl

/-- **The action map `(A, g) ↦ A ∘ g` is jointly smooth** on `Hom(ℝ¹⁴, C) × End(ℝ¹⁴)`. -/
theorem contMDiff_ract_joint :
    ContMDiff ((((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)).prod (modelWithCornersSelf ℝ EndC))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)) ∞ (fun q : HomTot X × EndC => ract q.1 q.2) := by
  intro q₀
  have hid := (contMDiffAt_totalSpace (n := ∞)
    (IM := ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
    (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
    (E := (frameCore (X := X)).Fiber) (F := EndC)
    (f := fun p : HomTot X => p) (x₀ := q₀.1)).mp contMDiffAt_id
  rw [contMDiffAt_totalSpace (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
    (modelWithCornersSelf ℝ (Fin 10 → ℝ)))]
  refine ⟨hid.1.comp q₀ contMDiffAt_fst, ?_⟩
  have h := (hid.2.comp q₀ contMDiffAt_fst).clm_comp (contMDiffAt_snd (p := q₀))
  convert h using 1
  funext x
  simp only [Function.comp, ract_proj, FiberBundle.trivializationAt, VectorBundleCore.localTriv_apply]
  rfl

open MulOpposite in
/-- `GL(14)` acts on the right on the frames. -/
noncomputable instance instFrYAction : MulAction EndCˣᵐᵒᵖ (FrY X) where
  smul g f := ⟨ract f.1 (unop g : EndCˣ), ract_mem f.2 (unop g)⟩
  one_smul _ := rfl
  mul_smul g h f := by
    apply Subtype.ext
    change ract f.1 (((unop h * unop g : EndCˣ)) : EndC) = ract (ract f.1 ((unop h : EndCˣ) : EndC)) ((unop g : EndCˣ) : EndC)
    rw [ract_mul, Units.val_mul]

open MulOpposite in
/-- **`FrY` is a principal `GL(14)`-bundle over `Y`** in the set-level sense of `GU.PrincipalBundle`
(free, fibre-transitive, onto). The smooth data are separate theorems: `frames_isManifold`,
`contMDiff_frames_proj`, `contMDiff_ract_joint` (on the ambient `Hom × End`), and equivariant local
triviality `localTriv_ract` + `localTriv_frames`. -/
noncomputable def frYBundle : GU.PrincipalBundle EndCˣ (FrY X) (Yobs X) where
  proj f := (f : HomTot X).proj
  proj_surjective y := ⟨⟨⟨y, (1 : EndC)⟩, isUnit_one⟩, rfl⟩
  proj_smul _ _ := rfl
  free f g h := by
    apply Units.ext
    exact ract_free f.2 _ (congrArg Subtype.val h)
  transitive f f' h := by
    obtain ⟨g, hg⟩ := ract_transitive f.2 f'.2 h
    exact ⟨g, Subtype.ext hg⟩

section LieGroupAction
open MulOpposite

noncomputable local instance : NormedRing EndC := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndC := inferInstance
noncomputable local instance : ChartedSpace EndC EndCˣ := Units.instChartedSpace

/-- `GL(14) = End(ℝ¹⁴)ˣ` is a Lie group (Mathlib's units of a complete normed algebra). -/
example : LieGroup (modelWithCornersSelf ℝ EndC) ∞ EndCˣ := inferInstance

/-- **The action `FrY × GL(14) → FrY` is smooth.** -/
theorem contMDiff_smul_FrY :
    ContMDiff ((((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)).prod (modelWithCornersSelf ℝ EndC))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)) ∞
      (fun q : FrY X × EndCˣ => op q.2 • q.1) := by
  have h := (contMDiff_ract_joint (X := X)).comp
    ((contMDiff_subtype_val (n := ∞) (U := FrY X)).prodMap (Units.contMDiff_val (n := ∞)))
  intro q
  rw [contMDiffAt_iff_target]
  exact ⟨ContinuousAt.codRestrict (t := (FrY X : Set (HomTot X)))
    (fun q : FrY X × EndCˣ => ract_mem q.1.2 q.2) (h q).continuousAt,
    (contMDiffAt_iff_target.mp (h q)).2⟩

end LieGroupAction

end GU.Observerse
