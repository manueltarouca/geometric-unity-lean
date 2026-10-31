import GU.Bundle.HomFrames
import GU.Bundle.Isometry77

/-!
# The two frame bundles of `C` agree: a fibrewise-linear diffeomorphism of total spaces

`SmoothFrames.lean` builds `Hom(Y × CFib, C)` from the cocycle `gX` (`frameCore`, total space
`HomTot`); `HomFrames.lean` uses Mathlib's hom bundle `Hom(Y × ℝ¹⁴, C)` (`HomTotM`). With the
isometry `Φ : ℝ¹⁴ ≃ CFib` of `Isometry77.lean` (orthonormal basis of the (7,7) model):

* `toM : (y, A) ↦ (y, A ∘ Φ)` and `ofM : (y, B) ↦ (y, B ∘ Φ⁻¹)` are mutually inverse
  (`ofM_toM`, `toM_ofM`), cover the identity of `Y`, and
* **`contMDiff_toM`, `contMDiff_ofM`**: both are smooth (in trivialisations they are right
  composition with `Φ^{±1}`, using `frameCore_localTriv_eq` and `triv_apply`);
* **`toM_mem_iff`**: they match frames: `A` is invertible iff `A ∘ Φ` is an isomorphism `ℝ¹⁴ ≃ C_y`.

Packaged: **`homDiffeo`**, a `Diffeomorph` of the total spaces over `id_Y` (`toM_proj`), and
**`frEquiv : FrY ≃ FrM`** (frames to frames, `toM_mem_iff`, `ofM_mem_iff`). **`toM_ract`**: `toM` is
equivariant for the right actions, with `g ∈ End(CFib)` acting on the `ℝ¹⁴` side as `Φ⁻¹ g Φ`. This
closes the comparison left open in reviews 10/17. Not stated: smoothness of `frEquiv` as a map of the
open subsets (immediate from `homDiffeo` by restriction), and the group isomorphism
`End(CFib)ˣ ≃* Aut(ℝ¹⁴)`. Any linear `Φ` would do; the isometry of `Isometry77.lean` is chosen so that
orthonormal frames on both sides will correspond.
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- `Φ` as a continuous linear equivalence. -/
noncomputable def ΦL : R14 ≃L[ℝ] CFib := GU.Iso77.Φiso.toContinuousLinearEquiv

noncomputable def toM (p : HomTot X) : HomTotM X := ⟨p.proj, (show EndC from p.2).comp (ΦL : R14 →L[ℝ] CFib)⟩
noncomputable def ofM (q : HomTotM X) : HomTot X :=
  ⟨q.proj, (show HomF from q.2).comp (ΦL.symm : CFib →L[ℝ] R14)⟩

lemma ofM_toM (p : HomTot X) : ofM (toM p) = p := by
  obtain ⟨y, A⟩ := p
  show (⟨y, ((show EndC from A).comp (ΦL : R14 →L[ℝ] CFib)).comp (ΦL.symm : CFib →L[ℝ] R14)⟩ : HomTot X) = ⟨y, A⟩
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  show (show EndC from A) (ΦL (ΦL.symm v)) = (show EndC from A) v
  rw [ΦL.apply_symm_apply]

lemma toM_ofM (q : HomTotM X) : toM (ofM q) = q := by
  obtain ⟨y, B⟩ := q
  show (⟨y, ((show HomF from B).comp (ΦL.symm : CFib →L[ℝ] R14)).comp (ΦL : R14 →L[ℝ] CFib)⟩ : HomTotM X) = ⟨y, B⟩
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  show (show HomF from B) (ΦL.symm (ΦL v)) = (show HomF from B) v
  rw [ΦL.symm_apply_apply]

/-- Local formula for `toM`. -/
lemma triv_toM (y : Yobs X) (p : HomTot X) (hp : p.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    ((trivializationAt HomF (HomCb (X := X)) y) (toM p)).2 =
      (((frameCore (X := X)).localTriv (achart (Fin 4 → ℝ) (πY y)) p).2 : EndC).comp (ΦL : R14 →L[ℝ] CFib) := by
  rw [triv_apply y (toM p) hp]
  refine ContinuousLinearMap.ext fun v => ?_
  exact (frameCore_localTriv_eq y p hp (ΦL v)).symm

/-- Local formula for `ofM`. -/
lemma triv_ofM (y : Yobs X) (q : HomTotM X) (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    (((frameCore (X := X)).localTriv (achart (Fin 4 → ℝ) (πY y)) (ofM q)).2 : EndC) =
      ((trivializationAt HomF (HomCb (X := X)) y) q).2.comp (ΦL.symm : CFib →L[ℝ] R14) := by
  rw [triv_apply y q hq]
  refine ContinuousLinearMap.ext fun w => ?_
  exact frameCore_localTriv_eq y (ofM q) hq w

/-- **`toM` is smooth.** -/
theorem contMDiff_toM :
    ContMDiff (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF)) ∞ (toM (X := X)) := by
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
  have hR : ContDiff ℝ ∞ (fun A : EndC => A.comp (ΦL : R14 →L[ℝ] CFib)) :=
    contDiff_id.clm_comp contDiff_const
  have hg := hR.contMDiff.contMDiffAt.comp p₀ hid.2
  refine hg.congr_of_eventuallyEq ?_
  have hU : {p : HomTot X | p.proj ∈ (trivializationAt CFib (Cb (X := X)) p₀.proj).baseSet} ∈ nhds p₀ :=
    ((trivializationAt CFib (Cb (X := X)) p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj EndC (frameCore (X := X)).Fiber)).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt CFib (Cb (X := X)) p₀.proj)
  filter_upwards [hU] with p hp
  exact triv_toM p₀.proj p hp

/-- **`ofM` is smooth.** -/
theorem contMDiff_ofM :
    ContMDiff (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC)) ∞ (ofM (X := X)) := by
  intro q₀
  have hid := (contMDiffAt_totalSpace (n := ∞)
    (IM := ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF))
    (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ)))
    (E := HomCb (X := X)) (F := HomF)
    (f := fun q : HomTotM X => q) (x₀ := q₀)).mp contMDiffAt_id
  rw [contMDiffAt_totalSpace (IB := (modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod
    (modelWithCornersSelf ℝ (Fin 10 → ℝ)))]
  refine ⟨hid.1, ?_⟩
  have hR : ContDiff ℝ ∞ (fun B : HomF => B.comp (ΦL.symm : CFib →L[ℝ] R14)) :=
    contDiff_id.clm_comp contDiff_const
  have hg := hR.contMDiff.contMDiffAt.comp q₀ hid.2
  refine hg.congr_of_eventuallyEq ?_
  have hU : {q : HomTotM X | q.proj ∈ (trivializationAt CFib (Cb (X := X)) q₀.proj).baseSet} ∈ nhds q₀ :=
    ((trivializationAt CFib (Cb (X := X)) q₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj HomF (HomCb (X := X)))).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt CFib (Cb (X := X)) q₀.proj)
  filter_upwards [hU] with q hq
  exact triv_ofM q₀.proj q hq

/-- **Frames correspond**: `A` invertible iff `A ∘ Φ` is an isomorphism `ℝ¹⁴ ≃ C_y`. -/
theorem toM_mem_iff (p : HomTot X) : toM p ∈ FrMset (X := X) ↔ p ∈ frameSet (X := X) := by
  constructor
  · rintro ⟨e, he⟩
    let f : CFib ≃L[ℝ] CFib := ΦL.symm.trans e
    refine ⟨⟨f, f.symm, ?_, ?_⟩, ?_⟩
    · exact ContinuousLinearMap.ext fun v => f.apply_symm_apply v
    · exact ContinuousLinearMap.ext fun v => f.symm_apply_apply v
    · refine ContinuousLinearMap.ext fun v => ?_
      show e (ΦL.symm v) = (show EndC from p.2) v
      have := congrArg (fun L : HomF => L (ΦL.symm v)) he
      simp only [ContinuousLinearEquiv.coe_coe] at this
      rw [this]; show (show EndC from p.2) (ΦL (ΦL.symm v)) = _; rw [ΦL.apply_symm_apply]
  · rintro ⟨u, hu⟩
    let f : CFib ≃L[ℝ] CFib := ContinuousLinearEquiv.unitsEquiv ℝ CFib u
    refine ⟨ΦL.trans f, ContinuousLinearMap.ext fun v => ?_⟩
    show f (ΦL v) = (show EndC from p.2) (ΦL v)
    rw [ContinuousLinearEquiv.unitsEquiv_apply, hu]

lemma toM_proj (p : HomTot X) : (toM p).proj = p.proj := rfl

lemma ofM_mem_iff (q : HomTotM X) : ofM q ∈ frameSet (X := X) ↔ q ∈ FrMset (X := X) := by
  rw [← toM_mem_iff, toM_ofM]

/-- **The total spaces are diffeomorphic** (fibrewise linear, over `id_Y`). -/
noncomputable def homDiffeo :
    Diffeomorph (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ EndC))
      (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF)) (HomTot X) (HomTotM X) ∞ where
  toFun := toM
  invFun := ofM
  left_inv := ofM_toM
  right_inv := toM_ofM
  contMDiff_toFun := contMDiff_toM
  contMDiff_invFun := contMDiff_ofM

/-- **The frame bundles correspond** (as sets): `FrY ≃ FrM` over `Y`. -/
noncomputable def frEquiv : FrY X ≃ FrM X where
  toFun f := ⟨toM f.1, (toM_mem_iff f.1).mpr f.2⟩
  invFun g := ⟨ofM g.1, (ofM_mem_iff g.1).mpr g.2⟩
  left_inv f := Subtype.ext (ofM_toM f.1)
  right_inv g := Subtype.ext (toM_ofM g.1)

/-- **Equivariance**: `toM (A ∘ g) = (A ∘ Φ) ∘ (Φ⁻¹ g Φ)`, i.e. `toM` intertwines the right
`End(CFib)`-action with the `End(ℝ¹⁴)`-action conjugated by `Φ`. -/
theorem toM_ract (p : HomTot X) (g : EndC) :
    toM (ract p g) = ⟨p.proj, (show HomF from (toM p).2).comp
      ((ΦL.symm : CFib →L[ℝ] R14).comp (g.comp (ΦL : R14 →L[ℝ] CFib)))⟩ := by
  show (⟨p.proj, _⟩ : HomTotM X) = ⟨p.proj, _⟩
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  show (show EndC from p.2) (g (ΦL v)) = (show EndC from p.2) (ΦL (ΦL.symm (g (ΦL v))))
  rw [ΦL.apply_symm_apply]

end GU.Observerse
