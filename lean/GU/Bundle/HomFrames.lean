/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Bundle.FramesCb
import GU.Bundle.Principal

/-!
# The frame bundle of `C` inside Mathlib's hom bundle `Hom(Y × ℝ¹⁴, C)`

Mathlib's `Bundle.ContinuousLinearMap` construction applies to `Cb` once its fibres get their
(definitionally inherited) group/topological instances, giving the smooth vector bundle
`HomCb y = ℝ¹⁴ →L C_y` over `Y` (`homCb_smooth`). Here the model is `Fin 14 → ℝ` (not a product type,
which avoids the `Trivial`/product instance diamond met in `FramesCb.lean`).

* `FrM`: the points `(y, A)` with `A : ℝ¹⁴ ≃ C_y` a linear isomorphism.
* **`isOpen_FrM`**: an open subset of the total space (isomorphisms are open,
  `ContinuousLinearEquiv.isOpen`, and the trivialisations compose with isomorphisms).
* **`FrM_isManifold`**: so the frame bundle of `C`, built entirely from Mathlib's bundle API, is a
  smooth manifold; `contMDiff_FrM_proj`: its projection to `Y` is smooth.

* `frMBundle`: a set-level principal `GL(14)`-bundle (`GL14 = ℝ¹⁴ ≃L ℝ¹⁴`, precomposition).

This is an independent construction of the frame bundle inside Mathlib's hom bundle. The data differ
from `frameCore`/`FrY` of `SmoothFrames.lean` (fibre model `ℝ¹⁴ →L CFib` vs `End(CFib)`, group
`Aut(ℝ¹⁴)` vs `End(CFib)ˣ`); after choosing `Φ : ℝ¹⁴ ≃ CFib` they are compared in
`FramesCompare.lean` (`homDiffeo`, `frEquiv`). Downstream files (`SmoothOrtho`, `OrthoGlue`) still use `FrY`.

CAVEATS. Frames are `ℝ¹⁴ ≃L CFib`, identified with `ℝ¹⁴ →L C_y` through the definitional `C_y ≡ CFib`.
Not here (unlike `SmoothFrames.lean`): equivariant local triviality and smoothness of the action
(`ContinuousLinearEquiv` has no topology in Mathlib; that would go through `(ℝ¹⁴ →L ℝ¹⁴)ˣ`).
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

noncomputable instance (y : Yobs X) : AddCommGroup (Cb (X := X) y) := inferInstanceAs (AddCommGroup CFib)
instance (y : Yobs X) : IsTopologicalAddGroup (Cb (X := X) y) :=
  inferInstanceAs (IsTopologicalAddGroup CFib)
instance (y : Yobs X) : ContinuousSMul ℝ (Cb (X := X) y) := inferInstanceAs (ContinuousSMul ℝ CFib)

/-- `ℝ¹⁴`. -/
abbrev R14 := Fin 14 → ℝ

/-- The hom bundle `y ↦ (ℝ¹⁴ →L C_y)`. -/
abbrev HomCb := fun y : Yobs X => (Bundle.Trivial (Yobs X) R14 y →L[ℝ] Cb (X := X) y)

/-- Its fibre model. -/
abbrev HomF := R14 →L[ℝ] CFib

noncomputable instance : FiberBundle HomF (HomCb (X := X)) := inferInstance
noncomputable instance : VectorBundle ℝ HomF (HomCb (X := X)) := inferInstance

theorem homCb_smooth : ContMDiffVectorBundle ∞ HomF (HomCb (X := X))
    ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) := inferInstance

abbrev HomTotM (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] := TotalSpace HomF (HomCb (X := X))

noncomputable instance : TopologicalSpace (HomTotM X) := inferInstance

/-- Frames: linear isomorphisms `ℝ¹⁴ ≃ C_y`. -/
def FrMset : Set (HomTotM X) :=
  {p | (show HomF from p.2) ∈ Set.range ((↑) : (R14 ≃L[ℝ] CFib) → HomF)}

lemma triv_apply (y : Yobs X) (q : HomTotM X) (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    ((trivializationAt HomF (HomCb (X := X)) y) q).2 =
      (show HomF from ((trivializationAt CFib (Cb (X := X)) y).continuousLinearEquivAt ℝ q.proj hq :
        Cb (X := X) q.proj →L[ℝ] CFib).comp q.2) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 : ((trivializationAt R14 (Bundle.Trivial (Yobs X) R14) y).symmL ℝ q.proj) v = v := by
    rw [Trivialization.symmL_apply]
    · exact Bundle.Trivial.trivialization_symm_apply (Yobs X) R14 q.proj v
    · exact Set.mem_univ _
  show ((trivializationAt CFib (Cb (X := X)) y).continuousLinearMapAt ℝ q.proj)
      (q.2 (((trivializationAt R14 (Bundle.Trivial (Yobs X) R14) y).symmL ℝ q.proj) v)) = _
  rw [h1, ← Trivialization.coe_continuousLinearEquivAt_eq _ hq]
  rfl

lemma mem_FrM_iff (y : Yobs X) (q : HomTotM X) (hq : q.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    q ∈ FrMset (X := X) ↔
      ((trivializationAt HomF (HomCb (X := X)) y) q).2 ∈ Set.range ((↑) : (R14 ≃L[ℝ] CFib) → HomF) := by
  rw [triv_apply y q hq]
  set E : CFib ≃L[ℝ] CFib := (trivializationAt CFib (Cb (X := X)) y).continuousLinearEquivAt ℝ q.proj hq
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.trans E, ContinuousLinearMap.ext fun v => ?_⟩
    show E (f v) = E ((show HomF from q.2) v)
    rw [← hf]; rfl
  · rintro ⟨g, hg⟩
    refine ⟨g.trans E.symm, ContinuousLinearMap.ext fun v => ?_⟩
    show E.symm (g v) = (show HomF from q.2) v
    have := congrArg (fun L : HomF => L v) hg
    simp only [ContinuousLinearEquiv.coe_coe] at this
    rw [this]
    exact E.symm_apply_apply _

theorem isOpen_FrM : IsOpen (FrMset (X := X)) := by
  have hU : IsOpen (Set.range ((↑) : (R14 ≃L[ℝ] CFib) → HomF)) := ContinuousLinearEquiv.isOpen
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  set e := trivializationAt HomF (HomCb (X := X)) p.proj
  have hpe : p ∈ e.source := by
    rw [e.mem_source]; exact FiberBundle.mem_baseSet_trivializationAt' p.proj
  refine ⟨e.source ∩ e ⁻¹' (Set.univ ×ˢ Set.range ((↑) : (R14 ≃L[ℝ] CFib) → HomF)), ?_,
    e.continuousOn.isOpen_inter_preimage e.open_source (isOpen_univ.prod hU), hpe, ?_⟩
  · rintro q ⟨hq, -, hq2⟩
    have hb : q.proj ∈ (trivializationAt CFib (Cb (X := X)) p.proj).baseSet := (e.mem_source.mp hq).2
    exact (mem_FrM_iff p.proj q hb).mpr hq2
  · have hb : p.proj ∈ (trivializationAt CFib (Cb (X := X)) p.proj).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' p.proj
    exact ⟨Set.mem_univ _, (mem_FrM_iff p.proj p hb).mp hp⟩

variable (X) in
/-- **The frame bundle of `C`**, as an open subset of Mathlib's hom bundle. -/
def FrM : TopologicalSpace.Opens (HomTotM X) :=
  ⟨FrMset, isOpen_FrM⟩

-- Shortcut: the synthesized subtype topology sits exactly at `synthInstance.maxSize` (128).
noncomputable instance : TopologicalSpace (FrM X) := instTopologicalSpaceSubtype
/-- **It is a smooth manifold** (model `(ℝ⁴ × ℝ¹⁰) × (ℝ¹⁴ →L ℝ¹⁴)`). -/
theorem FrM_isManifold :
    IsManifold (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF)) ∞ (FrM X) := inferInstance

theorem contMDiff_FrM_proj :
    ContMDiff (((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))).prod
      (modelWithCornersSelf ℝ HomF))
      ((modelWithCornersSelf ℝ (Fin 4 → ℝ)).prod (modelWithCornersSelf ℝ (Fin 10 → ℝ))) ∞
      (fun f : FrM X => (f : HomTotM X).proj) :=
  (Bundle.contMDiff_proj _).comp contMDiff_subtype_val

/-- `GL(14) = Aut(ℝ¹⁴)`. -/
abbrev GL14 := R14 ≃L[ℝ] R14

open MulOpposite in
/-- Right action by precomposition. -/
noncomputable instance : MulAction GL14ᵐᵒᵖ (FrM X) where
  smul g f := ⟨⟨(f : HomTotM X).proj, (show HomF from (f : HomTotM X).2).comp ((unop g : GL14) : R14 →L[ℝ] R14)⟩, by
    obtain ⟨e, he⟩ := f.2
    exact ⟨(unop g).trans e, by rw [← he]; rfl⟩⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

open MulOpposite in
/-- **`FrM` is a principal `GL(14)`-bundle over `Y`** (set level: free, fibre-transitive, onto). -/
noncomputable def frMBundle : GU.PrincipalBundle GL14 (FrM X) (Yobs X) where
  proj f := (f : HomTotM X).proj
  proj_surjective y := by
    let e : R14 ≃L[ℝ] CFib := (ContinuousLinearEquiv.ofFinrankEq (by
      rw [Module.finrank_fin_fun]
      have hd : Module.finrank ℝ ((Fin 4 → ℝ) →L[ℝ] ℝ) = 4 := by
        rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin 4 → ℝ) (F' := ℝ)).finrank_eq]
        simp
      rw [Module.finrank_prod, hd]; simp))
    exact ⟨⟨⟨y, (e : HomF)⟩, ⟨e, rfl⟩⟩, rfl⟩
  proj_smul _ _ := rfl
  free f g h := by
    obtain ⟨e, he⟩ := f.2
    have h2 := congrArg (fun q : FrM X => (show HomF from (q : HomTotM X).2)) h
    change (show HomF from (f : HomTotM X).2).comp (g : R14 →L[ℝ] R14) = show HomF from (f : HomTotM X).2 at h2
    rw [← he] at h2
    refine ContinuousLinearEquiv.ext (funext fun v => ?_)
    apply e.injective
    exact congrArg (fun L : HomF => L v) h2
  transitive f f' h := by
    obtain ⟨⟨y, A⟩, ⟨e, he⟩⟩ := f
    obtain ⟨⟨y', A'⟩, ⟨e', he'⟩⟩ := f'
    simp only at h
    subst h
    refine ⟨e'.trans e.symm, ?_⟩
    apply Subtype.ext
    show (⟨y, (show HomF from A).comp ((e'.trans e.symm : R14 ≃L[ℝ] R14) : R14 →L[ℝ] R14)⟩ : HomTotM X) = ⟨y, A'⟩
    congr 1
    change (show HomF from A).comp _ = (show HomF from A')
    have hA : (show HomF from A) = (e : HomF) := he.symm
    have hA' : (show HomF from A') = (e' : HomF) := he'.symm
    rw [hA, hA']
    refine ContinuousLinearMap.ext fun v => ?_
    show e (e.symm (e' v)) = e' v
    exact e.apply_symm_apply _

end GU.Observerse
