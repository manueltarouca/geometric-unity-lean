import GU.Library.RegularValue

/-!
# Regular level sets from the textbook hypothesis (Track 3, L4e `of_contMDiff`)

**`RegularLevel.of_contMDiff`**: if `f : M → F` is smooth and its manifold derivative is onto at every
point of `f⁻¹{c}`, then `f⁻¹{c}` is a regular level set in the chartwise sense used by
`isManifold_regularLevel` (`RegularLevel`). Instance: `regularLevel_fst`.
-/

open scoped ContDiff Manifold
open Topology

namespace GU.Library

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


/-- **The textbook regular value theorem's hypothesis gives the chartwise `RegularLevel`.** -/
theorem RegularLevel.of_contMDiff {f : M → F} {c : F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hs : ∀ x, f x = c → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) : RegularLevel E f c := by
  refine ⟨fun a => ?_, fun a x hx hc => ?_⟩
  · have h := hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := a))
    exact contMDiffOn_iff_contDiffOn.mp h
  · set φ := chartAt E a
    have hxt : φ x ∈ φ.target := φ.map_source hx
    have hsymm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (φ x) :=
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
        (φ.open_target.mem_nhds hxt)).mdifferentiableAt (by simp)
    have hφ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ x :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
        (φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    have hfx : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f (φ.symm (φ x)) := by
      rw [φ.left_inv hx]; exact (hf x).mdifferentiableAt (by simp)
    -- chain rule for `f ∘ φ.symm`
    have hchain : fderiv ℝ (f ∘ φ.symm) (φ x) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (φ x)) := by
      have e : fderiv ℝ (f ∘ φ.symm) (φ x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f ∘ φ.symm) (φ x) := by
        rw [mfderiv_eq_fderiv]; rfl
      rw [e, mfderiv_comp (φ x) hfx hsymm, φ.left_inv hx]
    -- `φ.symm ∘ φ = id` near `x`, so `mfderiv φ.symm` is onto
    have hid : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (φ x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x) =
        ContinuousLinearMap.id ℝ E := by
      have hev : (φ.symm ∘ φ) =ᶠ[𝓝 x] id := by
        filter_upwards [φ.open_source.mem_nhds hx] with z hz
        exact φ.left_inv hz
      have h1 := mfderiv_comp x hsymm hφ
      rw [hev.mfderiv_eq, mfderiv_id] at h1
      exact h1.symm
    have key : ∀ u : E, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (φ x)) ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x) u) = u :=
      fun u => congrArg (fun L : E →L[ℝ] E => L u) hid
    rw [hchain, LinearMap.range_eq_top]
    intro w
    obtain ⟨u, hu⟩ := hs x hc w
    refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x u, ?_⟩
    erw [ContinuousLinearMap.comp_apply, key u]
    exact hu
/-- Instance: `{(a, b) | a = 0}` in `ℝ²`, as the level set of the projection. -/
theorem regularLevel_fst : RegularLevel (ℝ × ℝ) (Prod.fst : ℝ × ℝ → ℝ) 0 := by
  refine RegularLevel.of_contMDiff (contMDiff_iff_contDiff.mpr contDiff_fst) fun x _ w => ⟨(w, 0), ?_⟩
  rw [mfderiv_eq_fderiv]
  show (fderiv ℝ Prod.fst x) (w, 0) = w
  rw [fderiv_fst]; rfl

end GU.Library
