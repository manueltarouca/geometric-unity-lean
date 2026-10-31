import GU.Bundle.Principal
import GU.Observerse.ChimericBundle

/-!
# The frame bundle `P_Fr(C)` of the chimeric bundle over the global `Y` ((3.32))

A frame at `y ∈ Y` is a linear isomorphism `CFib ≃ₗ C_y` (`CFib = ℝ¹⁰ × (ℝ⁴)*`, rank 14).
`GL(CFib) = (CFib ≃ₗ CFib)` acts on the right by precomposition. `frameBundle` proves this is a
principal `GL(14)`-bundle over `Y` in the sense of `GU.PrincipalBundle`.

Caveat (review 6): Mathlib's fibers are definitionally the model `CFib`, so `Frames X` is literally
`Yobs X × GL(CFib)` and `GU.PrincipalBundle` has no topology. This statement therefore has no
bundle content beyond the product; local triviality and smoothness of the frame bundle are not
formalised. The O(7,7) reduction is in `OrthoFrames.lean`; the spin cover's algebraic core is in
`SpinCover.lean`.
-/

namespace GU

open Bundle Manifold GU.Observerse MulOpposite
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- Frames of `C`. -/
noncomputable def Frames (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
    [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X] : Type :=
  Σ y : Yobs X, CFib ≃ₗ[ℝ] Cb (X := X) y

noncomputable abbrev GLC := CFib ≃ₗ[ℝ] CFib

noncomputable instance : MulAction GLCᵐᵒᵖ (Frames X) where
  smul g f := ⟨f.1, g.unop.trans f.2⟩
  one_smul f := by cases f; rfl
  mul_smul a b f := by cases f; rfl

/-- **`P_Fr(C)` is a principal `GL(14)`-bundle over `Y`.** -/
def frameBundle : PrincipalBundle GLC (Frames X) (Yobs X) where
  proj := Sigma.fst
  proj_surjective y := ⟨⟨y, LinearEquiv.refl ℝ _⟩, rfl⟩
  proj_smul _ _ := rfl
  free f g h := by
    obtain ⟨y, e⟩ := f
    have h2 : g.trans e = e := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    apply LinearEquiv.ext
    intro v
    apply e.injective
    simpa using LinearEquiv.congr_fun h2 v
  transitive f f' h := by
    obtain ⟨y, e⟩ := f; obtain ⟨y', e'⟩ := f'
    simp only at h; subst h
    refine ⟨e'.trans e.symm, ?_⟩
    show (⟨y, (e'.trans e.symm).trans e⟩ : Frames X) = ⟨y, e'⟩
    congr 1
    exact LinearEquiv.ext fun v => e.apply_symm_apply (e' v)

end GU
