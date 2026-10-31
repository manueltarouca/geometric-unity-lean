import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth principal bundles

`SmoothPrincipalBundle IB IG IP B G P`: a smooth projection `proj : P → B`, a smooth right action
`act : P × G → P` that is free and fibre-transitive and preserves fibres, surjective `proj`, and
**smooth local trivialisations** in the form: around every base point a smooth local section `σ`
and a smooth "division" map `τ : P → G` on the preimage with `σ (proj p) · τ p = p`. (Then
`(b, g) ↦ σ b · g` is a diffeomorphism `V × G ≅ proj⁻¹ V` with inverse `p ↦ (proj p, τ p)`, and
`τ (p · g) = τ p · g` follows from freeness.) `G` is required to be a Lie group and `B`, `P` manifolds.
-/

namespace GU.Library

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [TopologicalSpace B] [ChartedSpace HB B]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [TopologicalSpace HP]
  [TopologicalSpace P] [ChartedSpace HP P]

/-- **A smooth principal `G`-bundle** `P → B`. -/
structure SmoothPrincipalBundle (IB : ModelWithCorners 𝕜 EB HB) (IG : ModelWithCorners 𝕜 EG HG)
    (IP : ModelWithCorners 𝕜 EP HP) (B G P : Type*) [TopologicalSpace B] [ChartedSpace HB B]
    [TopologicalSpace G] [ChartedSpace HG G] [Group G] [TopologicalSpace P] [ChartedSpace HP P]
    [LieGroup IG ∞ G] [IsManifold IB ∞ B] [IsManifold IP ∞ P] where
  proj : P → B
  act : P → G → P
  act_one : ∀ p, act p 1 = p
  act_mul : ∀ p g h, act (act p g) h = act p (g * h)
  proj_act : ∀ p g, proj (act p g) = proj p
  free : ∀ p g, act p g = p → g = 1
  transitive : ∀ p q, proj p = proj q → ∃ g, act p g = q
  proj_surjective : Function.Surjective proj
  smooth_proj : ContMDiff IP IB ∞ proj
  smooth_act : ContMDiff (IP.prod IG) IP ∞ (fun pg : P × G => act pg.1 pg.2)
  locTriv : ∀ b : B, ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ ∃ (σ : B → P) (τ : P → G),
    ContMDiffOn IB IP ∞ σ V ∧ (∀ y ∈ V, proj (σ y) = y) ∧
    ContMDiffOn IP IG ∞ τ (proj ⁻¹' V) ∧ (∀ p ∈ proj ⁻¹' V, act (σ (proj p)) (τ p) = p)

end GU.Library
