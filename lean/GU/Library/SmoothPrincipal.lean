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

variable {IB : ModelWithCorners 𝕜 EB HB} {IG : ModelWithCorners 𝕜 EG HG}
  {IP : ModelWithCorners 𝕜 EP HP} [LieGroup IG ∞ G] [IsManifold IB ∞ B] [IsManifold IP ∞ P]

/-- **A reduction of the structure group** of a smooth principal `G`-bundle to `H ≤ G`: a subset
`Q ⊆ P` that is `H`-stable, on which `H` acts transitively on each fibre, and which admits smooth
local sections of `P` with values in `Q` (`locSec`; so `Q` meets every fibre). This is a
local-section characterisation; it is equivalent to the sub-bundle definition (a principal
`H`-bundle with an equivariant embedding into `P`) when `H` is an embedded Lie subgroup, which is
not proved here in general (for the adapted frames the sub-bundle is built directly:
`adaptedBundle`, `adaptedSubBundle`). `SmoothReduction.locTriv` derives smooth local trivialisations whose division maps
are `H`-valued on `Q` (smooth as `G`-valued maps). -/
structure SmoothReduction (Pb : SmoothPrincipalBundle IB IG IP B G P) (H : Subgroup G) where
  carrier : Set P
  act_mem : ∀ p ∈ carrier, ∀ g ∈ H, Pb.act p g ∈ carrier
  transitive : ∀ p ∈ carrier, ∀ q ∈ carrier, Pb.proj p = Pb.proj q → ∃ g ∈ H, Pb.act p g = q
  locSec : ∀ b : B, ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ ∃ σ : B → P,
    ContMDiffOn IB IP ∞ σ V ∧ ∀ y ∈ V, Pb.proj (σ y) = y ∧ σ y ∈ carrier

namespace SmoothReduction

variable {Pb : SmoothPrincipalBundle IB IG IP B G P} {H : Subgroup G}

/-- The reduced set meets every fibre. -/
lemma exists_mem (R : SmoothReduction Pb H) (b : B) : ∃ p ∈ R.carrier, Pb.proj p = b := by
  obtain ⟨V, -, hb, σ, -, hσ⟩ := R.locSec b
  exact ⟨σ b, (hσ b hb).2, (hσ b hb).1⟩

/-- **Smooth local trivialisations of the reduction**: an `R`-valued smooth local section `σ`
and a smooth division map `τ` with `σ (proj p) · τ p = p`, and `τ p ∈ H` for `p ∈ R`. -/
theorem locTriv (R : SmoothReduction Pb H) (b : B) :
    ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ ∃ (σ : B → P) (τ : P → G),
      ContMDiffOn IB IP ∞ σ V ∧ (∀ y ∈ V, Pb.proj (σ y) = y ∧ σ y ∈ R.carrier) ∧
      ContMDiffOn IP IG ∞ τ (Pb.proj ⁻¹' V) ∧
      (∀ p ∈ Pb.proj ⁻¹' V, Pb.act (σ (Pb.proj p)) (τ p) = p) ∧
      ∀ p ∈ Pb.proj ⁻¹' V, p ∈ R.carrier → τ p ∈ H := by
  obtain ⟨V1, hV1, hb1, σ, hσ, hσp⟩ := R.locSec b
  obtain ⟨V2, hV2, hb2, σ', τ', -, -, hτ', hrec⟩ := Pb.locTriv b
  have key : ∀ p ∈ Pb.proj ⁻¹' (V1 ∩ V2),
      Pb.act (σ (Pb.proj p)) ((τ' (σ (Pb.proj p)))⁻¹ * τ' p) = p := by
    intro p hp
    have hy := (hσp _ hp.1).1
    have e1 : Pb.act (σ' (Pb.proj p)) (τ' (σ (Pb.proj p))) = σ (Pb.proj p) := by
      have := hrec (σ (Pb.proj p)) (by show Pb.proj _ ∈ V2; rw [hy]; exact hp.2)
      rwa [hy] at this
    calc Pb.act (σ (Pb.proj p)) ((τ' (σ (Pb.proj p)))⁻¹ * τ' p)
        = Pb.act (Pb.act (σ' (Pb.proj p)) (τ' (σ (Pb.proj p))))
            ((τ' (σ (Pb.proj p)))⁻¹ * τ' p) := by rw [e1]
      _ = Pb.act (σ' (Pb.proj p)) (τ' p) := by rw [Pb.act_mul, mul_inv_cancel_left]
      _ = p := hrec p hp.2
  refine ⟨V1 ∩ V2, hV1.inter hV2, ⟨hb1, hb2⟩, σ, fun p => (τ' (σ (Pb.proj p)))⁻¹ * τ' p,
    hσ.mono Set.inter_subset_left, fun y hy => hσp y hy.1, ?_, key, ?_⟩
  · have hs : ContMDiffOn IP IP ∞ (fun p => σ (Pb.proj p)) (Pb.proj ⁻¹' (V1 ∩ V2)) :=
      hσ.comp Pb.smooth_proj.contMDiffOn fun p hp => hp.1
    have h1 : ContMDiffOn IP IG ∞ (fun p => τ' (σ (Pb.proj p))) (Pb.proj ⁻¹' (V1 ∩ V2)) :=
      hτ'.comp hs fun p hp => by
        show Pb.proj (σ (Pb.proj p)) ∈ V2
        rw [(hσp _ hp.1).1]; exact hp.2
    exact h1.inv.mul (hτ'.mono fun p hp => hp.2)
  · intro p hp hpR
    show (τ' (σ (Pb.proj p)))⁻¹ * τ' p ∈ H
    set t := (τ' (σ (Pb.proj p)))⁻¹ * τ' p
    obtain ⟨h, hH, hh⟩ := R.transitive _ (hσp _ hp.1).2 p hpR (hσp _ hp.1).1
    have hrec' : Pb.act (σ (Pb.proj p)) t = p := key p hp
    have hfree : t * h⁻¹ = 1 := by
      apply Pb.free (σ (Pb.proj p))
      rw [← Pb.act_mul, hrec']
      calc Pb.act p h⁻¹ = Pb.act (Pb.act (σ (Pb.proj p)) h) h⁻¹ := by rw [hh]
        _ = σ (Pb.proj p) := by rw [Pb.act_mul, mul_inv_cancel, Pb.act_one]
    have : t = h := by
      calc t = t * h⁻¹ * h := by rw [inv_mul_cancel_right]
        _ = h := by rw [hfree, one_mul]
    rw [this]; exact hH

end SmoothReduction

end GU.Library
