# A time-orientation obstruction in the Geometric Unity chimeric bundle: note for an expert

Lean 4 / Mathlib audit of the April 2021 draft (`data/Geometric_Unity-Draft-April-1st-2021.pdf`). Everything
marked **Lean** compiles with no `sorry` and standard axioms only (`lean/Audit.lean`). Everything marked
**informal** is not machine-checked. We make no claim that any of this is new.

## Setting

Y¹³ is the bundle over a 4-manifold X of metrics of signature (1,3). The chimeric bundle C = V ⊕ π\*T\*X carries
a natural metric of signature (7,7). The draft builds P_H from "the double cover of the frame bundle of the
Chimeric bundle" (p. 24, (3.32)) and maps Spin(7,7) into U(64,64) ((3.28)). It never mentions time
orientation or a component of SO(7,7).

## The obstruction

Rotate the timelike axis by π in one fibre: G(θ) = R(θ) η R(θ)ᵀ, θ ∈ [0, π]. This is a closed loop of metrics,
for any X. It is not closed on frames: the frame holonomy is a diagonal element gHol with determinant 1 whose
positive 7×7 block has determinant −1, so gHol ∉ SO₀(7,7).

**Lean, for every nonempty X, including ℝ⁴:**
- `no_SO0_reduction_univ`: no clopen set of (7,7)-orthonormal frames over all of Y¹³ is SO₀-stable and meets
  each fibre in exactly one SO₀-coset. No spin group appears in this statement.
- `no_spinStructure_univ`: no principal Spin⁺(7,7)-bundle over all of Y¹³ maps equivariantly to those frames.

**Informal reading.** The Lorentzian fibre retracts to RP³ (Steenrod, cited by Torre, hep-th/9706092, §7). The
timelike line L is tautological with w₁(L) ≠ 0, and C⁺ ≅ V⁺ ⊕ L\* with V⁺ orientable, so w₁(C⁺) ≠ 0. This sits
upstream of w₂, and it is compatible with the external, unverified claim w₂(TY) = π\*w₂(X).

**Spin structures on smaller sets (Lean).** They exist near every point and over {G₀₀ > 0} for X = ℝ⁴, and that
locus is the largest open set invariant under the stabiliser of the line of dx⁰ carrying one, and likewise for global
frames (`gauge_largest_iff`). Over ℝ⁴ the base of a spin structure cannot contain all of {G₀₀ < 0} in a fibre
(`no_spinStructure_of_neg_fibre`). They are
not unique: over the part of that locus off a plane in ℝ⁴, which is not simply connected, two spin structures on
the same frames are not isomorphic (`not_iso_holeSpin`).

## The double-cover resolution

**Lean, for general X.** `Ytilde X`, the space of metrics with a choice of future cone of timelike covectors, is
a two-sheeted covering of Y¹³ (`isCoveringMap_tilde`, `ncard_fibre`), a smooth manifold (`isManifold_tilde`), and
Hausdorff when X is (`t2_Ytilde`). The loop above does not lift to a closed loop (`no_closed_lift`), and the
cover has no section (`no_section`). **The pulled-back frames have a clopen SO₀-reduction, for every X**
(`redT_reduction`): every orthochronous Lorentz transformation acts on frames through SO₀ (`lorO_mem_SO0`).

**Lean, for X = ℝ⁴.**
- The frames pulled back to the cover have a clopen SO₀-reduction (`exists_SO0_reduction_cover`). It does not
  descend: the two sheets over a point lie in different SO₀-orbits (`deck_not_SO0`).
- There is a global frame of C on the cover (`exists_frame_tilde`), and hence a Spin⁺(7,7) structure over the
  whole cover (`coverSpin`), with map to the frames two-to-one onto the reduction (`coverSpin_Φ_eq_iff`,
  `range_coverSpin`).
- The frame uses a smooth future covector g (smooth partition of unity on convex cones, so not fully explicit)
  and the matrix with rows 1·g, i·g, j·g, k·g (quaternion products; informally, the parallelisation of S³). It
  is smooth (`contMDiff_Ff`), and the spin structure is a smooth principal bundle (`smoothCoverSpin`).

**General X, spin structure.** Local spin structures compatible with the reduction exist near every point
(`exists_local_spin_cover`); the SO₀ transition cocycle of chart frames has a {±1} defect (`cover_defect_mem`),
and continuous cocycle lifts give a global structure (`exists_coverSpin_of_lifts`). Whether the defect class
(informally w₂ of the reduction) vanishes for a given X is open; it may fail for some X (informal), and w₂ is not
in Mathlib.

## What is proved and what is not

| Statement | Status |
|---|---|
| Holonomy, no SO₀-reduction, no Spin⁺ structure over Y¹³, for the chimeric metric as formalised | Lean |
| Double cover and its SO₀-reduction, general X; smooth global frame and Spin⁺ structure, X = ℝ⁴ | Lean |
| Non-isomorphic spin structures over a non-simply-connected open set | Lean |
| Fibre ≃ RP³, cover fibre ≃ S³, w₁(C⁺) ≠ 0, cones are connected components | Informal; w₁ and w₂ are not defined in the repo |
| The Spin⁺ reading of the draft's "double cover" | Our interpretation; the draft does not say |
| A two-component Spin(7,7) over Y¹³ | Neither excluded nor constructed |
| Non-identity component flips the spinor forms | Lean (`flip_nonidentity`, `flip_omega`; instance `isInvariant_formC`) |
| Spin structure on the cover for general X | Local and from cocycle lifts: Lean; global: open (w₂) |

We searched for prior statements and did not find that the (7,7) bundle over Lorentzian metrics is not
time-orientable, nor a critic treating the SO₀ reduction (`FINDINGS.md`, a weak negative from open-web searches).

## Questions for an expert

1. **Is this known?** Has the failure of time orientability for the chimeric or DeWitt-type (7,7) bundle over the
   full space of Lorentzian metrics been stated anywhere?
2. **Which group is meant?** Does the draft intend the connected Spin⁺(7,7) or the two-component group? A
   two-component structure is not excluded by our result, but in Lean (`TwoComponent.lean`) the group
   Spin⁺(7,7) × {1, ω} (ω a volume element; our model of the two-component group, `emb_injective`) maps to
   O(7,7) with kernel ±1 onto SO₀ ∪ (−1)·SO₀ inside det = 1 (`toO_ker`, `range_toO`, `det_toO`; that this is all
   of SO(7,7) is not formalised), and its non-identity component changes the sign of every Spin⁺-invariant
   bilinear form on the Dirac module (`flip_nonidentity`). So in the Clifford action it does not land in
   U(64,64) as (3.28) requires (informal step from the sign flip). Informally, twisting S⁻ by the sign character is ρ∘pr, pr killing ω: isometric, but equivariant only
   for a vector action through SO₀, which forgets exactly the component gHol lies in. The draft reaches (3.28)
   "by exponentiation" (p. 23), which gives only the identity component. Is that the right reading, and is there a way round it?
3. **Is the fibre notation the resolution?** The draft writes the fibre as GL̃(4,ℝ)/Spin(1,3) ((3.33), (3.38),
   (12.1), p. 54). Informally: reading GL̃ as GL̃⁺(4,ℝ) since X is oriented (p. 4; the "connected" double cover of
   GL(N,ℝ) on p. 20 cannot be literal), and Spin(1,3) as the Sl(2,ℂ) that the opening table uses for the Lorentz group,
   this is GL⁺(4,ℝ)/SO₀(1,3) ≃ S³ and describes
   time-oriented metrics: the cover, not the space of metrics it defines Y by. With the two-component group it is
   RP³. Which is meant, and does Geometric Unity accept a time orientation as data, given p. 25: "all that has
   been chosen is the signature"?
4. **Does the cover cost anything?** A section of the cover over X is a time-oriented metric, so only time-orientable
   observations pull back. Is this physically acceptable, and does anything downstream in the draft need to change?
5. **General X.** The reduction on the cover exists for every X (Lean). What is the exact condition on X for
   the spin structure on the cover (presumably w₂ of the reduction, related to w₂(X))?
