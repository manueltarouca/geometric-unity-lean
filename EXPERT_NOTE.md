# A time-orientation obstruction in the Geometric Unity chimeric bundle: note for an expert

Lean 4 / Mathlib audit of E. Weinstein's *Geometric Unity* draft of April 1, 2021 (not redistributed here). Everything
marked **Lean** compiles with no `sorry` and standard axioms only (`lean/Audit.lean`). Everything marked
**informal** is not machine-checked. We do not claim novelty.

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

**Spin structures on smaller sets (Lean).** They exist near every point and over {G₀₀ > 0} for X = ℝ⁴
(`gauge_largest_iff`), never over all of {G₀₀ < 0} in a fibre (`no_spinStructure_of_neg_fibre`), and are
not unique off a plane in ℝ⁴ (`not_iso_holeSpin`).

## The double-cover resolution

**Lean, for general X.** `Ytilde X`, the space of metrics with a choice of future cone of timelike covectors, is
a two-sheeted covering of Y¹³ (`isCoveringMap_tilde`, `ncard_fibre`), a smooth manifold (`isManifold_tilde`), and
Hausdorff when X is (`t2_Ytilde`). The loop above does not lift to a closed loop (`no_closed_lift`), and the
cover has no section (`no_section`). **The pulled-back frames have a clopen SO₀-reduction, for every X**
(`redT_reduction`): every orthochronous Lorentz transformation acts on frames through SO₀ (`lorO_mem_SO0`).

**Lean, for X = ℝ⁴.**
- The reduction does not descend: the two sheets over a point lie in different SO₀-orbits (`deck_not_SO0`).
- A global frame of C on the cover (`exists_frame_tilde`) gives a Spin⁺(7,7) structure over the whole
  cover (`coverSpin`), mapping two-to-one onto the reduction (`coverSpin_Φ_eq_iff`, `range_coverSpin`).
- The frame (a smooth future covector and a quaternion trivialisation) is smooth (`contMDiff_Ff`), and so is
  the spin structure (`smoothCoverSpin`). The spinor bundle P̃ ×_ρD ℂ^{64,64} with its U(64,64) form exists
  on the cover; P_H is a topological principal bundle there and (3.36) holds, reading ϱ_D on P_H as the defining representation (`CoverPH.lean`).

**General X, spin structure.** Local spin structures compatible with the reduction exist near every
point (`exists_local_spin_cover`). If TX has a continuous global frame, there is one over the whole cover
(`exists_coverSpin_parallel`; e.g. ℝ⁴ minus a plane, not simply connected). In general, given
continuous lifts of the transitions on a fixed cover (assumed), the ℤ/2 Čech class of their
defect does not depend on them and vanishes iff they can be corrected to cocycle lifts, which give a global
structure (`defZ_indep`, `isCobdy_defZ_iff`). Its identification with w₂: informal. The sheet swap lifts to no Spin⁺ structure with image the reduction
(`no_deck_lift`); composed with gHol (non-identity component) it preserves the reduction.

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
| Spin structure on the cover | Parallelisable X: Lean; general X: a ℤ/2 class (Lean, fixed cover, lifts assumed), its vanishing open |
| Spinor bundle and P_H (topological) on the cover, X = ℝ⁴; (3.36) | Lean (ϱ_D on P_H: our reading) |

We found no prior statement that the (7,7) bundle over Lorentzian metrics is not time-orientable, nor a
critic treating the SO₀ reduction (`FINDINGS.md`; open-web searches only).

## Questions for an expert

1. **Is this known?** Has the failure of time orientability for the chimeric or DeWitt-type (7,7) bundle over the
   full space of Lorentzian metrics been stated anywhere?
2. **Which group is meant?** Does the draft intend the connected Spin⁺(7,7) or the two-component group? A
   two-component structure is not excluded by our result, but in Lean (`TwoComponent.lean`) the group
   Spin⁺(7,7) × {1, ω} (ω a volume element; our model of the two-component group, `emb_injective`) maps to
   O(7,7) with kernel ±1 onto SO₀ ∪ (−1)·SO₀ inside det = 1 (`toO_ker`, `range_toO`, `det_toO`), which is
   all of SO(7,7) (`range_toO_eq`), and its non-identity component changes the sign of every Spin⁺-invariant
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
   the spin structure on the cover (presumably w₂ of the reduction, related to w₂(X))? It holds when TX is
   trivial (Lean).

---
© 2026 Manuel Tarouca. Licensed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/).
