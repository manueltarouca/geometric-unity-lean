# Geometric Unity: constraint audit and Lean 4 baseline

- `data/`: source draft (Weinstein, *Geometric Unity*, April 1 2021).
- `PHASE1_BLUEPRINT.md`: Phase 1 gap audit.
- `lean/`: Phase 2 Lean 4 + Mathlib (v4.35.0) baseline.

## Toolchain (workspace-local)
Everything lives under `.toolchain/`: elan, the Lean toolchain, and the Mathlib cache.
Shell profiles are untouched.

    source env.sh
    cd lean && lake build            # whole library
    lake env lean Audit.lean         # axiom audit: only propext / Classical.choice / Quot.sound

## Modules (all compile; `lake env lean Audit.lean` shows only propext / Classical.choice / Quot.sound)
| Area | Files | Headline results |
|---|---|---|
| Gauge (§5–7) | `GU/Gauge/Inhomogeneous.lean`, `MatrixModel.lean` | 𝒢 = 𝓗⋉N; Lemma 6.1/6.3/6.4 proved; the footnote-7 sign slip formalised (`no_common_section`) with a one-sign repair (`piPlus`); concrete non-abelian model |
| Observerse (§3) | `GU/Observerse/*.lean` | Y¹⁴ a global smooth manifold over any smooth X⁴ (Sym²(TX)); C = V ⊕ H* a smooth rank-14 bundle; fiber metric (7,7) and chart-covariant; chimeric metric has an orthogonal (7,7) basis at λ=1, transported to every (1,3) point |
| Signature (§3.1) | `GU/Geometry/Signature.lean` | DeWitt λ > 1/4 is needed for (6,4) |
| Spinors (§3.5–3.6) | `GU/Spinor/Gamma, Dirac, Basis, Faithful, DetOne, Checkerboard.lean` | Cl(7,7) ≃ₐ ℝ(128); ρ_D : Spin(7,7) → SO(64,64) ⊂ U(64,64), faithful, det 1; checkerboard (3.26)/(3.27) proved for all monomials |
| Calculus | `GU/Spinor/Pauli.lean`, `PSum.lean` | exact Pauli-string and linear-combination calculus with certified zero test |
| Reductions (§4) | `GU/Spinor/Branching, Reductions, Hypercharge, WeightSpaces, HyperchargeOp, SMAlgebra, Anomaly.lean` | Γ = ω₄ω₁₀; Pati–Salam 21/24; u(3,2) = centraliser of J (exactly 25) ⊃ u(3)⊕u(2), su(3)/su(2) closure; one SM generation (+ν^c) as eigenspaces of Ŷ, Q̂; sin²θ_W = 3/8; anomaly-free; group-level Pati–Salam (Spin6×Spin4)/ℤ₂ ⊂ Spin(7,7) (`PatiSalamGroup.lean`); Spin6, Spin4 are non-split double covers of block SO(6), SO(4) (`BlockSpin.lean`); Spin4 ≃* Mathlib's spinGroup of ℝ^{0,4}, Spin6 ≃* spinGroup of ℝ^{6,0} (`SpinIso.lean`, `SpinIso6.lean`); Spin4 ≃* Sp(1)×Sp(1), unit-quaternion pairs (`SpinQuat.lean`), Sp(1) ≃* SU(2), so Spin4 ≃* SU(2)×SU(2) (`SpinSU2.lean`); Spin6 ≃* SU(4) via the Λ²ℂ⁴ real form (`SpinSU4, Lambda2, SU4Det, SU4Onto.lean`) |
| Shiab (§8–9) | `GU/Shiab/Degrees, CliffordBianchi, Einstein, ShiabGU.lean` | 3-gamma and Lichnerowicz identities; Clifford core of (9.3) gives the Einstein tensor and kills Weyl; synthetic ⧉_GU |
| Fermions (§9.3, §12.9) | `GU/Fermion/Decoupling, Bilinear.lean` | chirality decoupling theorem; Spin-equivariant sesquilinear pairing S̸⊗S̸ → u(64,64) |
| Bundles (§3.6) | `GU/Bundle/*.lean`, `GU/Spinor/SpinCover.lean` | P_H with explicit ρ_D; GL(14) frames and O(7,7) orthonormal frames of C (set level); smooth GL(14) frame bundle; orthonormal frames closed, existing exactly over (1,3) points; covering map Spin(7,7) → SO(7,7) with kernel exactly ±1 and image exactly the spinor-norm kernel SO⁺(7,7) (index 2; `SpinImage.lean`), which is the identity component SO₀(7,7), both connected and path component (`SpinComponent.lean`). Smooth: the orthonormal frames over Y13 are a smooth principal O(7,7)-bundle (`frameBundle`), the adapted frames a smooth principal O(6,4)×O(1,3) sub-bundle (`adaptedBundle`); Spin(7,7) is a Lie group (`lieGroup_spin`). **Obstruction: for nonempty X there is no Spin⁺(7,7) structure over all of Y13** (`no_spinStructure_univ`: a metric loop has holonomy outside SO₀(7,7); a two-component Spin(7,7) is not excluded); spin structures exist only over smaller open W ⊂ Y13 (`exists_smoothSpin_near`, `smoothSpinBundle`, `exists_spinLiftData_gauge`). No clopen SO₀-reduction over Y13 either (`no_SO0_reduction_univ`). The time-orientation double cover `Ytilde` (general X, `TimeCover.lean`) resolves it for X = ℝ⁴: global frame, SO₀-reduction and Spin⁺(7,7) structure on the cover (`TimeCoverSpin.lean`). For every X the cover's frames have an SO₀-reduction (`redT_reduction`); over ℝ⁴ the frame and spin structure are smooth (`contMDiff_Ff`, `smoothCoverSpin`); for general X spin structures exist locally and from cocycle lifts, the global question needs w₂, not formalised. The non-identity component of our two-component model Spin⁺ × {1, ω} flips every Spin⁺-invariant spinor form (`flip_nonidentity`, `TwoComponent.lean`). See `EXPERT_NOTE.md` |
| Predictions | `GU/synthetic_predictions.lean` | contingent Z′, sector counts, RS kernel, forced hypercharge direction, signature selection (orthonormal (7,7) frames exist iff (1,3)), particle allocation of one chirality, Pati–Salam (Spin6×Spin4)/ℤ₂ acting only on the fibre |

Numerical experiments (`experiments/`, run with `uv run --with numpy python -I ...`): the Shiab/Einstein checks,
the deformation-complex symbol, self-adjointness, the Shiab-family search, and the trilemma.

Journals: `unbounded_discovery_log.md`, `unbounded_semigroup_log.md` (including corrections from independent reviews).

Gaps are supplied as explicit hypothesis structures or definitions tagged `AI_BREAKTHROUGH_PATCH_V1`, never as global `axiom`s.

## Findings so far (details and caveats in the logs)
**Confirmed (Lean):** Cl(7,7) ≅ ℝ(128); ρ_D faithful into SO(64,64) ⊂ U(64,64); the Clifford checkerboard (3.26)/(3.27) (footnote 3); Lemma 6.1/6.3/6.4; the chimeric metric is (7,7) at λ = 1 on (1,3) points; Γ = ω₄ω₁₀ (12.20); one SM generation (+ν^c) from N^{6,4} with sin²θ_W = 3/8, anomaly-free; the Clifford core of (9.3) kills Weyl and yields Einstein (mixed brackets), also with Hodge stars at n = 4 (every real algebraic curvature tensor, `einstein_all_real`); the Shiab equation with cosmological source implies G = Λg; §12.9 decoupling.

**Defects in the draft (Lean):** the footnote-7 sign slip (Lemmas 6.3 vs 7.2; one-sign repair given); the literal Frobenius metric gives (7,3) (needs DeWitt λ > 1/4); the (9.4) integrand has a dropped ⋆.

**Numerical (n = 4; Einstein check also at n = 6):** the printed (9.3) needs mixed brackets for Einstein. It is not formally self-adjoint (also a Lean witness), so (9.7) does not follow. The synthetic ⧉_GU (second term = sum of both bracket pairings) fixes the quadratic part, but the cubic Chern–Simons term still blocks (9.7) (Lean witness). More strongly, no Spin(4)-equivariant operator Ω² → Ω³ at n = 4 that outputs Einstein and is formally self-adjoint satisfies the cubic identity, for any coefficient. Weyl annihilation is automatic for every Def 8.1 Shiab (representation theory), so it is not a real constraint. Ellipticity of (10.1) is *achievable* (Euclidean, n = 4) once Def 8.1's twisted invariants Φ_r·ω are included. The earlier "trilemma" was an artefact of an incomplete family and is withdrawn.

**Retracted after review:** the "(9.3) degree defect" (a misread outer ⋆) and the "Einstein needs +½ at (7,7)" claim (convention artefact).

**Caveat (Pati–Salam blocks, FINDINGS §E2):** the blocks of `Spinor/PatiSalamGroup.lean` are an abstract
`(1,3) ⊕ (6) ⊕ (4)` split. Under the identification `Φ` with the chimeric bundle, `H*` is spanned by
`e₆, e₁₁, e₁₂, e₁₃`, so the old `W4` is mostly horizontal and the old "base" `e₀, e₇, e₈, e₉` is vertical.
Statements like "acts only on the fibre / does not mix with spacetime" (e.g. `gauge_embedding`'s reading)
hold for the `Φ`-aligned groups `PS6'`, `PS4'` (`Bundle/ChimReduction.lean`), not for the old blocks.
