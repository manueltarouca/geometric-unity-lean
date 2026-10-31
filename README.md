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
| Observerse (§3) | `GU/Observerse/Manifold.lean`, `Chimeric*.lean` | Y¹⁴ locally a smooth manifold; chimeric metric has an orthogonal (7,7) basis at λ=1, transported to every (1,3) point |
| Signature (§3.1) | `GU/Geometry/Signature.lean` | DeWitt λ > 1/4 is needed for (6,4) |
| Spinors (§3.5–3.6) | `GU/Spinor/Gamma, Dirac, Basis, Faithful, DetOne, Checkerboard.lean` | Cl(7,7) ≃ₐ ℝ(128); ρ_D : Spin(7,7) → SO(64,64) ⊂ U(64,64), faithful, det 1; checkerboard (3.26)/(3.27) proved for all monomials |
| Calculus | `GU/Spinor/Pauli.lean`, `PSum.lean` | exact Pauli-string and linear-combination calculus with certified zero test |
| Reductions (§4) | `GU/Spinor/Branching, Reductions, Hypercharge, WeightSpaces, HyperchargeOp, SMAlgebra, Anomaly.lean` | Γ = ω₄ω₁₀; Pati–Salam 21/24; u(3,2) (≥25) ⊃ u(3)⊕u(2); one SM generation (+ν^c) as eigenspaces of Ŷ, Q̂; sin²θ_W = 3/8; anomaly-free |
| Shiab (§8–9) | `GU/Shiab/Degrees, CliffordBianchi, Einstein, ShiabGU.lean` | 3-gamma and Lichnerowicz identities; Clifford core of (9.3) gives the Einstein tensor and kills Weyl; synthetic ⧉_GU |
| Fermions (§9.3, §12.9) | `GU/Fermion/Decoupling, Bilinear.lean` | chirality decoupling theorem; Spin-equivariant sesquilinear pairing S̸⊗S̸ → u(64,64) |
| Bundles (§3.6) | `GU/Bundle/*.lean` | P_H as a principal U(64,64)-bundle with the explicit ρ_D (spin structure on C is a hypothesis) |
| Predictions | `GU/synthetic_predictions.lean` | contingent Z′, sector counts, RS kernel, forced hypercharge direction |

Numerical experiments (`experiments/`, run with `uv run --with numpy python -I ...`): the Shiab/Einstein checks,
the deformation-complex symbol, self-adjointness, the Shiab-family search, and the trilemma.

Journals: `unbounded_discovery_log.md`, `unbounded_semigroup_log.md` (including corrections from independent reviews).

Gaps are supplied as explicit hypothesis structures or definitions tagged `AI_BREAKTHROUGH_PATCH_V1`, never as global `axiom`s.

## Findings so far (details and caveats in the logs)
**Confirmed (Lean):** Cl(7,7) ≅ ℝ(128); ρ_D faithful into SO(64,64) ⊂ U(64,64); the Clifford checkerboard (3.26)/(3.27) (footnote 3); Lemma 6.1/6.3/6.4; the chimeric metric is (7,7) at λ = 1 on (1,3) points; Γ = ω₄ω₁₀ (12.20); one SM generation (+ν^c) from N^{6,4} with sin²θ_W = 3/8, anomaly-free; the Clifford core of (9.3) kills Weyl and yields Einstein (mixed brackets); §12.9 decoupling.

**Defects in the draft (Lean):** the footnote-7 sign slip (Lemmas 6.3 vs 7.2; one-sign repair given); the literal Frobenius metric gives (7,3) (needs DeWitt λ > 1/4); the (9.4) integrand has a dropped ⋆.

**Numerical (n = 4; Einstein check also at n = 6):** the printed (9.3) needs mixed brackets for Einstein. It is not formally self-adjoint (also a Lean witness), so (9.7) does not follow. The synthetic ⧉_GU (second term = sum of both bracket pairings) fixes the quadratic part, but the cubic Chern–Simons term still blocks (9.7) (Lean witness). More strongly, no Spin(4)-equivariant operator Ω² → Ω³ at n = 4 that outputs Einstein and is formally self-adjoint satisfies the cubic identity, for any coefficient. Weyl annihilation is automatic for every Def 8.1 Shiab (representation theory), so it is not a real constraint. Ellipticity of (10.1) is *achievable* (Euclidean, n = 4) once Def 8.1's twisted invariants Φ_r·ω are included. The earlier "trilemma" was an artefact of an incomplete family and is withdrawn.

**Retracted after review:** the "(9.3) degree defect" (a misread outer ⋆) and the "Einstein needs +½ at (7,7)" claim (convention artefact).
