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

## Modules
| File | Content |
|---|---|
| `GU/Gauge/Inhomogeneous.lean` | 𝒢 = 𝓗 ⋉ N, τ_c, actions, π, μ, T; sign slip of footnote 7 formalised, with a one-sign repair (`piPlus`) |
| `GU/Geometry/Signature.lean` | DeWitt λ: trace norm 4−16λ (gap M1); Q(7,7), Spin(7,7), ϑ, Clifford counts |
| `GU/Geometry/IndefUnitary.lean` | U(p,q) group, H = U(64,64) |
| `GU/Bundle/Principal.lean` | set-level principal bundles, extension P ×_ρ K |
| `GU/Bundle/MainBundle.lean` | P_H as a principal U(64,64)-bundle using the explicit ρ_D (`physicalBundle`); spin structure still a hypothesis |
| `GU/Shiab/Degrees.lean` | degree audit: (9.3) is correct, the (9.4) integrand has a typo; typed (9.3); equivariance theorem |
| `GU/Spinor/Gamma.lean` | 128×128 gamma matrices; Cl(7,7) → ℝ(128) algebra hom |
| `GU/Spinor/Dirac.lean` | spinor form C (3.24), chirality Γ, ρ_D : Spin(7,7) → U(C) |
| `GU/Spinor/Basis.lean` | U(C) ≃* U(64,64) via P = (1 + CD)/√2 |
| `GU/Spinor/Faithful.lean` | Cl(7,7) ≃ₐ ℝ(128) (3.18); ρ_D injective (3.28) |

Gaps are supplied as explicit hypothesis structures (`ChimericSpinStructure`, `DiracRep`,
`GaugeData`, `GradedForms`, `GaugeOnForms`); `DiracRep` now has a constructed instance, `diracRep`, never as global `axiom`s.
