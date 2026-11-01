# A machine-checked audit of the 2021 Geometric Unity draft (DRAFT, not for circulation)

> Status: working draft, generated from `FINDINGS.md`. **Not checked by a domain expert, and
> novelty is not established beyond a first literature pass** (see §7). Do not post before both are
> done. Every formal claim cites a Lean 4 theorem in this repository. All of them build with no
> `sorry` and depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`;
> run `lake env lean lean/Audit.lean`).

## Abstract (draft)

We formalise in Lean 4 + Mathlib the mathematical skeleton of E. Weinstein's April 2021 draft
*Geometric Unity* (GU), and use the proof assistant as an auditor. Machine-checked results cover:
- the observerse Y¹⁴ → X⁴ and the chimeric bundle with its (7,7) metric;
- the spinor representation (Cl(7,7) ≅ ℝ(128), with ρ_D faithful);
- the inhomogeneous gauge group;
- the Pati–Salam reduction at the group level (Spin(6) ≅ SU(4), Spin(4) ≅ SU(2) × SU(2), and
  Spin(7,7) → SO₀(7,7));
- the Clifford core of the Shiab operator.

The same process exposes several concrete defects in the draft as printed:
- a sign inconsistency in the gauge-action lemmas of §6–7;
- a signature mismatch in the fibre metric (3.8);
- a dropped Hodge star in (9.4);
- non-self-adjointness of the printed Shiab (9.3), and a cubic obstruction to (9.4) ⇒ (9.7);
- non-exactness of the deformation complex (10.1) at the symbol level.

We also make precise points the draft leaves implicit. The chimeric (7,7) structure admits
orthonormal frames exactly over the (1,3) points of Y, so Lorentzian signature is *selected*. And
the printed Shiab, with Hodge stars, outputs the Einstein tensor for every algebraic curvature
tensor (n = 4, Euclidean), but only with mixed bracket conventions. And no Spin⁺(7,7) structure on
the chimeric bundle exists over the whole (1,3) observerse, for any nonempty X (§4). We do not claim to prove or
refute GU as physics.

## 1. Introduction (outline)
- GU as an informal proposal; the 2021 draft; the Nguyen–Polya response (Feb 2021, on the video
  presentation).
- Why a proof assistant: every claim is reduced to a mechanically checked statement, and gaps
  surface as unprovable goals or explicit counterexamples.
- Scope and non-goals: classical, pre-quantum; no claims about physical correctness.

## 2. Formal setting
- Lean 4 v4.35, Mathlib; workspace layout; the axiom audit; the policy of no `sorry`, no project
  axioms, and draft-gap repairs stated as explicit hypotheses.
- Representations: the Clifford algebra via an explicit 128-dimensional Pauli-string model
  (`cliffordRep_bijective`); Spin(7,7) as Mathlib's `spinGroup`.

## 3. What holds (confirmed claims)
- B1: Cl(7,7) ≅ ℝ(128), with ρ_D faithful. B2: the degrees of (9.3) are correct once the outer ⋆
  is read correctly.
- B3: Shiab → Einstein, with mixed brackets: the Clifford core (`shiab_einstein`), and with Hodge
  stars for every real algebraic curvature tensor (`einstein_all_real`, via `einstein_all_curv`, `einstein_span`
  and `curv_span`).
- B4: Shiab with a cosmological source gives G = Λg. B7: (3.27) verified (placement of i, Spin(7,7)-equivariance). B5–B6: one Standard Model generation,
  anomaly-free, sin²θ_W = 3/8, with the hypercharge direction forced.

## 4. Group-level structure made precise
- No Spin⁺(7,7) structure over all of the (1,3) observerse for nonempty X: a closed loop of Lorentzian
  metrics in one fibre has frame holonomy outside SO₀(7,7) (`no_spinStructure_univ`, `qLoop_pi`). A
  two-component Spin(7,7) is not excluded. Spin structures exist over smaller open sets (`exists_spinStructure_near`, `exists_smoothSpin_near`), and need not be unique (`not_iso_holeSpin`).
- The same holonomy excludes any clopen SO₀-reduction of the frames over all of Y13 (`no_SO0_reduction_univ`).
- On the time-orientation double cover of Y13 (general X: `isCoveringMap_tilde`, `isManifold_tilde`, `no_closed_lift`) the obstruction disappears for X = ℝ⁴: a global frame, an SO₀-reduction and a Spin⁺(7,7) structure exist (`exists_frame_tilde`, `exists_SO0_reduction_cover`, `coverSpin`), all smooth (`contMDiff_Ff`, `smoothCoverSpin`). The SO₀-reduction on the cover exists for every X (`redT_reduction`); for general X spin structures exist locally and from continuous cocycle lifts (`exists_coverSpin_of_lifts`). For every parallelisable X (frame given in charts) there is a Spin⁺(7,7) structure on the whole cover (`exists_coverSpin_parallel`; instances ℝ⁴ and ℝ⁴ minus a plane). For general X, given continuous lifts of the transitions on a fixed cover (assumed, not constructed), the ℤ/2 Čech class of their defect is independent of the lifts and vanishes iff they can be corrected to cocycle lifts, which give a structure (`defZ_indep`, `isCobdy_defZ_iff`); its identification with w₂ is informal. Over ℝ⁴ the spinor bundle P̃ ×_ρD ℂ^{64,64} exists on the cover with its U(64,64) form (`SpinorBundle`, `spinorForm_mk`), a first step towards P_H. Our two-component model Spin⁺ × {1, ω} has a non-identity component that flips every invariant spinor form (`flip_nonidentity`), and maps onto all of SO(7,7) (`range_toO_eq`). Questions for an expert: `EXPERT_NOTE.md`.
- Spin(7,7) → SO(7,7) has kernel ±1, and its image is exactly SO₀(7,7), both connected and path
  component (`range_vecRep`, `cc_iff_spin`).
- Pati–Salam:
  - Spin6 ≅ Spin(6) ≅ SU(4) (`spin6Equiv`, `Spin6SU4`);
  - Spin4 ≅ Spin(0,4) ≅ Sp(1)² ≅ SU(2)² (`spin4Equiv`, `spin4QuatEquiv`, `spin4SU2Equiv`);
  - Spin6 ∩ Spin4 = ±1 (`product_kernel`).
- The hypercharge circle has period π; the maximal torus kernel is (ℤ/2)⁴.
- Signature selection: orthonormal (7,7) frames exist exactly over the (1,3) points
  (`ortho_iff_13`, `no_ortho_31`).

## 5. Defects in the draft as printed
For each item: the statement in the draft, the formal counterexample or mismatch, and (where it
exists) the one-line repair.
- A1: the τ sign convention (§6–7, fn 7); repair by negating one term.
- A2: (3.8) gives (7,3); (6,4) needs the DeWitt parameter λ > 1/4.
- A3: (9.4) integrand.
- A4–A5: self-adjointness and the cubic obstruction.
- A6: deformation complex symbol sequence.
- A7: (3.20) typing.

## 6. Underspecified constructs
The Shiab family (8.1); D_ω in (9.6); the fermionic quadrant (9.16); integration over the
non-compact fibres; no anomaly-cancellation mechanism; the global spin structure. As formalised, no
Spin⁺(7,7) structure exists over all of the (1,3) observerse for any nonempty X
(`no_spinStructure_univ`: a loop of Lorentzian metrics in one fibre has holonomy outside SO₀(7,7));
one exists over smaller open sets, and one exists over the whole time-orientation double cover for
every parallelisable X (`coverSpin`, `exists_coverSpin_parallel`). A two-component Spin(7,7) is not excluded, and w₂ itself is not formalised.

## 7. Relation to prior critiques (to be completed by an expert)
- Nguyen–Polya (2021):
  - Complexification of the Shiab: the draft's (7,7) real form removes the dimension mismatch
    (u(64,64) has dimension 2¹⁴), and the linear identification (3.27) is verified with its placement
    of i and is Spin(7,7)-equivariant (B7). Their point that Clifford multiplication leaves u(64,64)
    stands for the Shiab operator.
  - Chiral anomaly: overlaps with §6.
  - Supersymmetry: out of scope.
- No published technical analysis of the April 2021 draft was found (web search; weak negative).
- TODO: an expert to confirm (i) there is no missed literature and (ii) the formal readings match
  the draft's intent, especially A1, A4–A6 and B3, which depend on conventions.

## 8. Reproducibility
Repository commit hash (TODO: pin); build instructions (`source env.sh; lake build`, building the
19 heavy `Shiab/FE` files sequentially); `lean/Audit.lean`; generator scripts in `lean/scripts/f2/`.

## Appendix: claim → theorem map
See `FINDINGS.md` (kept in sync with this draft).

---
© 2026 Manuel Tarouca. Licensed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/).
