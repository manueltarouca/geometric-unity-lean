# Machine-checked audit of the Geometric Unity draft: findings map (DRAFT)

Status: working notes towards a possible technical note. **Novelty is not checked.** In particular,
compare every item below with T. Nguyen and T. Polya, *A Response to Geometric Unity* (2021), and
the later public discussion before claiming anything is new. Every "Lean" item is a theorem in this
repository. All of them build with no `sorry` and depend only on `propext`, `Classical.choice` and
`Quot.sound` (`lake env lean lean/Audit.lean`). Equation numbers refer to the April 2021 draft.

Framing for any write-up: this verifies and audits an informal draft. It is not new physics, and
nothing here proves or refutes GU as a physical theory.

## A. Defects in the draft (Lean-checked)

| # | Claim | Paper | Lean |
|---|---|---|---|
| A1 | The gauge-action sign convention is inconsistent. Lemma 6.3 holds only with τ⁻ = (h, −h⁻¹dh); Lemmas 6.5/7.2 hold only with τ⁺. Repair: negate one sign. | §6–7, fn 7 | `no_common_section`, `pi_invariant_tau_neg`, `T_equivariant_tau_pos` (`Gauge/Inhomogeneous.lean`) |
| A2 | The literal Frobenius trace metric (3.8) gives signature (7,3)/(3,7), not the required (6,4). (6,4) needs the DeWitt supermetric with λ > 1/4. | (3.8)–(3.9) | `Geometry/Signature.lean`, `Observerse/Chimeric.lean` (`chim_signature`) |
| A3 | The expanded (9.4) integrand is a 2-form, so a ⋆ was dropped. The L² pairing on its first line is correct. | (9.4) | `Shiab/Degrees.lean` |
| A4 | The printed Shiab (9.3), with Einstein-type brackets, is **not formally self-adjoint**, so (9.7) does not follow from (9.4). | (9.3), (9.7) | `not_selfadjoint` (`Shiab/FormsWitness.lean`) |
| A5 | Even for a synthetic Shiab that fixes A4, the cubic Chern–Simons term blocks (9.4) → (9.7). | (9.4), (9.7) | `cubic_fails` (`Shiab/FormsCubic.lean`) |
| A6 | The deformation complex (10.1) is **not exact** at the symbol level for the printed Shiab, so it is not elliptic as printed. | (10.1) | `sigma2_kills`, `not_in_image` (`Shiab/DeformationWitness.lean`) |
| A7 | Spin(14,ℂ) → U(128,ℂ) in (3.20) is type-incorrect as written; the real form Spin(7,7) → U(64,64) is meant. | (3.20) | blueprint note (no Lean theorem needed) |

## B. Draft claims confirmed (Lean-checked)

| # | Claim | Paper | Lean |
|---|---|---|---|
| B1 | Cl(7,7) ≅ ℝ(128), and ρ_D is faithful. | (3.18), (3.28) | `cliffordRep_bijective`, `rhoD_injective` (`Spinor/Faithful.lean`) |
| B2 | (9.3) has correct degrees once the outer ⋆ over the ½ is read correctly. An earlier "degree defect" was retracted. | (9.3) | `draft93_ok` (`Shiab/Degrees.lean`) |
| B3 | The Clifford core of (9.3) kills Weyl and yields the Einstein tensor, but **only with mixed brackets** (commutator in the Ricci term, anticommutator in the scalar term). | §9.1 | `shiab_einstein` (`Shiab/Einstein.lean`); with Hodge stars at n = 4 on a 55-tensor spanning set: `einstein_all`, for every integer algebraic curvature tensor: `einstein_all_curv` (`Shiab/FormsCurvSpan.lean`), and for every real one: `einstein_all_real` (`Shiab/FormsRealCoords.lean`) |
| B4 | The Shiab equation with a cosmological source gives G = Λg. | (9.9)–(9.10) | `einstein_equation` (`Shiab/EinsteinEquation.lean`) |
| B5 | One SM generation (+ν^c) from the (6,4) branching, anomaly-free, with sin²θ_W = 3/8. | §11–12 | `anomaly_free`, `weinberg_angle`, `particle_allocation` |
| B6 | The hypercharge direction is forced. | §11.3 | `hypercharge_forced` (`synthetic_predictions.lean`) |
| B7 | (3.27) is right as a linear statement: under the split form C, u(64,64) = real Λ^{4i+1}, Λ^{4i+2} ⊕ i·Λ^{4i}, Λ^{4i+3} (the placement of i is forced), and the identification Cl(7,7) → u(64,64) is Spin(7,7)-equivariant. Λ^k = span of k-blades; Chevalley map not formalised. | (3.27) | `Ψu_blade`, `star_blade`, `uEquiv`, `Ψu_equivariant` (`Spinor/LieU6464.lean`) |

## C. Precise statements of things the draft leaves implicit (Lean-checked)

| # | Statement | Lean |
|---|---|---|
| C1 | **Signature selection.** Orthonormal (7,7) frames of the chimeric bundle exist exactly over the (1,3) points of Y, never over the (3,1) points. Y splits as (1,3) ⊔ (3,1). | `ortho_iff_13`, `no_ortho_31`, `lorentz_dichotomy`, `signature_selected` |
| C2 | The image of Spin(7,7) in O(7,7) is exactly SO⁺ (the spinor-norm kernel), of index 2 in SO. It equals the identity component SO₀, both connected and path component. | `range_vecRep`, `cc_iff_spin` |
| C3 | Pati–Salam at the group level. Spin6 and Spin4 inside Spin(7,7) commute and meet in ±1. Spin6 ≅ Mathlib's Spin(6) ≅ SU(4); Spin4 ≅ SU(2) × SU(2). | `product_kernel`, `spin6Equiv`, `Spin6SU4`, `spin4SU2Equiv` |
| C4 | Hypercharge circle U(1)_Y ⊂ Spin(7,7) has minimal period π. The maximal torus kernel on U(1)⁵ is (ℤ/2)⁴. | `U1Y_eq_one_iff`, `torusKer_quot_equiv_four` |

## D. Underspecified in the draft (not formalisable as stated)

The Shiab family in (8.1) is only a template. The operator D_ω in (9.6) is not given. The fermionic
quadrant of (9.16) is left open. Integration over the non-compact fibres of Y is unaddressed. There
is no anomaly-cancellation mechanism. The global spin structure (w₂) is not discussed. (External, unverified: disruptionjoe/gu-formalization `canon/w2-y14-spin-structure.md`
argues w₂(Y¹⁴) = π*w₂(X⁴), i.e. Y spin iff X spin, with only the mod-2 polynomial identities in Lean;
they retracted an earlier, unconditional version.) Details:
`PHASE1_BLUEPRINT.md`, "Omitted constructs".

## E. Not done / open

- The global spin lift (w₂).
- The submanifold structure of the orthonormal frames.

## Literature comparison (first pass, 2026-10-31)

Source read: T. Nguyen, T. Polya, *A Response to Geometric Unity*, 23 February 2021
(files.timothynguyen.org/geometric_unity.pdf). It analyses the 2013/2020 **video** presentation and
predates the April 2021 draft that this audit targets. Its objections:
1. the Shiab operator needs an unannotated complexification (u(128) ≇ Λ•T*U over ℝ);
2. U(128) as the gauge group gives an abelian chiral anomaly, and removing it via Spin(14) kills
   the Shiab;
3. supersymmetry in d = 14 forces higher-spin fields;
4. missing details: "certain differential forms are exact", "sign calculations work out"; recovering
   4d physics.
It also notes that spinors still need a metric or connection on U, and that a spin structure
needs w₂(TU) = 0.

Status of our items relative to it:
- **Addresses or sharpens objection 1:** B1 and B7. In the draft, signature (7,7) gives
  Cl(7,7) ≅ ℝ(128) real and u(64,64) of dimension 16384 = 2¹⁴ = dim Λ•. So the dimension mismatch
  behind objection 1 is removed in the draft. Whether the draft's i-factor placement makes the
  isomorphism equivariant is now checked at the linear level: B7 (the i placement in (3.27) is
  correct and Spin(7,7)-equivariant). This does **not** resolve objection 1 itself, which concerns
  the Shiab *operator*: Clifford products of u-elements leave u (Λ¹·Λ² ∋ Λ³, whose u-slot is
  imaginary), so the operator still needs an i inserted by hand (compare B3's anticommutator).
- **Known (N–P):** anomaly concerns (objection 2; our blueprint row "anomaly cancellation absent");
  w₂ / spin structure (our open item E); "spinors need a choice of connection" (our blueprint B5,
  "semi-canonical").
- **Not in N–P, and plausibly new** (they predate the draft and treat these points only generically
  under "omissions"): A1 (§6–7 sign inconsistency, with an explicit repair), A2 ((7,3) vs (6,4)),
  A3, A4 (printed Shiab not self-adjoint), A5 (cubic obstruction), A6 (deformation complex not
  exact), B3 (Einstein only with mixed brackets), B4, C1 (signature selection: (1,3) points only),
  C2–C4 (group-level structure).
- A search for detailed technical critiques of the April 2021 draft itself found none (only
  popular-press summaries). This is a weak negative.
- Second pass (web search, arXiv / MathOverflow / Physics StackExchange): no technical analysis of
  the April 2021 draft found. Hits are forum threads (r/ThePortal, scienceforums.net, Physics
  Forums), Substack explainers, and unreliable "rescue" papers (academia.edu, gsjournal). One search
  summary claimed Nguyen–Polya is arXiv:2106.07852; **checked: false** (that ID is an unrelated CV
  paper), so cite the PDF URL instead. Still recommended before posting: ask a GU-literate
  physicist and check Weinstein's own later responses or talks.

## Before any publication

1. ~~Read Nguyen–Polya (2021)~~ done. ~~Wider web search~~ done (nothing found). Remaining: an expert who follows GU confirms nothing is missed.
2. Get an independent read by a mathematician or physicist, to check that each formal statement
   matches the intended reading of the draft. That matters most for A1, A4–A6 and B3, which depend
   on bracket and sign conventions.
3. Pin the exact draft version and equation numbering.
