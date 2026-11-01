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
| C5 | **No Spin⁺(7,7) structure (and, more strongly, no cocycle lift, `SpinLiftData`) exists over the full (1,3) observerse, for any nonempty X, including ℝ⁴.** Rotating the timelike axis by π in one fibre gives a closed loop of Lorentzian metrics whose frame holonomy reverses the orientation of the positive 7-plane (positive-block determinant −1; determinant 1 overall, `det_gHol`), so it lies outside SO₀(7,7). The same holonomy excludes any clopen SO₀(7,7)-reduction of the frames over all of Y13, a statement with no spin group in it (`no_SO0_reduction_univ`). A reduction to SO₀ is our reading of what a Spin⁺ structure needs; the draft does not mention it (§3.6, p. 24). Limits: this concerns the connected group; a two-component Spin(7,7) → SO(7,7) structure is not excluded (not formalised); it holds as formalised, for the chimeric (7,7) metric on C with the fibre of all (1,3) metrics. We make no claim that it is new. | `no_spinStructure_univ`, `no_SO0_reduction_univ`, `no_spinLiftData`, `qLoop_pi`, `gHol_not_mem_SO0`, `det_gHol` |

## D. Underspecified in the draft (not formalisable as stated)

The Shiab family in (8.1) is only a template. The operator D_ω in (9.6) is not given. The fermionic
quadrant of (9.16) is left open. Integration over the non-compact fibres of Y is unaddressed. There
is no anomaly-cancellation mechanism. The global spin structure is not discussed; as formalised it fails over all of Y13 before w₂ even arises (C5). (External, unverified: disruptionjoe/gu-formalization `canon/w2-y14-spin-structure.md`
argues w₂(Y¹⁴) = π*w₂(X⁴), i.e. Y spin iff X spin, with only the mod-2 polynomial identities in Lean;
they retracted an earlier, unconditional version. That concerns the Riemannian spin structure of TY, structure group Spin(14), and is a separate question from C5, which concerns (C, chimeric (7,7) metric) and the orientation of its positive part.) Details: the
author's Phase 1 gap audit ("Omitted constructs"), not included in this repository.

## E2. Internal consistency note (Lean-checked)

Under the isometry `Φ : (ℝ¹⁴, Q77) ≅ (CFib, Bη)` the chimeric horizontal part `H*` is spanned by
`e₆, e₁₁, e₁₂, e₁₃` (`ΦL_horiz`, `ΦL_vert`, `Bundle/ChimReduction.lean`). The Pati–Salam blocks of
`Spinor/PatiSalamGroup.lean` (`W6 = e₁..e₆`, `W4 = e₁₀..e₁₃`, base `e₀,e₇,e₈,e₉`) are an abstract
`(1,3) ⊕ (6) ⊕ (4)` split with the right signatures, but they are not aligned with `V ⊕ H*` under `Φ`.
The group-theoretic results (Spin(6) ≅ SU(4), commuting, kernels) are unaffected. Statements about
the Pati–Salam group acting on the chimeric *bundle* need the aligned blocks `{0..5}`, `{7..10}`; the old
`W4` is three-quarters horizontal and the old base is vertical, so the Coleman–Mandula reading in
`synthetic_predictions.lean` ("fixes the base") applies to the aligned `PS6'`, `PS4'` (which fix `H*`
pointwise), not to the old blocks.

## E. Not done / open

- ~~The submanifold structure of the orthonormal frames.~~ Done (`isManifold_orthoFrames`, dimension 105).
- ~~The principal O(7,7)-bundle structure.~~ Done (`frameBundle`, `localTriv_diffeo`).
- ~~The time-orientation double cover of Y13.~~ Done for general X (`Ytilde`, `isCoveringMap_tilde`, `isManifold_tilde`, `no_closed_lift`); SO₀-reduction, global frame and Spin⁺ structure on it for X = ℝ⁴ (`exists_SO0_reduction_cover`, `exists_frame_tilde`, `coverSpin`). General X: the SO₀-reduction exists for every X (`redT_reduction`, via `lorO_mem_SO0`); the cover is Hausdorff when X is (`t2_Ytilde`); spin structure on the cover for general X: local ones and the {±1} defect cocycle (`exists_local_spin_cover`, `cover_defect_mem`, `exists_coverSpin_of_lifts`), global open (w₂). For parallelisable X (a continuous global frame of TX) a global frame of C and a Spin⁺ structure on the whole cover (`exists_coverSpin_parallel`), e.g. ℝ⁴ minus a plane, which is not simply connected. For general X, given continuous lifts on a fixed cover (assumed), the obstruction is the ℤ/2 Čech class of their defect (`defZ_cocycle`, `defZ_indep`, `isCobdy_defZ_iff`). Fibre ≃ S³: informal.
- w₁, w₂, ℤ/2 cohomology of manifolds: not available in the pinned Mathlib, so not defined here. Statements about them in this repo are informal. The formal content is cocycle data and an explicit holonomy.
- ~~No nontrivial gluing.~~ Done: two spin structures on the same frames over a non-simply-connected open `holeW` are not isomorphic (`not_iso_holeSpin`).

## F. Phases 3–6: claim-to-theorem map (`GU/Bundle/`, Lean-checked, standard axioms only)

| Claim | Theorem | Caveat |
|---|---|---|
| Orthonormal frames over Y13 are a smooth principal O(7,7)-bundle | `frameBundle`, `localTriv_diffeo` | |
| Adapted frames are a smooth 65-dimensional principal O(6,4)×O(1,3) sub-bundle; the aligned Pati–Salam groups act | `adaptedBundle`, `adaptedSubBundle`, `fibreDim_AFrM`, `adaptedBundle_PS6'`, `adaptedBundle_PS4'` | Inclusion and `ιB` are immersions (`injective_mfderiv_inclA`, `injective_mfderiv_ιB`); topological embedding not stated |
| Cocycle lifts ⇔ spin structures over an open W ⊂ Y13; every spin structure is isomorphic to the one glued from its cocycle | `spin_structure_of_lift`, `exists_data_iff_exists_structure`, `SpinStructure.isoToData` | Spin means the connected `Spin77` = Spin⁺(7,7). Image of Φ is the SO₀-reduction determined by the sections, not all of OFr |
| Φ is a double cover: fibres {p, p·(−1)}, covering map onto its image | `Φ_eq_iff`, `isCoveringMap_Φ` | |
| Defect of lifts lies in {±1} and changes by δη; same frames give isomorphic structures iff the lifts differ by a coboundary | `spinLift_defect_mem`, `defect_of_lifts`, `iso_iff_coboundary` | Identification with w₂ and H¹(·; ℤ/2) is informal |
| No spin structure over all of Y13 | C5 above | |
| Spin structures exist near every point, and over a time-gauge locus; for X = ℝ⁴ on all of `{G₀₀ > 0}` | `exists_spinStructure_near`, `exists_spinLiftData_gauge`, `mem_gaugeSet_iff`, `exists_spinLiftData_R4` | Natural but not canonical: it depends on the coordinate `x⁰` |
| There is no largest open subset of Y13 with a spin structure or a global frame | `no_largest_spinStructure`, `no_largest_frameSet` | Arbitrary open sets, no symmetry imposed |
| Over X = ℝ⁴, `{G₀₀ > 0}` is the largest open subset invariant under the matrices fixing dx⁰ up to scale that carries a global frame or a spin structure | `gauge_largest_iff`, `gauge_largest`, `gauge_largest_frame`, `exists_frame_timeGaugeLocus` | "Natural" means relative to that choice of covector. These matrices have three orbits per fibre (informal), so "largest" is largely by elimination; informally, the content is that no open set containing `{G₀₀ < 0}` of a fibre carries one. A coordinate-free base, the double cover of Y13, is open |
| Two charts with constant lift t; a sign change alters the lift but gives an isomorphic structure | `twoChart`, `twoCharts_iso`, `twoCharts_lift_ne`, `exists_twoChart_near` | Same domain and a Spin77-coboundary, so the gluing is trivial; not a nontrivial gluing |
| Spin(7,7) is a Lie group; ρ is a local diffeomorphism with image SO₀ | `lieGroup_spin`, `isLocalDiffeomorph_ρ`, `range_ρ` | Stated into O77, where SO₀ is open |
| Smooth data gives a smooth principal Spin(7,7)-bundle over W, Φ a local diffeomorphism | `smoothSpinBundle`, `isLocalDiffeomorph_Φ`, `exists_smoothSpin_near` | |
| No clopen SO₀-reduction of the frames over all of Y13 (no spin group involved); det gHol = 1 | `no_SO0_reduction_univ`, `det_gHol`, `no_spinStructure_of_neg_fibre` | Non-vacuous over smaller bases: `exists_reduction_timeGaugeLocus` |
| Non-isomorphic spin structures on the same frames over a non-simply-connected open set | `not_iso_holeSpin`, `holeSign_not_coboundary`, `holeLoop_not_nullhomotopic` | Isomorphism as `SpinIso`; as abstract principal bundles not analysed |
| Time-orientation double cover of Y13: two-sheeted covering, smooth manifold, pairs (metric, future cone), metric loop has no closed lift | `isCoveringMap_tilde`, `ncard_fibre`, `isManifold_tilde`, `eq_of_future_eq`, `future_pt`, `no_closed_lift`, `no_section` | General X; Hausdorff when Y13o X is |
| Over X = ℝ⁴ the cover carries a global frame of C, a clopen SO₀-reduction (which does not descend), and a Spin⁺(7,7) structure; the frame is smooth and the structure is a smooth principal bundle | `exists_frame_tilde`, `exists_SO0_reduction_cover`, `deck_not_SO0`, `coverSpin`, `range_coverSpin`, `contMDiff_Ff`, `smoothCoverSpin` | Frame from a smooth partition of unity plus a quaternion trivialisation |
| For every X the cover's frames have a clopen SO₀-reduction; orthochronous Lorentz transformations act through SO₀; the cover is Hausdorff when X is | `redT_reduction`, `lorO_mem_SO0`, `t2_Ytilde` | |
| Spin structures on the cover, general X: local ones, the SO₀ transition cocycle and its {±1} defect, global from continuous cocycle lifts | `exists_local_spin_cover`, `transI_cocycle`, `cover_defect_mem`, `exists_coverSpin_of_lifts` | Global existence for general X open (needs w₂, not in Mathlib) |
| CoverSpin API: two-to-one, covering map, spin structures ⇔ cocycle lifts (via a generic frame-system theory) | `CoverSpin.Φ_eq_iff`, `CoverSpin.isCoveringMap_Φ`, `coverSpin_iff_data`, `SpinGeneric.lean` | |
| Parallelisable X (continuous global frame of TX, no other hypothesis): global frame of C on the cover and a Spin⁺(7,7) structure over the whole cover with image the SO₀-reduction; for ℝ⁴ the image is that of `coverSpin`; also ℝ⁴ minus the plane x⁰ = x¹ = 0, which is not simply connected | `exists_coverSpin_parallel`, `continuous_secX`, `QT_eq_redT`, `exists_coverSpin_hole`, `loopU_not_nullHomotopic` (`ParallelCover.lean`) | The frame on X is encoded as a matrix in charts; its columns are continuous tangent sections (`continuous_section`). Smoothness for general X not formalised |
| The defect class: for continuous lifts of the transition functions (no cocycle condition), the {±1} defect is a locally constant ℤ/2 Čech 2-cocycle; its class does not depend on the lifts and vanishes iff the lifts can be corrected to cocycle lifts, which then give a Spin⁺ structure on the cover | `defZ_cocycle`, `cont_defZ`, `defZ_indep`, `isCobdy_defZ_iff`, `sheet_isCobdy_iff`, `exists_coverSpin_of_isCobdy` (`DefectClass.lean`) | On one fixed cover. Lifts on the sheet cover are a hypothesis, never constructed; independence of the cover and of the local sections is not formalised; "the class is w₂" is informal |
| Spinor bundle on the cover over ℝ⁴: the associated bundle P̃ ×_ρD ℂ^{64,64}, homeomorphic to the trivial vector bundle, with a frame-independent Hermitian nondegenerate form of signature (64,64); P_H (3.32) on the same P̃ | `SpinorBundle`, `toTrivial`, `spinorMk_linear`, `spinorForm_mk`, `spinorForm_conj`, `spinorForm_nondegenerate`, `coverPH` (`SpinorCover.lean`) | P_H is set level (no topology); the link from the spinor bundle to P_H (3.36), smoothness, connections and a Dirac operator are not built; over the cover of Y13(ℝ⁴) only |
| Two-component Spin(7,7) model Spin⁺ × {1, ω}: its non-identity component flips every Spin⁺-invariant spinor form; double cover onto SO₀ ∪ (−1)SO₀ in det = 1 | `flip_nonidentity`, `flip_omega`, `toO_ker`, `range_toO`, `det_toO`, `toO_spec`; onto SO(7,7): `range_toO_eq`, `SO77_eq`, `mem_SO0_iff` (`O77Components.lean`) | Identification of the model with Pin ∩ Cl⁰ informal |

Correction on record: the spin-lift theorem of commit 9b35485 and the first versions of Phase 4 items 1–2 were stated over all of Y13, so by C5 their hypotheses could not hold for nonempty X and they were vacuous; reviews 64–66 missed this. They were restated over an open base W in bcdbfd6.

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
  w₂ / spin structure (our C5 and the open items in E); "spinors need a choice of connection" (our blueprint B5,
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

## Literature check: time orientation of the (7,7) bundle (Phase 5 item 2, 2026-11-01)

Question: has anyone stated that the chimeric or DeWitt-type (7,7) bundle over the space of Lorentzian
metrics is not time-orientable, that Lorentzian metrics on ℝ⁴ retract to RP³, or how the SO₀ reduction
is handled? Read-only web and local search. Page text was treated as data. Quotes were read from
extracted PDF text unless marked otherwise.

**Prior statements, with a source**
- *The fibre retracts to RP³.* C. G. Torre, *Local cohomology in field theory*, arXiv:hep-th/9706092,
  §7 (pp. 18–20): "the bundle of Lorentzian signature metrics over an n-dimensional spacetime manifold
  admits a deformation retraction to a bundle E′ over spacetime whose typical fiber is diffeomorphic
  to the real projective space RP^{n−1}", attributed to Steenrod, *The Topology of Fibre Bundles*
  (1951). We did not read Steenrod and have no section number. So the RP³ statement in FINDINGS is classical, not ours.
- *The fibre's topology has been used physically.* The same source links the RP³ volume form to the
  Finkelstein–Misner "kink number" (1959), "the number of times a light cone tumbles".
  Related, titles only, not read: Chamblin, *Some applications of differential topology in general
  relativity*, arXiv:gr-qc/9509048 (includes the homotopy type of Lorentz metrics).
- *Time-orientable double covers of one Lorentzian manifold are standard.* Chruściel, *Elements of
  causality theory*, arXiv:1110.6706, Remark 2.1.2; Natário, *Mathematical Relativity*,
  arXiv:2003.02855. These cover one spacetime (M, g), not the universal bundle of metrics. Hadley,
  arXiv:1703.05573, is a related use.
- *Universal spinor bundle over all metrics, any signature.* Müller–Nowaczyk, arXiv:1504.01034
  (Lett. Math. Phys. 107(5), 933–961, 2017), Remark 2.2: GL̃⁺V / Spin_{r,s} ≅ GL⁺V / SO_{r,s} ≅ S_{r,s}V, with Spin_{r,s}
  the double cover of the **full** SO_{r,s}. Spinors there are built from a spin structure on the base
  M, using the two-component group. The extracted text has no occurrence of "time orient". This is the
  closest rigorous prior construction. It sits on GL̃⁺, not on a (7,7) bundle.
- *w₂ of Y¹⁴, external and unverified.* disruptionjoe/gu-formalization,
  `canon/w2-y14-spin-structure.md`, claims w₂(Y¹⁴) = π\*w₂(X⁴), fibre F = GL(4,ℝ)/O(3,1) ≅ RP³ up to
  homotopy. It takes a time line bundle L ⊂ TX⁴ with w₁(L) = 0 for oriented X⁴, a step that does not follow
  from w₁(V) + w₁(L) = 0 alone. It uses the tautological line γ¹ → RP³ only fibrewise, for the monodromy
  of H¹(RP³; ℤ/2), and never names w₁ of the resulting line bundle on Y¹⁴ as an obstruction.
  It does not mention SO(7,7) or the chimeric bundle. No conflict with C5: w₂ of TY is a different
  obstruction from the time-orientation one, which is a w₁(C⁺) question (the identification with w₁ is
  informal). Lean proves the holonomy statement, not a w₁ statement.
- *Nguyen–Polya* (Feb 2021), §2.2 footnotes a–b: the chimeric bundle has a natural metric from a
  **Riemannian** fibre point, spin structures need w₂(TU) = 0. No (7,7), no time orientation.

**What the draft says (local PDF, printed page numbers)**
- p. 4: "X⁴ … with a chosen orientation and unique spin structure". The word "orient" otherwise appears
  once in a non-mathematical sense and twice in the Hodge-star passage ("we have assumed our manifold to
  be oriented"). There is no time orientation, no SO₀, and no identity component of SO(7,7) anywhere.
- p. 24 (3.32): "P̃_Fr(C^{7,7}) is the double cover of the frame bundle of the Chimeric bundle". Its
  existence is assumed. So the "SO₀ reduction" in our blueprint is **our reading** of what a Spin⁺
  structure needs, not a step the draft takes. Lean now states that reduction directly
  (`no_SO0_reduction_univ`).
- pp. 24–25, (3.33) and (3.38), and again in a later diagram: the fibre is written **GL̃(4,ℝ)/Spin(1,3)**.
  The draft's opening table has "L = Sl(2,ℂ) Lorentz Group". Informal, our computation, reading GL̃(4,ℝ)
  as GL̃⁺(4,ℝ) since X⁴ is oriented (the "connected two-fold double cover" of GL(N,ℝ) on p. 20 cannot be
  literal, as GL(N,ℝ) has two components): if Spin(1,3) is
  the connected Sl(2,ℂ), this quotient is GL⁺(4,ℝ)/SO₀(1,3) ≃ S³, which is the *time- and space-oriented*
  metrics, i.e. the double cover Phase 5 builds, and not the metrics the draft defines Y by. If Spin(1,3)
  is the two-component cover of SO(1,3), it is GL⁺(4,ℝ)/SO(1,3) ≃ RP³, the metrics themselves. The draft
  does not say which. So the draft's notation may already contain the resolution, or may conceal the
  obstruction; this is a reading, not a claim about intent.
- p. 25: "all that has been chosen is the signature of a (1, 3)-metric". The time orientation is not
  listed as a choice.

**A claim that conflicts with this**
- S. Austermann, *Pati-Salam gauge unification from the Lorentzian DeWitt metric*, Phys. Lett. B 877
  (2026) 140447: "The fibre F = GL⁺(4,ℝ)/SO(3,1) is contractible and contributes no topological
  multiplicity." This contradicts Steenrod via Torre, and the elementary (informal) computation GL⁺(4)/SO(3,1) ≃
  SO(4)/S(O(1)×O(3)) ≅ RP³ (contractible is the *Riemannian* fibre GL⁺(4)/SO(4)). Our Lean holonomy
  theorem does not itself state non-contractibility. We make no claim about the paper's other results;
  its (6,4) signature agrees with ours (A2 context). Single-author, not checked further.

**Searched for and not found** (weak negatives: a few searches, English, open web)
- Any statement that the chimeric or DeWitt-type (7,7) bundle over Lorentzian metrics is not
  time-orientable, or that C⁺ has nonzero w₁ on the metric bundle.
- Any critic of GU discussing the SO₀ reduction or time orientation. Nguyen–Polya does not; Woit's post
  ?p=5927 and its comments do not (full-text search of both comment pages, 76 responses); Physics Forums, Substack explainers do not (search
  summaries only).
- Any treatment by Weinstein of time orientation. A summary of the 2020 talk mentions a "double cover";
  it is an AI-generated summary and it was not confirmed. We had no transcript of the talk.
- DeWitt- and simplicial-supermetric signature papers: Giulini (gr-qc/9311017), Giulini–Kiefer (gr-qc/9405040), Hartle–Miller–
  Williams (gr-qc/9609028): signature results only, nothing on orientability of the subbundles (search summaries, not read in full).
- Not checked: Steenrod's text, Weinstein's later talks, non-English sources, paywalled journals.

**Status of C5 relative to this:** RP³ is classical, the double cover of one spacetime is classical, the
universal two-component spinor bundle exists. The specific statement that a Spin⁺(7,7) structure on the
chimeric bundle cannot exist over all of Y13 for nonempty X, with its Lean proof, was not found in what
we read. That is "not found", not "new"; an expert should confirm (see "Before any publication").

## Before any publication

1. ~~Read Nguyen–Polya (2021)~~ done. ~~Wider web search~~ done (nothing found). Remaining: an expert who follows GU confirms nothing is missed.
2. Get an independent read by a mathematician or physicist, to check that each formal statement
   matches the intended reading of the draft. That matters most for A1, A4–A6 and B3, which depend
   on bracket and sign conventions.
3. Pin the exact draft version and equation numbering.

---
© 2026 Manuel Tarouca. Licensed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/).
