import GU.Bundle.MetricLoopChim

/-!
# Phase 4, item 4: no `SO₀`-reduction of the frame bundle over all of `Y13`

The loop of metrics `Rθ ηR Rθᵀ`, `θ ∈ [0, π]`, in one fibre of `Y13` has frame holonomy `gHol ∉ SO₀`
(`qLoop_pi`, `gHol_not_mem_SO0`): rotating the timelike axis by `π` reverses the time orientation.
Over `W`, the image of a spin structure is a relatively clopen set of frames meeting each fibre in
one `SO₀`-coset (`isOpen_range_Φ`, `exists_nhds_disjoint`), which no such path can leave.

**`no_spinLiftData`**, **`no_spinStructure`**: an open `W` containing such a loop carries no spin
structure, so (`no_spinStructure_univ`) none exists over all of `Y13` when `X` is nonempty. This is
an obstruction of `w₁`-type (the positive part of `C` is not orientable
over `Y13`), upstream of `w₂`. It concerns the connected group `Spin77 → SO₀(7,7)` and base all of
`Y13`; it does not exclude a two-component spin group covering `SO(7,7)` (`gHol` has determinant 1,
not formalised here), and smaller bases do carry spin structures (`SpinExamples.lean`).
-/

namespace GU.Library

open Bundle Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-! ### The holonomy of the loop -/

lemma sθ_pi : sθ Real.pi = sθ 0 := by
  have h0 : Gθ 0 = ηR := by rw [Gθ, Rθ_zero]; simp
  have hp : Gθ Real.pi = ηR := by
    rw [Gθ, Rθ_pi, GU.Iso77.ηR_eq, ηr, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext i; fin_cases i <;> simp
  unfold sθ; rw [h0, hp]

lemma yLoop_pi (x : X) : yLoop x Real.pi = yLoop x 0 :=
  Subtype.ext (congrArg (TotalSpace.mk x) sθ_pi)

lemma TP_Rθ_zero (u : CFib) : TP (Rθ 0) (isUnit_Rθ 0) u = u := by
  refine Prod.ext ?_ ?_
  · show symCoords (Rθ 0 * symMat u.1 * (Rθ 0)ᵀ) = u.1
    rw [Rθ_zero]; simp [symCoords_symMat]
  · show u.2.comp (toCLM (Rθ 0)⁻¹) = u.2
    rw [Rθ_zero, inv_one]
    refine ContinuousLinearMap.ext fun w => ?_
    simp [toCLM_apply]

lemma ΦL_single (i : Fin 14) :
    ΦL (Pi.single i 1 : Fin 14 → ℝ) =
      GU.Iso77.cfac i • GU.Iso77.toCF (chimVec (GU.Iso77.σl i)) := by
  have h : GU.Iso77.Ψ (Pi.single i 1 : Fin 14 → ℝ) = GU.Iso77.Bon i := by
    simp [GU.Iso77.Ψ, Module.Basis.equivFun_symm_apply, Pi.single_apply]
  show GU.Iso77.toCFL (GU.Iso77.Ψ (Pi.single i 1)) = _
  rw [h, GU.Iso77.Bon_apply, map_smul]; rfl

lemma dHol_eq_sgnK (i : Fin 14) : dHol i = sgnK (GU.Iso77.σl i) := by
  fin_cases i <;> simp [dHol, sgnK, GU.Iso77.σl]

/-- The endpoint frame is the initial frame composed with the holonomy. -/
lemma hLoop_pi : hLoop Real.pi = (hLoop 0).comp (matCLM gHolM) := by
  have hb : ∀ i : Fin 14, hLoop Real.pi (Pi.single i 1) =
      (hLoop 0).comp (matCLM gHolM) (Pi.single i 1) := by
    intro i
    have e : matCLM gHolM (Pi.single i 1) = dHol i • (Pi.single i 1 : Fin 14 → ℝ) := by
      show (Matrix.diagonal dHol) *ᵥ Pi.single i 1 = _
      rw [Matrix.mulVec_single_one]
      ext k; by_cases h : k = i
      · subst h; simp
      · simp [h]
    show TP (Rθ Real.pi) (isUnit_Rθ _) (ΦL _) = TP (Rθ 0) (isUnit_Rθ 0) (ΦL (matCLM gHolM (Pi.single i 1)))
    rw [TP_Rθ_zero, e, map_smul, ΦL_single, map_smul, TP_chim, dHol_eq_sgnK, smul_comm]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [← Finset.univ_sum_single v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show Pi.single k (v k) = v k • (Pi.single k 1 : Fin 14 → ℝ) by
    ext i; by_cases e : i = k <;> simp [e], map_smul, map_smul, hb]

lemma mk_eq_of {y y' : Yobs X} (hy : y = y') {h h' : HomF} (hh : h = h') :
    (⟨y, h⟩ : HomTotM X) = ⟨y', h'⟩ := by subst hy; subst hh; rfl

/-- **The holonomy of the frame path.** -/
theorem qLoop_pi (x : X) : qLoop x Real.pi = ractM (qLoop x 0) gHolM :=
  mk_eq_of (yLoop_pi x) hLoop_pi

/-- The frame path in the frame bundle. -/
def pLoop (x : X) (θ : ℝ) : OFr X := ⟨qLoop x θ, (qLoop_mem x θ).1⟩

lemma continuous_pLoop (x : X) : Continuous (pLoop x) := (continuous_qLoop x).subtype_mk _

lemma pLoop_pi (x : X) : pLoop x Real.pi = actOFr' (pLoop x 0) gHol :=
  Subtype.ext (qLoop_pi x)

/-! ### The image of a spin structure is locally clopen -/

namespace SpinLiftData

variable (D : SpinLiftData X)

lemma mem_range_of_τ (i : D.ι) {q : OFr X} (hi : projOFr q ∈ D.V i) (h : D.τ i q ∈ SO0) :
    q ∈ Set.range D.Φ := by
  obtain ⟨t, ht⟩ := spinToSO0_surjective ⟨_, h⟩
  have ht' : spinToO77 t = D.τ i q := congrArg Subtype.val ht
  set e := D.core.localTriv i
  let y : D.W := ⟨projOFr q, D.V_sub i hi⟩
  have hT : (y, t) ∈ e.target := by rw [e.target_eq]; exact ⟨hi, Set.mem_univ _⟩
  set p := e.toOpenPartialHomeomorph.symm (y, t)
  have hep : e p = (y, t) := e.right_inv hT
  have hpp : p.proj = y := e.proj_symm_apply hT
  refine ⟨p, ?_⟩
  rw [D.Φ_chart i (by rw [hpp]; exact hi), hpp, hep]
  show actOFr' _ (spinToO77 t) = q
  rw [ht']; exact D.τ_spec i hi

lemma isOpen_nbhd (i : D.ι) {A : Set O77} (hA : IsOpen A) :
    IsOpen (projOFr ⁻¹' D.V i ∩ D.τ i ⁻¹' A) :=
  (D.continuousOn_τ i).isOpen_inter_preimage ((D.isOpen_V i).preimage continuous_projOFr) hA

/-- **The image of `Φ` is open in the frame bundle.** -/
theorem isOpen_range_Φ : IsOpen (Set.range D.Φ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro q ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := D.cover _ p.proj.2
  have hi' : projOFr (D.Φ p) ∈ D.V i := by rw [D.proj_Φ]; exact hi
  exact ⟨_, fun r hr => D.mem_range_of_τ i hr.1 hr.2,
    D.isOpen_nbhd i (isOpen_connectedComponent (x := (1 : O77))), hi',
    D.τ_mem_SO0 i ⟨p, rfl⟩ hi'⟩

/-- **Over `W`, the image of `Φ` is also relatively closed.** -/
theorem exists_nhds_disjoint {q : OFr X} (hq : q ∉ Set.range D.Φ) (hW : projOFr q ∈ D.W) :
    ∃ N : Set (OFr X), IsOpen N ∧ q ∈ N ∧ Disjoint N (Set.range D.Φ) := by
  obtain ⟨i, hi⟩ := D.cover _ hW
  refine ⟨_, D.isOpen_nbhd i (isClosed_connectedComponent (x := (1 : O77))).isOpen_compl,
    ⟨hi, fun h => hq (D.mem_range_of_τ i hi h)⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro r ⟨hr, hrO⟩ hrQ
  exact hrO (D.τ_mem_SO0 i hrQ hr)

end SpinLiftData

/-! ### The obstruction -/

namespace SpinLiftData

variable (D : SpinLiftData X)

/-- A path of frames over `W` starting in the image stays in the image. -/
lemma path_stays {f : ℝ → OFr X} (hf : Continuous f) (hW : ∀ θ, projOFr (f θ) ∈ D.W)
    (h0 : f 0 ∈ Set.range D.Φ) (θ : ℝ) : f θ ∈ Set.range D.Φ := by
  have hcl : IsClopen (f ⁻¹' Set.range D.Φ) := by
    refine ⟨?_, D.isOpen_range_Φ.preimage hf⟩
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨N, hN, hqN, hd⟩ := D.exists_nhds_disjoint (q := f t) ht (hW t)
    exact ⟨f ⁻¹' N, fun u hu huQ => Set.disjoint_left.mp hd hu huQ, hN.preimage hf, hqN⟩
  have huniv := hcl.eq_univ ⟨0, h0⟩
  have : θ ∈ f ⁻¹' Set.range D.Φ := by rw [huniv]; exact Set.mem_univ _
  exact this

/-- The local frame lies in the image. -/
lemma σ_mem_range (i : D.ι) {y : Y13o X} (hy : y ∈ D.V i) : D.σ i y ∈ Set.range D.Φ := by
  have hry : projOFr (D.σ i y) = y := D.proj_σ i y hy
  have hmem : projOFr (D.σ i y) ∈ D.V i := by rw [hry]; exact hy
  have hτ : D.τ i (D.σ i y) = 1 := D.τ_unique i hmem (by rw [hry, actOFr'_one])
  exact D.mem_range_of_τ i hmem (by rw [hτ]; exact one_mem _)

/-- If `σᵢ y · c` lies in the image, then `c ∈ SO₀`. -/
lemma mem_SO0_of_act_mem (i : D.ι) {y : Y13o X} (hy : y ∈ D.V i) {c : O77}
    (h : actOFr' (D.σ i y) c ∈ Set.range D.Φ) : c ∈ SO0 := by
  have hry : projOFr (actOFr' (D.σ i y) c) = y := by rw [projOFr_act]; exact D.proj_σ i y hy
  have hmem : projOFr (actOFr' (D.σ i y) c) ∈ D.V i := by rw [hry]; exact hy
  have hτ : D.τ i (actOFr' (D.σ i y) c) = c := D.τ_unique i hmem (by rw [hry])
  have := D.τ_mem_SO0 i h hmem
  rwa [hτ] at this

end SpinLiftData

lemma exists_act_eq (p r : OFr X) (hp : projOFr p = projOFr r) : ∃ h : O77, actOFr' p h = r := by
  have h1 : (p : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact p.2
  have h2 : (r : HomTotM X) ∈ orthoSetM := by rw [← levelSet_Fframe]; exact r.2
  have h3 : (p : HomTotM X).proj = (r : HomTotM X).proj := congrArg Subtype.val hp
  obtain ⟨g, hg⟩ := ractM_transitive' h1 h2 h3
  exact ⟨g, Subtype.ext hg⟩

/-- **No cocycle lift exists over an open `W` containing a full loop of metrics.** -/
theorem no_spinLiftData (D : SpinLiftData X) (x : X) (hW : ∀ θ, projOFr (pLoop x θ) ∈ D.W) :
    False := by
  obtain ⟨i, hi⟩ := D.cover (projOFr (pLoop x 0)) (hW 0)
  have hry : projOFr (pLoop x 0) = projOFr (D.σ i (projOFr (pLoop x 0))) :=
    (D.proj_σ i _ hi).symm
  obtain ⟨h, hh⟩ := exists_act_eq _ _ hry
  have hf : Continuous fun θ => actOFr' (pLoop x θ) h :=
    continuous_actOFr'.comp ((continuous_pLoop x).prodMk continuous_const)
  have hstay := D.path_stays hf (fun θ => by rw [projOFr_act]; exact hW θ)
    (by rw [hh]; exact D.σ_mem_range i hi) Real.pi
  have hact : actOFr' (pLoop x Real.pi) h =
      actOFr' (D.σ i (projOFr (pLoop x 0))) (h⁻¹ * gHol * h) := by
    rw [pLoop_pi, ← hh, actOFr'_mul, actOFr'_mul]
    congr 1; group
  rw [hact] at hstay
  exact gHol_not_mem_SO0 (conj_mem_SO0 h (D.mem_SO0_of_act_mem i hi hstay))

/-- **No spin structure exists over an open `W` containing a full loop of metrics**; in particular
none exists over all of `Y13` when `X` is nonempty. -/
theorem no_spinStructure (S : SpinStructure X) (x : X) (hW : ∀ θ, projOFr (pLoop x θ) ∈ S.W) :
    False :=
  no_spinLiftData S.toData x hW

theorem no_spinStructure_univ (S : SpinStructure X) (hW : S.W = Set.univ) (x : X) : False :=
  no_spinStructure S x fun θ => by rw [hW]; exact Set.mem_univ _

end

end GU.Library
