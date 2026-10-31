import GU.Library.LevelInclusionOn
import GU.Library.Orthogonal

/-!
# Track 3, L4d: orthonormal frames of a smooth metric family form a smooth manifold

Let `G : ℝⁿ → Mat m` be `C^∞` on an open `U`, with `G y` symmetric, and fix a symmetric `η` with
`η² = 1` (e.g. `ηSig 7 7`). The `G(y)`-orthonormal frames
`{(y, q) | y ∈ U, qᵀ G(y) q = η}` are the level set of
`F(y, q) = sym(qᵀ G(y) q)` (set to `0` outside `U`). Its derivative in `q` alone,
`X ↦ Xᵀ G q + qᵀ G X`, is onto the symmetric matrices at every frame (`X = ½ q η S`;
`orthF_surj_gen`), so by `isManifold_levelOn` the frames form a smooth manifold
(**`isManifold_frames`**) of dimension `n + m(m−1)/2` (`fibreDim_frames`). Nondegeneracy of `G` is
not assumed: fibres over degenerate or wrong-signature points are simply empty. For GU, `G` is
the chimeric metric in fibre coordinates over a chart of `Y`, with `m = 14` and `η = η₇₇`. This is
**chartwise**. Still open: generalising the base to Yobs's model, transporting the fibre along
`ΦL`, smoothness of the chimeric Gram matrix, and gluing the chart pieces (or a regular value
theorem on manifold domains).
-/

namespace GU.Library

open Matrix
open scoped ContDiff Manifold Matrix

variable {m : ℕ}

/-- **Surjectivity for a general metric**: if `qᵀ Gm q = η` with `Gm, η` symmetric and `η² = 1`,
then `X ↦ sym(qᵀ Gm X + Xᵀ Gm q)` is onto `symS m`. -/
lemma orthF_surj_gen (Gm η : Mat m) (hG : Gm ∈ symS m) (hη : η ∈ symS m)
    (hηη : Matrix.of η * Matrix.of η = 1) (q : Mat m) (hq : bil Gm q q = η) :
    (fderiv ℝ (orthF Gm) q).range = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun S => ?_
  set M := Matrix.of q
  set g := Matrix.of Gm
  set e := Matrix.of η
  set s := Matrix.of (S : Mat m)
  have hMm : Mᵀ * g * M = e := by rw [← bil_eq_mat, hq]
  have hg : gᵀ = g := mat_symm_of_mem hG
  have he : eᵀ = e := mat_symm_of_mem hη
  have hs : sᵀ = s := mat_symm_of_mem S.2
  let X : Mat m := Matrix.of.symm ((1 / 2 : ℝ) • (M * e * s))
  have hX : Matrix.of X = (1 / 2 : ℝ) • (M * e * s) := rfl
  refine ⟨X, ?_⟩
  show fderiv ℝ (orthF Gm) q X = S
  rw [fderiv_orthF]
  have h1 : Matrix.of (bil Gm q X) = (1 / 2 : ℝ) • s := by
    rw [bil_eq_mat, hX, Matrix.mul_smul]
    congr 1
    calc Mᵀ * g * (M * e * s) = (Mᵀ * g * M) * e * s := by simp only [Matrix.mul_assoc]
      _ = s := by rw [hMm, hηη, Matrix.one_mul]
  have h2 : Matrix.of (bil Gm X q) = (1 / 2 : ℝ) • s := by
    rw [bil_eq_mat, hX, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    calc (M * e * s)ᵀ * g * M = s * (e * (Mᵀ * g * M)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, he]; simp only [Matrix.mul_assoc]
      _ = s := by rw [hMm, hηη, Matrix.mul_one]
  have hsum : bil Gm q X + bil Gm X q = (S : Mat m) := by
    have : Matrix.of (bil Gm q X + bil Gm X q) = s := by
      rw [← Matrix.of_add_of, h1, h2, ← add_smul]; norm_num
    exact Matrix.of.injective (this.trans rfl)
  apply Subtype.ext
  show (symP m (bil Gm q X + bil Gm X q) : Mat m) = S
  rw [hsum, symP_of_mem S.2]

section Family

variable {n : ℕ} (G : (Fin n → ℝ) → Mat m) (U : Set (Fin n → ℝ))

/-- `F₀(y, q) = sym(qᵀ G(y) q)`. -/
noncomputable def frameF0 (p : (Fin n → ℝ) × Mat m) : symS m := orthF (G p.1) p.2

variable {G U}

lemma contDiffOn_frameF0 (hG : ContDiffOn ℝ ∞ G U) :
    ContDiffOn ℝ ∞ (frameF0 G) (Prod.fst ⁻¹' U) := by
  have hb : ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × Mat m => bil (G p.1) p.2 p.2) (Prod.fst ⁻¹' U) := by
    refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    simp only [bil_apply]
    refine ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ => ?_
    have hq : ∀ a b : Fin m, ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × Mat m => p.2 a b) := fun a b =>
      (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) a b).comp contDiff_snd
    have hGkl : ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × Mat m => G p.1 k l) (Prod.fst ⁻¹' U) :=
      (contDiffOn_pi.mp (contDiffOn_pi.mp hG k) l).comp contDiff_fst.contDiffOn fun _ hp => hp
    exact ((hq k i).contDiffOn.mul hGkl).mul (hq l j).contDiffOn
  exact (symP m).contDiff.comp_contDiffOn hb

/-- The derivative of `F₀` is onto at every frame. -/
lemma frameF0_surj (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hsym : ∀ y ∈ U, G y ∈ symS m)
    {η : Mat m} (hη : η ∈ symS m) (hηη : Matrix.of η * Matrix.of η = 1)
    {p : (Fin n → ℝ) × Mat m} (hp : p.1 ∈ U) (hq : bil (G p.1) p.2 p.2 = η) :
    (fderiv ℝ (frameF0 G) p).range = ⊤ := by
  have hU' : IsOpen (Prod.fst ⁻¹' U : Set ((Fin n → ℝ) × Mat m)) := hU.preimage continuous_fst
  have hD : HasFDerivAt (frameF0 G) (fderiv ℝ (frameF0 G) p) p :=
    (((contDiffOn_frameF0 hG).contDiffAt (hU'.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hinc : HasFDerivAt (fun q : Mat m => (p.1, q))
      ((0 : Mat m →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ (Mat m))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hcomp := hD.comp p.2 (by simpa using hinc)
  have hfd : fderiv ℝ (orthF (G p.1)) p.2 = (fderiv ℝ (frameF0 G) p).comp
      ((0 : Mat m →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ (Mat m))) := hcomp.fderiv
  have htop := orthF_surj_gen (G p.1) η (hsym _ hp) hη hηη p.2 hq
  rw [hfd] at htop
  exact top_le_iff.mp (htop ▸ LinearMap.range_comp_le_range _ _)

end Family

section Frames

variable {n : ℕ} {G : (Fin n → ℝ) → Mat m} {U : Set (Fin n → ℝ)} {η : Mat m}

lemma bil_of_orthF_eq {Gm q : Mat m} (hG : Gm ∈ symS m) (hη : η ∈ symS m)
    (h : orthF Gm q = ⟨η, hη⟩) : bil Gm q q = η := by
  have := congrArg Subtype.val h
  rwa [orthF, symP_of_mem (bil_mem Gm hG q)] at this

open Classical in
/-- `F(y, q) = sym(qᵀ G(y) q)` on `U × Mat m`, and `0` elsewhere. -/
noncomputable def frameF (G : (Fin n → ℝ) → Mat m) (U : Set (Fin n → ℝ)) :
    (Fin n → ℝ) × Mat m → symS m :=
  fun p => if p ∈ (Prod.fst ⁻¹' U : Set ((Fin n → ℝ) × Mat m)) then frameF0 G p else 0

open Classical in
/-- The `G(y)`-orthonormal frames form a regular level set. -/
lemma frames_submersive (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hsym : ∀ y ∈ U, G y ∈ symS m)
    (hη : η ∈ symS m) (hηη : Matrix.of η * Matrix.of η = 1) (hη0 : (⟨η, hη⟩ : symS m) ≠ 0) :
    SmoothSubmersiveOn (frameF G U) ⟨η, hη⟩ (Prod.fst ⁻¹' U) :=
  smoothSubmersiveOn_extend (hU.preimage continuous_fst) (contDiffOn_frameF0 hG)
    (fun _ hp hpc => frameF0_surj hU hG hsym hη hηη hp (bil_of_orthF_eq (hsym _ hp) hη hpc))
    0 hη0.symm

open Classical in
lemma mem_frames_iff (hη : η ∈ symS m) (hη0 : (⟨η, hη⟩ : symS m) ≠ 0)
    (hsym : ∀ y ∈ U, G y ∈ symS m) (p : (Fin n → ℝ) × Mat m) :
    p ∈ levelSet (frameF G U) ⟨η, hη⟩ ↔ p.1 ∈ U ∧ bil (G p.1) p.2 p.2 = η := by
  rw [show levelSet (frameF G U) ⟨η, hη⟩ = levelSet (fun p => if p ∈ (Prod.fst ⁻¹' U :
    Set ((Fin n → ℝ) × Mat m)) then frameF0 G p else 0) ⟨η, hη⟩ from rfl,
    mem_levelSet_extend_iff 0 hη0.symm]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, bil_of_orthF_eq (hsym _ h1) hη h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  apply Subtype.ext
  show (symP m (bil (G p.1) p.2 p.2) : Mat m) = η
  rw [symP_of_mem (bil_mem _ (hsym _ h1) _), h2]

/-- **Orthonormal frames of a smooth metric family form a smooth manifold.** -/
theorem isManifold_frames (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hsym : ∀ y ∈ U, G y ∈ symS m)
    (hη : η ∈ symS m) (hηη : Matrix.of η * Matrix.of η = 1) (hη0 : (⟨η, hη⟩ : symS m) ≠ 0) :
    letI := smoothLevelChartedOn (frames_submersive hU hG hsym hη hηη hη0)
    IsManifold 𝓘(ℝ, Fin (fibreDim ((Fin n → ℝ) × Mat m) (symS m)) → ℝ) ∞
      (levelSet (frameF G U) ⟨η, hη⟩) :=
  isManifold_levelOn _

/-- **Dimension**: `n + m(m−1)/2` (for `ℝ¹⁴`-frames: base dimension `+ 91`). -/
lemma fibreDim_frames (n m : ℕ) : fibreDim ((Fin n → ℝ) × Mat m) (symS m) = n + m.choose 2 := by
  have h1 := fibreDim_orth m
  have hle : Module.finrank ℝ (symS m) ≤ Module.finrank ℝ (Mat m) := Submodule.finrank_le _
  unfold fibreDim at h1 ⊢
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

end Frames

end GU.Library
