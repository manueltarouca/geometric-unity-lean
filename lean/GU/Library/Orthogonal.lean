import GU.Library.LevelInclusion

/-!
# Track 3, L3: the pseudo-orthogonal group `O(η)` as a smooth manifold

Matrices are plain functions `Mat n = Fin n → Fin n → ℝ` (product norm). For a symmetric `η` with
`η² = 1` (e.g. `diag(1^p, (−1)^q)`), `f M = sym (Mᵀ η M)` maps into the symmetric matrices `symS n`,
and `O(η) = f⁻¹{η}` (`mem_orthLevel_iff`). At every `M ∈ O(η)`, `f′(M) X = Xᵀ η M + Mᵀ η X` is
surjective (`X = ½ M η S` hits `S`), so `O(η)` is a smooth manifold of dimension
`n² − n(n+1)/2 = n(n−1)/2` (`isManifold_orth`, `fibreDim_orth`). With matrix multiplication
(`orthGroup`, inverse `η Aᵀ η`) it is a **Lie group** (`lieGroup_orth`); for `η = diag(1⁷, (−1)⁷)`:
`lieGroup_O77`, `dim_O77 = 91`; `O77` carries these as global instances.

Caution: `*` and `1` on `Mat n` are the pointwise Pi operations; matrix algebra always goes through
`Matrix.of` (`mulM`, `invM`, `bil_eq_mat`).
-/

namespace GU.Library

open scoped Manifold ContDiff Matrix

abbrev Mat (n : ℕ) := Fin n → Fin n → ℝ

variable {n : ℕ}

/-- `(A, C) ↦ Aᵀ η C`, entrywise. -/
def bilL (η : Mat n) : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] Mat n :=
  LinearMap.mk₂ ℝ (fun A C i j => ∑ k, ∑ l, A k i * η k l * C l j)
    (fun A A' C => by ext i j; simp [add_mul, Finset.sum_add_distrib])
    (fun r A C => by ext i j; simp [Finset.mul_sum, mul_assoc])
    (fun A C C' => by ext i j; simp [mul_add, Finset.sum_add_distrib])
    (fun r A C => by
      ext i j; simp [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- The continuous bilinear map `(A, C) ↦ Aᵀ η C`. -/
noncomputable def bil (η : Mat n) : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] _).toLinearMap ∘ₗ bilL η)

lemma bil_apply (η A C : Mat n) (i j : Fin n) :
    bil η A C i j = ∑ k, ∑ l, A k i * η k l * C l j := rfl

/-- Symmetric matrices. -/
def symS (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {S | ∀ i j, S i j = S j i}
  add_mem' ha hb i j := by simp [ha i j, hb i j]
  zero_mem' _ _ := rfl
  smul_mem' r S hS i j := by simp [hS i j]

/-- Symmetrisation `S ↦ (S + Sᵀ)/2`. -/
noncomputable def symP (n : ℕ) : Mat n →L[ℝ] symS n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S => ⟨fun i j => (S i j + S j i) / 2, fun i j => by simp [add_comm]⟩
      map_add' := fun S T => by ext i j; simp; ring
      map_smul' := fun r S => by ext i j; simp; ring }

lemma symP_of_mem {S : Mat n} (hS : S ∈ symS n) : (symP n S : Mat n) = S := by
  funext i j
  show (S i j + S j i) / 2 = S i j
  rw [hS j i]; ring

lemma bil_symm (η : Mat n) (hη : η ∈ symS n) (A C : Mat n) (i j : Fin n) :
    bil η A C i j = bil η C A j i := by
  simp only [bil_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hη k l]; ring

lemma bil_mem (η : Mat n) (hη : η ∈ symS n) (M : Mat n) : bil η M M ∈ symS n :=
  fun i j => bil_symm η hη M M i j

/-- The defining map of `O(η)`. -/
noncomputable def orthF (η : Mat n) (M : Mat n) : symS n := symP n (bil η M M)

/-- `η` as a symmetric matrix. -/
def ηS (η : Mat n) (hη : η ∈ symS n) : symS n := ⟨η, hη⟩

lemma mem_orthLevel_iff (η : Mat n) (hη : η ∈ symS n) (M : Mat n) :
    M ∈ levelSet (orthF η) (ηS η hη) ↔ bil η M M = η := by
  show symP n (bil η M M) = ⟨η, hη⟩ ↔ _
  rw [Subtype.ext_iff, symP_of_mem (bil_mem η hη M)]

lemma orthF_contDiff (η : Mat n) : ContDiff ℝ ∞ (orthF η) :=
  (symP n).contDiff.comp ((bil η).isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id))

lemma fderiv_orthF (η : Mat n) (M X : Mat n) :
    fderiv ℝ (orthF η) M X = symP n (bil η M X + bil η X M) := by
  have hb : HasFDerivAt (fun M => bil η M M)
      ((bil η).precompR (Mat n) M (ContinuousLinearMap.id ℝ _) +
        (bil η).precompL (Mat n) (ContinuousLinearMap.id ℝ _) M) M :=
    (bil η).hasFDerivAt_of_bilinear (hasFDerivAt_id M) (hasFDerivAt_id M)
  have := ((symP n).hasFDerivAt.comp M hb).fderiv
  change fderiv ℝ (⇑(symP n) ∘ fun M => bil η M M) M X = _
  rw [this]
  rfl

/-- `bil` is matrix multiplication `Aᵀ η C`. -/
lemma bil_eq_mat (η A C : Mat n) :
    Matrix.of (bil η A C) = (Matrix.of A)ᵀ * Matrix.of η * Matrix.of C := by
  ext i j
  simp only [Matrix.of_apply, bil_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma mat_symm_of_mem {S : Mat n} (hS : S ∈ symS n) : (Matrix.of S)ᵀ = Matrix.of S := by
  ext i j; exact (hS i j).symm

/-- The submersion hypothesis: `f′(M)` is onto at every `M ∈ O(η)`. -/
lemma orthF_surj (η : Mat n) (hη : η ∈ symS n) (hηη : Matrix.of η * Matrix.of η = 1)
    (M : Mat n) (hM : bil η M M = η) : (fderiv ℝ (orthF η) M).range = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun S => ?_
  set m := Matrix.of M
  set e := Matrix.of η
  set s := Matrix.of (S : Mat n)
  have hMm : mᵀ * e * m = e := by rw [← bil_eq_mat, hM]
  have he : eᵀ = e := mat_symm_of_mem hη
  have hs : sᵀ = s := mat_symm_of_mem S.2
  let X : Mat n := Matrix.of.symm ((1 / 2 : ℝ) • (m * e * s))
  have hX : Matrix.of X = (1 / 2 : ℝ) • (m * e * s) := rfl
  refine ⟨X, ?_⟩
  show fderiv ℝ (orthF η) M X = S
  rw [fderiv_orthF]
  have h1 : Matrix.of (bil η M X) = (1 / 2 : ℝ) • s := by
    rw [bil_eq_mat, hX, Matrix.mul_smul]
    congr 1
    calc mᵀ * e * (m * e * s) = (mᵀ * e * m) * e * s := by simp only [Matrix.mul_assoc]
      _ = s := by rw [hMm, hηη, Matrix.one_mul]
  have h2 : Matrix.of (bil η X M) = (1 / 2 : ℝ) • s := by
    rw [bil_eq_mat, hX, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    calc (m * e * s)ᵀ * e * m = s * (e * (mᵀ * e * m)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, he]; simp only [Matrix.mul_assoc]
      _ = s := by rw [hMm, hηη, Matrix.mul_one]
  have hsum : bil η M X + bil η X M = (S : Mat n) := by
    have : Matrix.of (bil η M X + bil η X M) = s := by
      rw [← Matrix.of_add_of, h1, h2, ← add_smul]; norm_num
    exact Matrix.of.injective (this.trans rfl)
  apply Subtype.ext
  show (symP n (bil η M X + bil η X M) : Mat n) = S
  rw [hsum, symP_of_mem S.2]

/-- `O(η)` is a regular level set. -/
lemma orth_submersive (η : Mat n) (hη : η ∈ symS n) (hηη : Matrix.of η * Matrix.of η = 1) :
    SmoothSubmersive (orthF η) (ηS η hη) :=
  ⟨orthF_contDiff η, fun M hM => orthF_surj η hη hηη M ((mem_orthLevel_iff η hη M).mp hM)⟩

/-- **`O(η)` is a smooth manifold** of dimension `fibreDim (Mat n) (symS n)`. -/
theorem isManifold_orth (η : Mat n) (hη : η ∈ symS n) (hηη : Matrix.of η * Matrix.of η = 1) :
    letI := smoothLevelCharted (orth_submersive η hη hηη)
    IsManifold 𝓘(ℝ, Fin (fibreDim (Mat n) (symS n)) → ℝ) ∞ (levelSet (orthF η) (ηS η hη)) :=
  isManifold_level _

/-- Symmetric matrices are functions on unordered pairs. -/
noncomputable def symEquiv (n : ℕ) : symS n ≃ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun S := fun z => Sym2.lift ⟨fun i j => (S : Mat n) i j, fun i j => S.2 i j⟩ z
  invFun g := ⟨fun i j => g s(i, j), fun i j => by show g s(i, j) = g s(j, i); rw [Sym2.eq_swap]⟩
  map_add' S T := by funext z; induction z using Sym2.ind; rfl
  map_smul' r S := by funext z; induction z using Sym2.ind; rfl
  left_inv S := rfl
  right_inv g := by funext z; induction z using Sym2.ind; rfl

lemma finrank_symS (n : ℕ) : Module.finrank ℝ (symS n) = (n + 1).choose 2 := by
  rw [(symEquiv n).finrank_eq, Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]

/-- **`dim O(η) = n(n−1)/2`** (91 for `O(7,7)`). -/
lemma fibreDim_orth (n : ℕ) : fibreDim (Mat n) (symS n) = n.choose 2 := by
  unfold fibreDim
  have hM : Module.finrank ℝ (Mat n) = n * n := by
    simp [Mat, Module.finrank_pi_fintype]
  rw [finrank_symS, hM]
  rw [Nat.choose_two_right, Nat.choose_two_right]
  rcases n with _ | m
  · rfl
  · have h1 : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 1) * m + 2 * (m + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    have h2 : (m + 1) * (m + 1 - 1) = (m + 1) * m := by simp
    rw [h1, h2, Nat.add_mul_div_left _ _ (by norm_num)]
    have h3 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    have h4 : (m + 1) * m % 2 = 0 := by
      rw [mul_comm]; exact Nat.even_iff.mp (Nat.even_mul_succ_self m)
    omega


/-! ### Signature metrics and the group structure -/

/-- `diag(1^p, (−1)^q)`. -/
noncomputable def ηSig (p q : ℕ) : Mat (p + q) :=
  Matrix.diagonal fun i : Fin (p + q) => if (i : ℕ) < p then (1 : ℝ) else -1

lemma ηSig_mem (p q : ℕ) : ηSig p q ∈ symS (p + q) := fun i j => by
  unfold ηSig
  by_cases h : i = j
  · rw [h]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

lemma ηSig_sq (p q : ℕ) : Matrix.of (ηSig p q) * Matrix.of (ηSig p q) = 1 := by
  show Matrix.diagonal _ * Matrix.diagonal _ = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; split_ifs <;> norm_num

/-- **`O(7,7)` is a smooth manifold of dimension 91.** -/
theorem isManifold_O77 :
    letI := smoothLevelCharted (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
    IsManifold 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞
      (levelSet (orthF (ηSig 7 7)) (ηS _ (ηSig_mem 7 7))) :=
  isManifold_orth _ (ηSig_mem 7 7) (ηSig_sq 7 7)

section Group

variable (η : Mat n) (hη : η ∈ symS n) (hηη : Matrix.of η * Matrix.of η = 1)

/-- `O(η)` as a set. -/
abbrev Orth := levelSet (orthF η) (ηS η hη)

lemma mem_Orth_iff_mat (M : Mat n) :
    M ∈ levelSet (orthF η) (ηS η hη) ↔ (Matrix.of M)ᵀ * Matrix.of η * Matrix.of M = Matrix.of η := by
  rw [mem_orthLevel_iff, ← bil_eq_mat]
  exact ⟨fun h => by rw [h], fun h => Matrix.of.injective h⟩

/-- Matrix product on `Mat n`. -/
def mulM (A B : Mat n) : Mat n := Matrix.of.symm (Matrix.of A * Matrix.of B)

/-- The `O(η)` inverse `A ↦ η Aᵀ η`. -/
def invM (A : Mat n) : Mat n := Matrix.of.symm (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η)

variable {η hη}

lemma one_mem_Orth : Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℝ) ∈ Orth η hη := by
  rw [mem_Orth_iff_mat]; simp

lemma mulM_mem {A B : Mat n} (hA : A ∈ Orth η hη) (hB : B ∈ Orth η hη) :
    mulM A B ∈ Orth η hη := by
  rw [mem_Orth_iff_mat] at *
  show (Matrix.of A * Matrix.of B)ᵀ * Matrix.of η * (Matrix.of A * Matrix.of B) = _
  rw [Matrix.transpose_mul]
  calc (Matrix.of B)ᵀ * (Matrix.of A)ᵀ * Matrix.of η * (Matrix.of A * Matrix.of B)
      = (Matrix.of B)ᵀ * ((Matrix.of A)ᵀ * Matrix.of η * Matrix.of A) * Matrix.of B := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA, hB]

include hηη in
lemma invM_mul {A : Mat n} (hA : A ∈ Orth η hη) :
    Matrix.of (invM η A) * Matrix.of A = 1 := by
  rw [mem_Orth_iff_mat] at hA
  show Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η * Matrix.of A = 1
  calc Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η * Matrix.of A
      = Matrix.of η * ((Matrix.of A)ᵀ * Matrix.of η * Matrix.of A) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, hηη]

include hηη in
lemma invM_mem {A : Mat n} (hA : A ∈ Orth η hη) : invM η A ∈ Orth η hη := by
  have hl := invM_mul hηη hA
  have hr : Matrix.of A * Matrix.of (invM η A) = 1 := mul_eq_one_comm.mp hl
  have he : (Matrix.of η)ᵀ = Matrix.of η := mat_symm_of_mem hη
  rw [mem_Orth_iff_mat] at hA ⊢
  show (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η)ᵀ * Matrix.of η *
    (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η) = Matrix.of η
  have hr' : Matrix.of A * (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η) = 1 := hr
  rw [Matrix.transpose_mul, Matrix.transpose_mul, he, Matrix.transpose_transpose]
  calc _
      = Matrix.of η * (Matrix.of A * (Matrix.of η * Matrix.of η) *
          (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.of η := by rw [hηη, Matrix.mul_one, hr', Matrix.mul_one]

noncomputable instance : Mul (Orth η hη) := ⟨fun A B => ⟨mulM A B, mulM_mem A.2 B.2⟩⟩
noncomputable instance : One (Orth η hη) := ⟨⟨_, one_mem_Orth⟩⟩

lemma Orth.mul_val (A B : Orth η hη) : ((A * B : Orth η hη) : Mat n) = mulM A B := rfl
lemma Orth.one_val : ((1 : Orth η hη) : Mat n) = Matrix.of.symm 1 := rfl

variable (hη) in
/-- The inverse on `O(η)`. -/
@[instance_reducible] noncomputable def orthInv : Inv (Orth η hη) :=
  ⟨fun A => ⟨invM η A, invM_mem hηη A.2⟩⟩

variable (hη) in
lemma Orth.inv_val (A : Orth η hη) :
    letI := orthInv hη hηη
    ((A⁻¹ : Orth η hη) : Mat n) = invM η A := rfl

variable (hη) in
/-- **`O(η)` is a group** under matrix multiplication. -/
@[instance_reducible] noncomputable def orthGroup : Group (Orth η hη) :=
  letI := orthInv hη hηη
  Group.ofLeftAxioms
    (fun A B C => Subtype.ext (Matrix.of.injective
      (Matrix.mul_assoc (Matrix.of (A : Mat n)) (Matrix.of (B : Mat n)) (Matrix.of (C : Mat n)))))
    (fun A => Subtype.ext (Matrix.of.injective (Matrix.one_mul (Matrix.of (A : Mat n)))))
    (fun A => Subtype.ext (Matrix.of.injective (invM_mul hηη A.2)))


/-! ### `O(η)` is a Lie group -/

/-- The continuous bilinear matrix product on `Mat n`. -/
noncomputable def mulCL (n : ℕ) : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun A C i j => ∑ k, A i k * C k j)
        (fun A A' C => by ext i j; simp [add_mul, Finset.sum_add_distrib])
        (fun r A C => by ext i j; simp [Finset.mul_sum, mul_assoc])
        (fun A C C' => by ext i j; simp [mul_add, Finset.sum_add_distrib])
        (fun r A C => by
          ext i j; simp [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring))

lemma mulM_eq (A B : Mat n) : mulM A B = mulCL n A B := by
  funext i j; simp [mulM, mulCL, Matrix.mul_apply]

/-- The continuous linear map `A ↦ η Aᵀ η`. -/
noncomputable def invCL (η : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := invM η
      map_add' := fun A B => by
        apply Matrix.of.injective
        show Matrix.of η * (Matrix.of A + Matrix.of B)ᵀ * Matrix.of η =
          Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η + Matrix.of η * (Matrix.of B)ᵀ * Matrix.of η
        rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r A => by
        apply Matrix.of.injective
        show Matrix.of η * (r • Matrix.of A)ᵀ * Matrix.of η = r • (Matrix.of η * (Matrix.of A)ᵀ * Matrix.of η)
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul] }

lemma invCL_apply (η A : Mat n) : invCL η A = invM η A := rfl

include hηη in
variable (hη) in
/-- **`O(η)` is a Lie group** (for symmetric `η` with `η² = 1`); in particular `O(7,7)`. -/
theorem lieGroup_orth :
    letI := smoothLevelCharted (orth_submersive η hη hηη)
    letI := orthGroup hη hηη
    LieGroup 𝓘(ℝ, Fin (fibreDim (Mat n) (symS n)) → ℝ) ∞ (Orth η hη) := by
  let _ := smoothLevelCharted (orth_submersive η hη hηη)
  let _ := orthGroup hη hηη
  have hM := isManifold_orth η hη hηη
  have hv := contMDiff_levelSet_val (orth_submersive η hη hηη)
  refine { toIsManifold := hM, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · rw [contMDiff_levelSet_iff]
    have : (fun p : Orth η hη × Orth η hη => ((p.1 * p.2 : Orth η hη) : Mat n)) =
        fun p => mulCL n (p.1 : Mat n) (p.2 : Mat n) := by
      funext p; exact mulM_eq _ _
    rw [this]
    exact (mulCL n).isBoundedBilinearMap.contDiff.comp_contMDiff
      ((hv.comp contMDiff_fst).prodMk_space (hv.comp contMDiff_snd))
  · rw [contMDiff_levelSet_iff]
    exact (invCL η).contDiff.comp_contMDiff hv

end Group

/-- **`O(7,7)` is a 91-dimensional Lie group.** -/
theorem lieGroup_O77 :
    letI := smoothLevelCharted (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))
    letI := orthGroup (ηSig_mem 7 7) (ηSig_sq 7 7)
    LieGroup 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ (Orth (ηSig 7 7) (ηSig_mem 7 7)) :=
  lieGroup_orth (ηSig_mem 7 7) (ηSig_sq 7 7)

lemma dim_O77 : fibreDim (Mat 14) (symS 14) = 91 := by rw [fibreDim_orth]; rfl

/-! ### The concrete `O(7,7)` with global instances -/

/-- The `(7,7)` metric on `ℝ¹⁴` (as `Mat 14`). -/
noncomputable abbrev η77 : Mat 14 := ηSig 7 7

/-- **`O(7,7)`** `= {M | Mᵀ η₇₇ M = η₇₇}`, carrying global group, charted-space and Lie group
instances (model `Fin (fibreDim (Mat 14) (symS 14)) → ℝ`, of dimension 91 by `dim_O77`). -/
abbrev O77 := Orth η77 (ηSig_mem 7 7)

noncomputable instance : Group O77 := orthGroup (ηSig_mem 7 7) (ηSig_sq 7 7)

noncomputable instance : ChartedSpace (Fin (fibreDim (Mat 14) (symS 14)) → ℝ) O77 :=
  smoothLevelCharted (orth_submersive _ (ηSig_mem 7 7) (ηSig_sq 7 7))

instance : LieGroup 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ O77 :=
  lieGroup_orth (ηSig_mem 7 7) (ηSig_sq 7 7)

example : IsManifold 𝓘(ℝ, Fin (fibreDim (Mat 14) (symS 14)) → ℝ) ∞ O77 := inferInstance

end GU.Library
