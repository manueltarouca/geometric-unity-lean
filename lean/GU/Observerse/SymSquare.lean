import GU.Observerse.Global

/-!
# The symmetric square of a rank-4 vector bundle core

For a vector bundle core `Z` with fiber `ℝ⁴`, `symCore Z` has fiber `ℝ¹⁰` (symmetric 4×4 matrices in
`symMat` coordinates) and transition maps `A ↦ T A Tᵀ`, where `T` are the transitions of `Z`. The
cocycle law follows from that of `Z` because `symAct` is multiplicative (`symAct_mul`).
Applied to `tangentBundleCore` this is `Sym²(TX)`, the bundle of contravariant symmetric 2-tensors
(inverse metrics); the observerse `Met(X)` is the open set of Lorentzian ones (via `g ↦ g⁻¹`).
-/

namespace GU.Observerse

open Matrix

/-- Coordinates of a (symmetric) matrix. -/
def symCoords (A : Matrix (Fin 4) (Fin 4) ℝ) : Fin 10 → ℝ :=
  fun k => A (![0, 0, 0, 0, 1, 1, 1, 2, 2, 3] k) (![0, 1, 2, 3, 1, 2, 3, 2, 3, 3] k)

lemma symCoords_symMat (v : Fin 10 → ℝ) : symCoords (symMat v) = v := by
  ext k; fin_cases k <;> rfl

lemma symMat_symCoords (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.IsSymm) : symMat (symCoords A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat, symCoords, symIdx] <;> exact (hA.apply _ _).symm

/-- The matrix of a linear endomorphism of `ℝ⁴`. -/
def mat (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))

lemma mat_comp (T S : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : mat (T.comp S) = mat T * mat S := by
  simp [mat, LinearMap.toMatrix'_comp]

lemma mat_id : mat (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) = 1 := by
  simp [mat, LinearMap.toMatrix'_id]

/-- Action on symmetric-matrix coordinates: `v ↦ coords(M · symMat v · Mᵀ)`. -/
def symActL (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun v := symCoords (mat T * symMat v * (mat T)ᵀ)
  map_add' u v := by
    have : symMat (u + v) = symMat u + symMat v := by ext i j; simp [symMat]
    ext k; simp [symCoords, this, Matrix.mul_add, Matrix.add_mul]
  map_smul' c v := by
    have : symMat (c • v) = c • symMat v := by ext i j; simp [symMat]
    ext k; simp [symCoords, this]

noncomputable def symAct (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) : (Fin 10 → ℝ) →L[ℝ] (Fin 10 → ℝ) :=
  LinearMap.toContinuousLinearMap (symActL T)

lemma symAct_apply (T) (v : Fin 10 → ℝ) : symAct T v = symCoords (mat T * symMat v * (mat T)ᵀ) := rfl

lemma symAct_id (v : Fin 10 → ℝ) : symAct (ContinuousLinearMap.id ℝ _) v = v := by
  rw [symAct_apply, mat_id]; simp [symCoords_symMat]

lemma symAct_comp (T S : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (v : Fin 10 → ℝ) :
    symAct T (symAct S v) = symAct (T.comp S) v := by
  rw [symAct_apply, symAct_apply, symAct_apply, mat_comp]
  have hs : (mat S * symMat v * (mat S)ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm v).eq, Matrix.mul_assoc]
  rw [symMat_symCoords _ hs, transpose_mul]
  simp only [Matrix.mul_assoc]

end GU.Observerse

namespace GU.Observerse

open Matrix Bundle

theorem symAct_contDiff : ContDiff ℝ ⊤ symAct := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_pi]
  intro k
  have hev : ∀ (w : Fin 4 → ℝ) (a : Fin 4),
      ContDiff ℝ ⊤ (fun x : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) => x w a) := fun w a =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a).comp
      (ContinuousLinearMap.apply ℝ (Fin 4 → ℝ) w)).contDiff
  simp only [symAct_apply, symCoords, mat, LinearMap.toMatrix'_apply, mul_apply, transpose_apply,
    symMat, of_apply, ContinuousLinearMap.coe_coe]
  fun_prop

variable {B ι : Type*} [TopologicalSpace B]

/-- The symmetric square of a rank-4 vector bundle core. -/
noncomputable def symCore (Z : VectorBundleCore ℝ B (Fin 4 → ℝ) ι) :
    VectorBundleCore ℝ B (Fin 10 → ℝ) ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := symAct (Z.coordChange i j x)
  coordChange_self i x hx v := by
    have : Z.coordChange i i x = ContinuousLinearMap.id ℝ _ := by
      ext w; simp [Z.coordChange_self i x hx]
    rw [this, symAct_id]
  continuousOn_coordChange i j :=
    symAct_contDiff.continuous.comp_continuousOn (Z.continuousOn_coordChange i j)
  coordChange_comp i j k x hx v := by
    have hc : (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x := by
      ext w : 1; exact Z.coordChange_comp i j k x hx w
    rw [symAct_comp, hc]

lemma det_symAct (T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (v : Fin 10 → ℝ) :
    (symMat (symAct T v)).det = (mat T).det ^ 2 * (symMat v).det := by
  have hs : (mat T * symMat v * (mat T)ᵀ).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, (symMat_isSymm v).eq, Matrix.mul_assoc]
  rw [symAct_apply, symMat_symCoords _ hs, det_mul, det_mul, det_transpose]; ring

/-- Lorentzian points (`det < 0`) of the total space. -/
def lorSet (Z : VectorBundleCore ℝ B (Fin 4 → ℝ) ι) : Set (TotalSpace (Fin 10 → ℝ) (symCore Z).Fiber) :=
  {p | (symMat p.2).det < 0}

lemma mat_coordChange_det_ne (Z : VectorBundleCore ℝ B (Fin 4 → ℝ) ι) (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) : (mat (Z.coordChange i j x)).det ≠ 0 := by
  have hc : (Z.coordChange j i x).comp (Z.coordChange i j x) = ContinuousLinearMap.id ℝ _ := by
    ext w : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [Z.coordChange_comp i j i x ⟨hx, hx.1⟩ w, Z.coordChange_self i x hx.1 w]
  have := congrArg (fun T => (mat T).det) hc
  simp only [mat_comp, det_mul, mat_id, det_one] at this
  exact right_ne_zero_of_mul_eq_one this

theorem isOpen_lorSet (Z : VectorBundleCore ℝ B (Fin 4 → ℝ) ι) : IsOpen (lorSet Z) := by
  have key : lorSet Z = ⋃ i, ((symCore Z).localTriv i).source ∩
      ((symCore Z).localTriv i) ⁻¹' (Set.univ ×ˢ {w | (symMat w).det < 0}) := by
    ext p
    simp only [lorSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_prod, Set.mem_univ, true_and, VectorBundleCore.localTriv_apply,
      VectorBundleCore.mem_localTriv_source]
    constructor
    · intro h
      refine ⟨Z.indexAt p.1, Z.mem_baseSet_at p.1, ?_⟩
      change (symMat (symAct (Z.coordChange (Z.indexAt p.1) (Z.indexAt p.1) p.1)
        (p.2 : Fin 10 → ℝ))).det < 0
      have : Z.coordChange (Z.indexAt p.1) (Z.indexAt p.1) p.1 = ContinuousLinearMap.id ℝ _ := by
        ext w; simp [Z.coordChange_self _ p.1 (Z.mem_baseSet_at p.1)]
      rw [this]
      have e : ∀ v : Fin 10 → ℝ, (symMat (symAct (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) v)).det
          = (symMat v).det := fun v => by rw [symAct_id]
      exact (e p.2).trans_lt h
    · rintro ⟨i, hi, h⟩
      have h' : (symMat (symAct (Z.coordChange (Z.indexAt p.1) i p.1) (p.2 : Fin 10 → ℝ))).det < 0 := h
      have eq := det_symAct (Z.coordChange (Z.indexAt p.1) i p.1) p.2
      have hne := mat_coordChange_det_ne Z (Z.indexAt p.1) i p.1 ⟨Z.mem_baseSet_at p.1, hi⟩
      have hpos : 0 < (mat (Z.coordChange (Z.indexAt p.1) i p.1)).det ^ 2 := by positivity
      by_contra hc0
      have hc := not_lt.mp hc0
      have : 0 ≤ (mat (Z.coordChange (Z.indexAt p.1) i p.1)).det ^ 2 * (symMat p.2).det :=
        mul_nonneg hpos.le hc
      linarith [eq ▸ h']
  rw [key]
  exact isOpen_iUnion fun i => ((symCore Z).localTriv i).continuousOn.isOpen_inter_preimage
    ((symCore Z).localTriv i).open_source
    (isOpen_univ.prod (isOpen_lt (continuous_symMat.matrix_det) continuous_const))

end GU.Observerse
