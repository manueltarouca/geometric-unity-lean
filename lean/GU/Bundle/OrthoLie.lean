import GU.Bundle.OrthoM
import GU.Library.Orthogonal

/-!
# Track 3, L4a: the frame-bundle structure group `O(Bη)` is the Lie group `O(7,7)`

`Bm x y = x ⬝ᵥ η y` with `η = ηSig 7 7` is the bilinear form of `Q77` (`Q77_eq_Bm`), transported
to the chimeric `Bη` by `Φ` (`Bη_Φ_eq`), and
`M ∈ O(η) ↔ M` preserves `Bm` (`mem_Orth_iff_Bm`). Conjugation by `Φ : ℝ¹⁴ ≃ CFib` then identifies
`O(η)` with the structure group `OG = O(Bη)` of `orthoFrameBundle` (`orthOGEquiv`), so `OG` is, as a group,
the 91-dimensional Lie group `O77`. (`GLC` has no topology, so smooth bundle work should use `O77`
and transport along `orthOGEquiv`.)
-/

namespace GU.Library

open Matrix GU GU.Observerse

/-- The `(7,7)` bilinear form `x ⬝ᵥ η₇₇ y` on `ℝ¹⁴`. -/
noncomputable def Bm (x y : Fin 14 → ℝ) : ℝ := x ⬝ᵥ (Matrix.of η77 *ᵥ y)

lemma η77_apply (i j : Fin 14) :
    Matrix.of η77 i j = if i = j then (if (i : ℕ) < 7 then 1 else -1) else 0 := by
  show Matrix.diagonal _ i j = _
  rw [Matrix.diagonal_apply]

lemma Bm_comm (x y : Fin 14 → ℝ) : Bm x y = Bm y x := by
  unfold Bm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    mat_symm_of_mem (ηSig_mem 7 7)]

lemma Q77_eq_Bm (x : Fin 14 → ℝ) : Q77 x = Bm x x := by
  unfold Bm
  simp only [Q77, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, dotProduct, mulVec,
    η77_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_mul, Finset.sum_ite_eq]

lemma Bη_Φ_eq (x y : Fin 14 → ℝ) : Bη (ΦL x) (ΦL y) = Bm x y := by
  rw [Bη_Φ, QuadraticMap.polar, Q77_eq_Bm, Q77_eq_Bm, Q77_eq_Bm]
  unfold Bm
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  have := Bm_comm y x; unfold Bm at this
  rw [this]; ring

/-- `x ⬝ᵥ N *ᵥ y` on basis vectors is the entry `N i j`. -/
lemma single_dot_mulVec (N : Matrix (Fin 14) (Fin 14) ℝ) (i j : Fin 14) :
    Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) = N i j := by
  rw [mulVec_single_one, single_one_dotProduct]; rfl

lemma Bm_mulVec (M : Matrix (Fin 14) (Fin 14) ℝ) (x y : Fin 14 → ℝ) :
    Bm (M *ᵥ x) (M *ᵥ y) = x ⬝ᵥ ((Mᵀ * Matrix.of η77 * M) *ᵥ y) := by
  unfold Bm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Mᵀ, vecMul_transpose]

/-- Matrix membership in `O(7,7)` is preservation of `Bm`. -/
lemma mem_Orth_iff_Bm (M : Mat 14) :
    M ∈ O77 ↔ ∀ x y, Bm (Matrix.of M *ᵥ x) (Matrix.of M *ᵥ y) = Bm x y := by
  rw [mem_Orth_iff_mat]
  constructor
  · intro h x y; rw [Bm_mulVec, h]; rfl
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [Bm_mulVec, single_dot_mulVec] at this
    rw [this]; unfold Bm; rw [single_dot_mulVec]


/-- An element of `O(7,7)` as a linear automorphism of `ℝ¹⁴`. -/
noncomputable def matEquiv (M : O77) : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ) :=
  have hl : Matrix.of (invM η77 M) * Matrix.of (M : Mat 14) = 1 := invM_mul (ηSig_sq 7 7) M.2
  have hr : Matrix.of (M : Mat 14) * Matrix.of (invM η77 M) = 1 := mul_eq_one_comm.mp hl
  LinearEquiv.ofLinearMap (Matrix.toLin' (Matrix.of (M : Mat 14))) (Matrix.toLin' (Matrix.of (invM η77 M)))
    (by rw [← Matrix.toLin'_mul, hr, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hl, Matrix.toLin'_one])

lemma matEquiv_apply (M : O77) (x : Fin 14 → ℝ) :
    matEquiv M x = Matrix.of (M : Mat 14) *ᵥ x := Matrix.toLin'_apply _ _

/-- Conjugation by `Φ`. -/
noncomputable def conjΦ (A : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) : GLC :=
  ΦL.symm.toLinearEquiv.trans (A.trans ΦL.toLinearEquiv)

lemma conjΦ_apply (A : (Fin 14 → ℝ) ≃ₗ[ℝ] (Fin 14 → ℝ)) (u : CFib) :
    conjΦ A u = ΦL (A (ΦL.symm u)) := rfl

lemma conjΦ_mem (M : O77) : conjΦ (matEquiv M) ∈ OG := fun u v => by
  rw [conjΦ_apply, conjΦ_apply, Bη_Φ_eq, matEquiv_apply, matEquiv_apply,
    (mem_Orth_iff_Bm _).mp M.2, ← Bη_Φ_eq, ΦL.apply_symm_apply, ΦL.apply_symm_apply]

/-- **`O(7,7) →* O(Bη)`**, `M ↦ Φ M Φ⁻¹`. -/
noncomputable def orthToOG : O77 →* ↥OG where
  toFun M := ⟨conjΦ (matEquiv M), conjΦ_mem M⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro u
    show ΦL (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 14) (Fin 14) ℝ)) *ᵥ ΦL.symm u) = u
    simp
  map_mul' A B := by
    apply Subtype.ext; apply LinearEquiv.ext; intro u
    show ΦL (Matrix.of (mulM (A : Mat 14) B) *ᵥ ΦL.symm u) =
      ΦL (Matrix.of (A : Mat 14) *ᵥ ΦL.symm (ΦL (Matrix.of (B : Mat 14) *ᵥ ΦL.symm u)))
    rw [ΦL.symm_apply_apply]
    show ΦL ((Matrix.of (A : Mat 14) * Matrix.of (B : Mat 14)) *ᵥ ΦL.symm u) = _
    rw [← mulVec_mulVec]

lemma orthToOG_apply (M : O77) (u : CFib) :
    (orthToOG M : GLC) u = ΦL (Matrix.of (M : Mat 14) *ᵥ ΦL.symm u) := rfl

lemma orthToOG_injective : Function.Injective orthToOG := by
  intro A B h
  have hx : ∀ x, Matrix.of (A : Mat 14) *ᵥ x = Matrix.of (B : Mat 14) *ᵥ x := fun x => by
    have := congrArg (fun g : ↥OG => (g : GLC) (ΦL x)) h
    simp only [orthToOG_apply, ΦL.symm_apply_apply] at this
    exact ΦL.injective this
  apply Subtype.ext
  have : Matrix.of (A : Mat 14) = Matrix.of (B : Mat 14) := by
    ext i j
    have := congrFun (hx (Pi.single j 1)) i
    simpa [mulVec_single_one] using this
  exact this

/-- The matrix of `Φ⁻¹ A Φ`. -/
noncomputable def ogMat (A : ↥OG) : Mat 14 :=
  Matrix.of.symm (LinearMap.toMatrix'
    (ΦL.symm.toLinearEquiv.toLinearMap ∘ₗ (A : GLC).toLinearMap ∘ₗ ΦL.toLinearEquiv.toLinearMap))

lemma ogMat_mulVec (A : ↥OG) (x : Fin 14 → ℝ) :
    Matrix.of (ogMat A) *ᵥ x = ΦL.symm ((A : GLC) (ΦL x)) := by
  unfold ogMat
  rw [Equiv.apply_symm_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

lemma ogMat_mem (A : ↥OG) : ogMat A ∈ O77 := by
  rw [mem_Orth_iff_Bm]
  intro x y
  rw [ogMat_mulVec, ogMat_mulVec, ← Bη_Φ_eq, ΦL.apply_symm_apply, ΦL.apply_symm_apply, A.2,
    Bη_Φ_eq]

lemma orthToOG_surjective : Function.Surjective orthToOG := by
  intro A
  refine ⟨⟨ogMat A, ogMat_mem A⟩, Subtype.ext (LinearEquiv.ext fun u => ?_)⟩
  rw [orthToOG_apply]
  show ΦL (Matrix.of (ogMat A) *ᵥ ΦL.symm u) = (A : GLC) u
  rw [ogMat_mulVec, ΦL.apply_symm_apply, ΦL.apply_symm_apply]

/-- **`O(7,7) ≃* O(Bη)`**: the structure group of `orthoFrameBundle` is the matrix group `O(7,7)`. -/
noncomputable def orthOGEquiv : O77 ≃* ↥OG :=
  MulEquiv.ofBijective orthToOG ⟨orthToOG_injective, orthToOG_surjective⟩

end GU.Library
