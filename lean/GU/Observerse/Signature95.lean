import GU.Observerse.ChimericBasis

/-!
# At (3,1) points the chimeric form is not isometric to the (7,7) model

At `g = −η` the DeWitt part of the chimeric form is unchanged (even in `g`) and the `H*` part flips
sign, giving `chimBm`. On the same basis `chimVec` its Gram matrix is diagonal with norms
`chimNormsM` (9 positive, 5 negative; `chimBmZ_gram`, by `decide`).

**`no_isometry_95`**: there is no linear map `B` with `chimB (B x) (B x) = chimBm x x`. Proof without
Sylvester's law: the images of the 9 `chimBm`-positive basis vectors and the 7 `chimB`-negative basis
vectors are 16 vectors in a 14-dimensional space, hence dependent; a dependence gives a nonzero
`v` with `chimBm v v > 0` and `chimB (B v) (B v) ≤ 0`.
-/

namespace GU.Chimeric

open Matrix GU.Observerse

/-- The chimeric form at `g = −η` (`λ = 1`). -/
noncomputable def chimBm : LinearMap.BilinForm ℝ E14 :=
  LinearMap.mk₂ ℝ
    (fun x y => trace (ηr * symMat x.2 * ηr * symMat y.2) - trace (ηr * symMat x.2) * trace (ηr * symMat y.2)
      + x.1 ⬝ᵥ ((-ηr) *ᵥ y.1))
    (fun x x' y => by
      simp only [Prod.snd_add, Prod.fst_add, symMat_add, Matrix.mul_add, Matrix.add_mul, trace_add,
        add_dotProduct]; ring)
    (fun c x y => by
      simp only [Prod.smul_snd, Prod.smul_fst, symMat_smul, Matrix.mul_smul, Matrix.smul_mul, trace_smul,
        smul_dotProduct, smul_eq_mul]; ring)
    (fun x y y' => by
      simp only [Prod.snd_add, Prod.fst_add, symMat_add, Matrix.mul_add, trace_add,
        mulVec_add, dotProduct_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_snd, Prod.smul_fst, symMat_smul, Matrix.mul_smul, trace_smul,
        mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)

def chimBmZ (x y : (Fin 4 → ℤ) × (Fin 10 → ℤ)) : ℤ :=
  let sx : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j => x.2 (symIdx i j)
  let sy : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j => y.2 (symIdx i j)
  trace (ηZ * sx * ηZ * sy) - trace (ηZ * sx) * trace (ηZ * sy) + x.1 ⬝ᵥ ((-ηZ) *ᵥ y.1)

def chimNormsM : Fin 14 → ℤ := ![-2, -2, -2, 2, 2, 2, -12, 2, 6, 12, -1, 1, 1, 1]

theorem chimBmZ_gram : ∀ i j : Fin 14,
    chimBmZ (chimCoord i) (chimCoord j) = if i = j then chimNormsM i else 0 := by decide

lemma chimBm_cast (i j : Fin 14) :
    chimBm (chimVec i) (chimVec j) = (chimBmZ (chimCoord i) (chimCoord j) : ℝ) := by
  simp only [chimBm, LinearMap.mk₂_apply, chimBmZ, chimVec, ηr, ηZ, symMat]
  simp [trace, Fin.sum_univ_four, mul_apply, dotProduct, mulVec, diagonal]

theorem chimBm_basis (i j : Fin 14) :
    chimBm (chimVec i) (chimVec j) = if i = j then (chimNormsM i : ℝ) else 0 := by
  rw [chimBm_cast, chimBmZ_gram]; split_ifs <;> simp

/-- Diagonal Gram ⇒ the quadratic form is a weighted sum of squares. -/
lemma quad_diag {ι : Type} [Fintype ι] [DecidableEq ι] (F : LinearMap.BilinForm ℝ E14) (v : ι → E14)
    (n : ι → ℝ) (hF : ∀ i j, F (v i) (v j) = if i = j then n i else 0) (a : ι → ℝ) :
    F (∑ i, a i • v i) (∑ i, a i • v i) = ∑ i, a i ^ 2 * n i := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp; ring

def posM : Fin 9 → Fin 14 := ![3, 4, 5, 7, 8, 9, 11, 12, 13]
def negP : Fin 7 → Fin 14 := ![0, 1, 2, 6, 11, 12, 13]

lemma posM_inj : Function.Injective posM := by decide
lemma negP_inj : Function.Injective negP := by decide
lemma posM_pos : ∀ i, 0 < chimNormsM (posM i) := by decide
lemma negP_neg : ∀ j, chimNorms (negP j) < 0 := by decide

/-- **No isometry from the (3,1)-point form onto the (7,7) model.** -/
theorem no_isometry_95 (B : E14 →ₗ[ℝ] E14) (hB : ∀ x, chimB (B x) (B x) = chimBm x x) : False := by
  let f : Fin 9 ⊕ Fin 7 → E14 := Sum.elim (fun i => B (chimVec (posM i))) (fun j => chimVec (negP j))
  have hnot : ¬ LinearIndependent ℝ f := fun h => by
    have := h.fintype_card_le_finrank
    rw [finrank_E14] at this
    simp at this
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hnot
  rw [Fintype.sum_sum_type] at hg
  simp only [f, Sum.elim_inl, Sum.elim_inr] at hg
  set a : Fin 9 → ℝ := fun i => g (Sum.inl i)
  set b : Fin 7 → ℝ := fun j => g (Sum.inr j)
  set v : E14 := ∑ i, a i • chimVec (posM i)
  have hBv : B v = ∑ j, (-b j) • chimVec (negP j) := by
    simp only [v, map_sum, map_smul, neg_smul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hg
  have hdP : ∀ i j, chimBm (chimVec (posM i)) (chimVec (posM j)) = if i = j then (chimNormsM (posM i) : ℝ) else 0 :=
    fun i j => by rw [chimBm_basis]; simp [posM_inj.eq_iff]
  have hdN : ∀ i j, chimB (chimVec (negP i)) (chimVec (negP j)) = if i = j then (chimNorms (negP i) : ℝ) else 0 :=
    fun i j => by rw [chimB_basis]; simp [negP_inj.eq_iff]
  have hQ := hB v
  rw [hBv, quad_diag _ _ _ hdN, quad_diag _ _ _ hdP] at hQ
  have hle : ∑ j, (-b j) ^ 2 * (chimNorms (negP j) : ℝ) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (by exact_mod_cast (negP_neg j).le)
  have ha : a ≠ 0 := by
    intro ha0
    have hb0 : ∑ j, b j • chimVec (negP j) = 0 := by
      have : ∑ i, a i • chimVec (posM i) = 0 := by simp [ha0]
      have h2 := hg
      simp only [a] at this
      rw [show (∑ i, g (Sum.inl i) • B (chimVec (posM i))) = B (∑ i, g (Sum.inl i) • chimVec (posM i)) by
        simp [map_sum], this, map_zero, zero_add] at h2
      exact h2
    have hli := (chimVec_linIndep.comp negP negP_inj)
    have hb : b = 0 := funext fun j => Fintype.linearIndependent_iff.mp hli b hb0 j
    rcases k with i | j
    · exact hk (congrFun ha0 i)
    · exact hk (congrFun hb j)
  have hpos : 0 < ∑ i, a i ^ 2 * (chimNormsM (posM i) : ℝ) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    refine Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (by exact_mod_cast (posM_pos j).le))
      ⟨i, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (by simpa using hi))))
        (by exact_mod_cast posM_pos i)⟩
  linarith

end GU.Chimeric
