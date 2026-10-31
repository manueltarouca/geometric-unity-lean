import GU.Observerse.ChimericFiber

/-!
# The chimeric metric on the fibers of `C` over `Y` (contravariant coordinates)

A point of `Y` is a contravariant Lorentzian tensor `G = g⁻¹` (`GlobalSmooth.lean`). The draft's `Y`
consists of covariant metrics `g`; the two are identified by the fibrewise inversion `g ↦ g⁻¹`,
under which DeWitt (`λ = 1`) on covariant `h` becomes the formula below on contravariant `A = δG`
(`δG = −G h G`), and the inverse metric on `H*` is `g^{ab} p_a q_b = pᵀ G q`. That identification is
stated, not formalised. On the fiber
`C_y = Sym² ⊕ (ℝ⁴)*` the chimeric metric (DeWitt `λ = 1` plus inverse metric) reads
`F_G((A,p),(B,q)) = tr(gAgB) − tr(gA)tr(gB) + pᵀ G q` with `g = G⁻¹`.

`chimY_transport`: for `G = P η Pᵀ`, the map `(A, p) ↦ (P A Pᵀ, P⁻ᵀ p)` is an isometry from the
model at `η` (where `F_η` is `chimFormR 1 ηR`). So `chimY_signature`: at every (1,3) point of `Y`,
the transported basis is orthogonal with norms `chimNorms` (7 positive, 7 negative), i.e.
`C` has signature (7,7) over the (1,3) component of `Y`.
-/

namespace GU.Chimeric

open Matrix

/-- The chimeric form at a contravariant point `G` (with `g = G⁻¹`). -/
noncomputable def chimY (G : Matrix (Fin 4) (Fin 4) ℝ)
    (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) : ℝ :=
  trace (G⁻¹ * x.1 * G⁻¹ * y.1) - trace (G⁻¹ * x.1) * trace (G⁻¹ * y.1) + x.2 ⬝ᵥ (G *ᵥ y.2)

/-- Transport `(A, p) ↦ (P A Pᵀ, P⁻ᵀ p)`. -/
noncomputable def transportY (P : Matrix (Fin 4) (Fin 4) ℝ)
    (x : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ) :=
  (P * x.1 * Pᵀ, Pᵀ⁻¹ *ᵥ x.2)

lemma ηR_inv : ηR⁻¹ = ηR := by
  have h : ηR * ηR = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ηR, ηZ, mul_apply, diagonal]
  exact inv_eq_left_inv h

theorem chimY_transport (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P)
    (x y : Matrix (Fin 4) (Fin 4) ℝ × (Fin 4 → ℝ)) :
    chimY (P * ηR * Pᵀ) (transportY P x) (transportY P y) = chimFormR 1 ηR x y := by
  have hPd : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
  have hinv : (P * ηR * Pᵀ)⁻¹ = Pᵀ⁻¹ * ηR * P⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ηR_inv, Matrix.mul_assoc]
  have h1 : P⁻¹ * P = 1 := nonsing_inv_mul _ hPd
  have h2 : Pᵀ * Pᵀ⁻¹ = 1 := mul_nonsing_inv _ hPt
  have key : ∀ A : Matrix (Fin 4) (Fin 4) ℝ,
      Pᵀ⁻¹ * ηR * P⁻¹ * (P * A * Pᵀ) = Pᵀ⁻¹ * (ηR * A) * Pᵀ := by
    intro A
    calc Pᵀ⁻¹ * ηR * P⁻¹ * (P * A * Pᵀ) = Pᵀ⁻¹ * ηR * (P⁻¹ * P) * A * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have tr_conj : ∀ M : Matrix (Fin 4) (Fin 4) ℝ, trace (Pᵀ⁻¹ * M * Pᵀ) = trace M := by
    intro M; rw [trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [chimY, chimFormR, transportY, hinv]
  have e1 : Pᵀ⁻¹ * ηR * P⁻¹ * (P * x.1 * Pᵀ) * (Pᵀ⁻¹ * ηR * P⁻¹) * (P * y.1 * Pᵀ)
      = Pᵀ⁻¹ * (ηR * x.1 * ηR * y.1) * Pᵀ := by
    rw [key, Matrix.mul_assoc (Pᵀ⁻¹ * (ηR * x.1) * Pᵀ), key]
    calc Pᵀ⁻¹ * (ηR * x.1) * Pᵀ * (Pᵀ⁻¹ * (ηR * y.1) * Pᵀ)
        = Pᵀ⁻¹ * (ηR * x.1) * (Pᵀ * Pᵀ⁻¹) * (ηR * y.1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, tr_conj, key, key, tr_conj, tr_conj, one_mul]
  congr 1
  rw [mulVec_mulVec, show P * ηR * Pᵀ * Pᵀ⁻¹ = P * ηR by rw [Matrix.mul_assoc, h2, Matrix.mul_one],
    ← mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, transpose_nonsing_inv, transpose_transpose,
    vecMul_vecMul, nonsing_inv_mul _ hPd, vecMul_one]

/-- **(7,7) on every (1,3) fiber of `C` over `Y`.** -/
theorem chimY_signature (P : Matrix (Fin 4) (Fin 4) ℝ) (hP : IsUnit P) (i j : Fin 14) :
    chimY (P * ηR * Pᵀ)
        (transportY P ((chimBasis i).1.map (Int.castRingHom ℝ), fun k => ((chimBasis i).2 k : ℝ)))
        (transportY P ((chimBasis j).1.map (Int.castRingHom ℝ), fun k => ((chimBasis j).2 k : ℝ)))
      = if i = j then (chimNorms i : ℝ) else 0 := by
  rw [chimY_transport P hP, chimFormR_cast, chimBasis_gram]; split_ifs <;> simp

end GU.Chimeric
