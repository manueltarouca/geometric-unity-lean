import GU.Spinor.Reductions
import GU.Spinor.Branching
import GU.Shiab.Einstein
import GU.Observerse.Chimeric

/-!
# Synthetic predictions: what the compiled model forces

Each item is a *theorem about the formal model*. The "prediction" is its physical reading
under the draft's dictionary. None of them is a claim that nature behaves this way.

1. **Extra neutral gauge boson (Z′-type).** In `u(3) ⊕ u(2) ⊂ spin(6,4)` there are two
   independent central `u(1)` generators, `J₊` (three positive planes) and `J₋` (two negative
   planes). Hypercharge is one combination; the orthogonal one is an extra abelian gauge field.
   (`center_two_u1`)
2. **Mirror ("looking-glass") sector of equal size.** Each of the four joint chirality sectors
   `(±,±)` of `S̸(Y)` has dimension 32 = 2·16. The dark sector is exactly as large as the
   luminous one. (`four_sectors_equal`)
3. **Spin-3/2 surplus.** Clifford multiplication `TY ⊗ S̸ → S̸` is onto. Its kernel (the
   Rarita–Schwinger part of `ζ`) has dimension `13·128 = 1664`, and under `TY = TX ⊕ N` it
   splits as `R(X)⊗S(N) ⊕ S(X)⊗R(N) ⊕ S(X)⊗S(N) = 384 + 1152 + 128` (draft (11.3)). The last
   128 is the extra spin-½-looking copy, the draft's "imposter generation". (`rs_kernel_dim`,
   `rs_branching_count`)
4. **Gravity constraints.** An Einstein tensor emerges from (9.3) only with *mixed* brackets
   (`shiab_einstein`), and the fiber metric must have DeWitt `λ > 1/4` (`trace_direction_neg_iff`).
   At `λ = 1` the chimeric signature is (7,7) (`chim_signature`).
-/

namespace GU.Predictions

open GU.Spinor GU.Spinor.CSum Matrix

/-- `J₊`: rotation generator of the three positive planes. -/
def Jpos : CSum := (planes.take 3).flatMap fun p => biv p.1 p.2
/-- `J₋`: rotation generator of the two negative planes. -/
def Jneg : CSum := (planes.drop 3).flatMap fun p => biv p.1 p.2

/-- (1) Both `J₊` and `J₋` commute with every element of `u(3) ⊕ u(2)`, are θ-even (compact),
and are linearly independent: the SM-compatible algebra has at least a 2-dimensional center. -/
theorem center_two_u1 :
    smPart.all (fun X => isZero (comm X Jpos) && isZero (comm X Jneg)) = true ∧
      isZero (comm Jpos eNeg) = true ∧ isZero (comm Jneg eNeg) = true ∧
      LinearIndependent ℝ (fun i : Fin 2 => toMat (![Jpos, Jneg] i)) := by
  refine ⟨by decide, by decide, by decide, linIndep_of_gram _ (by decide) (by decide)⟩

/-- (2) All four joint chirality sectors have rank 32. -/
theorem four_sectors_equal (a b : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin'
        ((1 / 2 : ℂ) • (1 + (a * Complex.I) • toC ω4) *
          ((1 / 2 : ℂ) • (1 + (b * Complex.I) • toC ω10))))) = 32 := by
  have sq : ∀ c : ℂ, (c = 1 ∨ c = -1) → c * c = 1 := by
    rintro c (rfl | rfl) <;> norm_num
  exact (joint_eigenspace_finrank a b (sq a ha) (sq b hb)).2

/-- Clifford multiplication `(ψ_a)_a ↦ Σ_a γ_a ψ_a` on spinor-valued 1-forms at a point. -/
def cliffMul : (Fin 14 → (Idx → ℝ)) →ₗ[ℝ] (Idx → ℝ) where
  toFun ψ := ∑ a, (gamma (gen a)) *ᵥ ψ a
  map_add' ψ φ := by simp [mulVec_add, Finset.sum_add_distrib]
  map_smul' c ψ := by simp [mulVec_smul, Finset.smul_sum]

lemma gamma0_sq : gamma (gen 0) * gamma (gen 0) = 1 := by
  have := anticomm 0 0
  simp only [ite_true] at this
  rw [← two_smul ℝ] at this
  have hw : w 0 = 1 := by simp [w]
  rw [hw, mul_one] at this
  exact smul_right_injective M128 (two_ne_zero (α := ℝ)) this

theorem cliffMul_surjective : Function.Surjective cliffMul := by
  intro ψ
  refine ⟨Pi.single 0 (gamma (gen 0) *ᵥ ψ), ?_⟩
  show ∑ a, gamma (gen a) *ᵥ (Pi.single (M := fun _ => Idx → ℝ) 0 (gamma (gen 0) *ᵥ ψ)) a = ψ
  rw [Finset.sum_eq_single 0 (fun a _ ha => by simp [ha]) (by simp)]
  simp [mulVec_mulVec, gamma0_sq]

/-- (3) The Rarita–Schwinger kernel has dimension `13 · 128 = 1664`. -/
theorem rs_kernel_dim : Module.finrank ℝ (LinearMap.ker cliffMul) = 13 * 128 := by
  have h := LinearMap.finrank_range_add_finrank_ker cliffMul
  rw [LinearMap.range_eq_top.mpr cliffMul_surjective, finrank_top] at h
  have h1 : Module.finrank ℝ (Fin 14 → (Idx → ℝ)) = 14 * 128 := by
    rw [Module.finrank_pi_fintype]; simp
  have h2 : Module.finrank ℝ (Idx → ℝ) = 128 := by simp
  omega

/-- (3) Branching count of the RS representation under `14 = 4 + 10` with
`dim S(4) = 4`, `dim S(10) = 32` (complex Dirac dimensions), as in (11.3):
`R(U⊕V) = R(U)⊗S(V) ⊕ S(U)⊗R(V) ⊕ S(U)⊗S(V)`, with `dim R(W) = (dim W − 1)·dim S(W)`. -/
theorem rs_branching_count :
    (4 - 1) * 4 * 32 + 4 * ((10 - 1) * 32) + 4 * 32 = (14 - 1) * (4 * 32) ∧
      4 * 32 = 128 := by decide

end GU.Predictions
