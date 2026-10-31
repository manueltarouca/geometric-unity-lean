import GU.Spinor.Reductions
import GU.Spinor.Branching
import GU.Shiab.Einstein
import GU.Observerse.Chimeric
import GU.Bundle.NoOrtho31
import GU.Spinor.Anomaly
import GU.Spinor.PatiSalamGroup

/-!
# Synthetic predictions: what the compiled model forces

Each item is a *theorem about the formal model*. The "prediction" is its physical reading
under the draft's dictionary. None of them is a claim that nature behaves this way.

1. **Extra neutral gauge boson (Z′-type), contingent.** `u(3) ⊕ u(2)` has two independent
   central `u(1)`s, `J₊` and `J₋` (`center_two_u1`). Hypercharge `Y ∝ −2J₊ + 3J₋` is the unique
   traceless (`su(3,2)`) direction (`hypercharge_forced`). The extra `u(1)` is the centre of
   `U(3,2)`, so it exists only if `U(3,2)` rather than `SU(3,2)` is the structure group, a
   choice the draft explicitly leaves open (p. 29, after (4.6)).
2. **Mirror sector of equal size** (elementary): two commuting traceless involutions split
   `ℂ¹²⁸` into four rank-32 sectors (`four_sectors_equal`). The "dark/looking-glass" reading is
   the draft's (12.20), not something derived here.
3. **Spin-3/2 count** (elementary): Clifford multiplication `TY ⊗ S̸ → S̸` is onto, so its kernel
   has dimension `13·128 = 1664` (rank–nullity, `rs_kernel_dim`). `rs_branching_count` is only
   the arithmetic of (11.3) (`384 + 1152 + 128`), not a representation-theoretic proof; the
   "imposter generation" reading is the draft's.
4. **Gravity constraints.** An Einstein tensor emerges from (9.3) only with *mixed* brackets
   (`shiab_einstein`), and the fiber metric must have DeWitt `λ > 1/4` (`trace_direction_neg_iff`).
   At `λ = 1` the chimeric signature is (7,7) (`chim_signature`).
5. **Spacetime signature selection, contingent.** Every Lorentzian point of `Y` is (1,3) or (3,1)
   (`yobs_dichotomy`), and the chimeric bundle admits O(7,7)-orthonormal frames over `y` exactly when
   `y` is (1,3) (`signature_selected`). So an O(7,7)/Spin(7,7) structure on `C`, needed for the
   spinors `S̸ = S(C)` of (3.32), exists only over observations of signature (1,3) in the
   `η = diag(1,−1,−1,−1)` labelling (mostly-minus: one time, three space). Contingent on the relative
   sign `+DeWitt ⊕ +g⁻¹` (`Chimeric.lean`): the opposite sign selects (3,1) instead. Either way,
   the theory selects exactly one of the two Lorentzian signatures, never both.
6. **Particle allocation and gauge embedding.** One chirality of `N^{6,4}` carries 16 weights whose
   `12Y` multiset is one SM generation plus `ν^c` (`hypercharge_table`), with charges
   `{2/3, −1/3, −2/3, 1/3, 0, −1, 1, 0}` (`charge_table`), 12 coloured and 8 doublet states
   (`multiplet_counts`), and vanishing `U(1)_Y³` and gravitational anomalies (`anomaly_free`).
   The other chirality carries the conjugates (`hypercharge_table_conj`). The Pati–Salam group
   acts inside `Spin(7,7)` as `(Spin(6) × Spin(4))/ℤ₂`: the factors commute, intersect in `±1`,
   act only on the fibre directions `W6 ⊕ W4`, and fix the base (1,3) (`gauge_embedding`).
   So the internal symmetry does not mix with spacetime (compatible with Coleman–Mandula). Caveats: the
   reading of weights as one left-handed generation needs the Majorana reality and a chirality
   convention (`Anomaly.lean`); each subgroup is a non-split double cover of its block `SO(6)` / `SO(4)` (`BlockSpin.lean`);
   `Spin4 ≃* spinGroup Q₄` and `Spin6 ≃* spinGroup Q₆` (Mathlib's abstract `Spin(0,4)`, `Spin(6)`;
   `SpinIso.lean`, `SpinIso6.lean`), and `Spin4 ≃* Sp(1) × Sp(1)` (`SpinQuat.lean`); topology,
   `Spin4 ≃* SU(2) × SU(2)` (`SpinSU2.lean`); `Spin6 ≃* SU(4)` (`SU4Onto.lean`); topology is not formalised.
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

/-- The hypercharge direction is forced: among central combinations `a J₊ + b J₋`
(coefficients `(a,a,a,b,b)` on the five planes), `su(3,2)`-tracelessness `3a + 2b = 0`
holds exactly on the line through `(−2, 3)`, i.e. `12Y = −2Σs_colour + 3Σs_weak`. -/
theorem hypercharge_forced (a b : ℚ) : 3 * a + 2 * b = 0 ↔ ∃ t : ℚ, a = -2 * t ∧ b = 3 * t := by
  constructor
  · intro h; exact ⟨b / 3, by linarith, by ring⟩
  · rintro ⟨t, rfl, rfl⟩; ring

section Signature
open GU.Observerse Bundle Manifold
open scoped ContDiff

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- (5) **Signature selection**: orthonormal (7,7) frames of `C` exist over `y` iff `y` is a (1,3)
point, and every point is exactly one of (1,3), (3,1). -/
theorem signature_selected (y : Yobs X) :
    ((∃ p : HomTot X, p.proj = y ∧ p ∈ orthoSet (X := X)) ↔
      ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * GU.Chimeric.ηR * Pᵀ) ∧
    (Xor' (∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * GU.Chimeric.ηR * Pᵀ)
      (∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P ∧ Gpt y = P * (-GU.Chimeric.ηR) * Pᵀ)) := by
  refine ⟨ortho_iff_13 y, ?_⟩
  rcases yobs_dichotomy y with h | h
  · exact Or.inl ⟨h, fun h' => not_13_and_31 y ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => not_13_and_31 y ⟨h', h⟩⟩

end Signature

/-- (6a) **Particle allocation of one chirality.** -/
theorem particle_allocation :
    (GU.Spinor.oddWeights.map GU.Spinor.twelveY).Perm [2, 2, 2, 2, 2, 2, -8, -8, -8, 4, 4, 4, -6, -6, 12, 0] ∧
    (GU.Spinor.oddWeights.map GU.Spinor.twelveQ).Perm [8, 8, 8, -4, -4, -4, -8, -8, -8, 4, 4, 4, 0, -12, 12, 0] ∧
    (GU.Spinor.oddWeights.filter GU.Spinor.colored).length = 12 ∧
    (GU.Spinor.oddWeights.filter GU.Spinor.doublet).length = 8 ∧
    GU.Spinor.sumOver GU.Spinor.oddWeights (fun s => GU.Spinor.twelveY s ^ 3) = 0 ∧
    GU.Spinor.sumOver GU.Spinor.oddWeights GU.Spinor.twelveY = 0 :=
  ⟨GU.Spinor.hypercharge_table, GU.Spinor.charge_table, GU.Spinor.multiplet_counts.1,
    GU.Spinor.multiplet_counts.2, GU.Spinor.anomaly_free.1, GU.Spinor.anomaly_free.2.1⟩

/-- (6b) **Gauge embedding into the observerse fibre**: Pati–Salam `(Spin6 × Spin4)/ℤ₂ ⊂ Spin(7,7)`,
commuting factors, kernel exactly `±(1,1)`, base (1,3) directions fixed, fibre blocks preserved. -/
theorem gauge_embedding :
    (∀ x ∈ GU.Spinor.Spin6, ∀ y ∈ GU.Spinor.Spin4, x * y = y * x) ∧
    (∀ x ∈ GU.Spinor.Spin6, ∀ y ∈ GU.Spinor.Spin4, x * y = 1 →
      ((x : GU.Cl77) = 1 ∧ (y : GU.Cl77) = 1) ∨ ((x : GU.Cl77) = -1 ∧ (y : GU.Cl77) = -1)) ∧
    (∃ x ∈ GU.Spinor.Spin6, ∃ y ∈ GU.Spinor.Spin4, x ≠ 1 ∧ x * y = 1) ∧
    (∀ x, (x ∈ GU.Spinor.Spin6 ∨ x ∈ GU.Spinor.Spin4) → ∀ c, GU.Spinor.SuppIn GU.Spinor.SB c →
      GU.Spinor.vecRep x c = c) ∧
    (∀ x ∈ GU.Spinor.Spin6, ∀ v, GU.Spinor.SuppIn GU.Spinor.S6 v →
      GU.Spinor.SuppIn GU.Spinor.S6 (GU.Spinor.vecRep x v)) ∧
    (∀ x ∈ GU.Spinor.Spin4, ∀ v, GU.Spinor.SuppIn GU.Spinor.S4 v →
      GU.Spinor.SuppIn GU.Spinor.S4 (GU.Spinor.vecRep x v)) :=
  ⟨fun _ hx _ hy => GU.Spinor.spin6_spin4_commute hx hy,
   fun _ hx _ hy h => GU.Spinor.product_kernel hx hy h,
   GU.Spinor.product_not_injective,
   fun _ hx _ hc => GU.Spinor.base_fixed hx hc,
   fun _ hx _ hv => GU.Spinor.spin6_preserves_W6 hx hv,
   fun _ hx _ hv => GU.Spinor.spin4_preserves_W4 hx hv⟩

end GU.Predictions
