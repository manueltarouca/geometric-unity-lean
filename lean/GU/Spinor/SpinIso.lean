import GU.Spinor.SpinComponent

/-!
# `Spin4 ≅ spinGroup(Q₄)`: the Pati–Salam `Spin4` is isomorphic to Mathlib's abstract spin group of `ℝ^{0,4}`

`Q₄ = −(x₁² + ⋯ + x₄²)` on `ℝ⁴`, and `f₄ : ℝ⁴ → ℝ¹⁴` is the isometric inclusion onto
`W4 = span{e₁₀, …, e₁₃}`. Let `Φ = CliffordAlgebra.map f₄ : Cl(Q₄) → Cl(7,7)`.

1. **`Φ` is injective** (`Φ_injective`). `dim Cl(Q₄) = 16` (via `equivExterior`). The 16 monomials
   `e_S` (`S ⊆ {1..4}`) map to Pauli strings whose pairwise products have trace `0` off the
   diagonal and nonzero on it (`decide`), so their images are linearly independent.
2. **`Φ(spinGroup Q₄) ⊆ Spin4`**: `Φ` commutes with `star`, preserves evenness and the Lipschitz
   group. Even elements built from `W4` commute with every `e_j`, `j ∉ W4`. Then `spin4_iff` applies.
3. **`Spin4 ⊆ Φ(spinGroup Q₄)`**: the generators `ι a ι b` of `Spin4` are images.

**`spin4Equiv : spinGroup Q₄ ≃* Spin4`**. So the group-level Pati–Salam factor `Spin4` is
isomorphic to Mathlib's `Spin(0,4)` (`spinGroup` of a negative-definite rank-4 form). The analogous
`Spin6 ≃* spinGroup(Q₆)` is `SpinIso6.lean`. `Spin4 ≃* Sp(1) × Sp(1)` (unit quaternions) is
`spin4QuatEquiv`, `SpinQuat.lean`.
-/

namespace GU.Spinor

open CliffordAlgebra

/-- `Q₄ = −(x₁² + ⋯ + x₄²)`. -/
noncomputable def Q4 : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 4 => (-1 : ℝ))

/-- Block index `k ↦ 10 + k`. -/
def emb4 (k : Fin 4) : Fin 14 := ⟨k + 10, by omega⟩

/-- Extension by zero `ℝ⁴ → ℝ¹⁴` onto `W4`. -/
noncomputable def f4L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun v i := if h : 10 ≤ (i : ℕ) then v ⟨i - 10, by omega⟩ else 0
  map_add' v w := by funext i; by_cases h : 10 ≤ (i : ℕ) <;> simp [h]
  map_smul' c v := by funext i; by_cases h : 10 ≤ (i : ℕ) <;> simp [h]

lemma f4L_single (k : Fin 4) : f4L (Pi.single k 1) = eb (emb4 k) := by
  funext i
  simp only [f4L, LinearMap.coe_mk, AddHom.coe_mk, eb, emb4, Pi.single_apply]
  by_cases h : 10 ≤ (i : ℕ)
  · rw [dif_pos h]
    by_cases hk : (⟨i - 10, by omega⟩ : Fin 4) = k
    · subst hk; simp [Fin.ext_iff]; omega
    · rw [if_neg hk, if_neg]
      intro e; apply hk
      exact Fin.ext (by have := congrArg Fin.val e; simp only at this; simp only; omega)
  · rw [dif_neg h, if_neg]
    intro e; rw [e] at h; simp at h

lemma Q77_f4L (v : Fin 4 → ℝ) : Q77 (f4L v) = Q4 v := by
  simp only [Q77, Q4, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  rw [show (Finset.univ : Finset (Fin 14)).sum = (Finset.univ : Finset (Fin (10 + 4))).sum from rfl,
    Fin.sum_univ_add]
  have h1 : ∀ k : Fin 10, f4L v (Fin.castAdd 4 k) = 0 := fun k => by
    simp [f4L]
  have h2 : ∀ k : Fin 4, f4L v (Fin.natAdd 10 k) = v k := fun k => by
    simp only [f4L, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_natAdd]
    rw [dif_pos (by omega)]; congr 1; ext; simp
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, Fin.val_natAdd]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_neg (by omega)]

/-- The isometry `(ℝ⁴, Q₄) → (ℝ¹⁴, Q77)`. -/
noncomputable def f4 : Q4 →qᵢ Q77 := ⟨f4L, Q77_f4L⟩

/-- `Φ : Cl(Q₄) → Cl(7,7)`. -/
noncomputable def Φ4 : CliffordAlgebra Q4 →ₐ[ℝ] Cl77 := CliffordAlgebra.map f4

lemma Φ4_ι (v : Fin 4 → ℝ) : Φ4 (ι Q4 v) = ι Q77 (f4L v) := CliffordAlgebra.map_apply_ι _ v

/-! ### Dimension and monomials -/

noncomputable def ϑ4 : CliffordAlgebra Q4 ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin 4 → ℝ) :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  CliffordAlgebra.equivExterior Q4

instance : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
  Module.Finite.of_basis ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra)

instance : FiniteDimensional ℝ (CliffordAlgebra Q4) := LinearEquiv.finiteDimensional ϑ4.symm

theorem finrank_Cl4 : Module.finrank ℝ (CliffordAlgebra Q4) = 16 := by
  rw [ϑ4.finrank_eq, Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra),
    Fintype.card_finset, Fintype.card_fin]; rfl

/-- Indices selected by a bitmask. -/
def idx4 (b : Fin 4 → Bool) : List (Fin 4) := (List.finRange 4).filter fun k => b k

/-- The monomial `e_S`. -/
noncomputable def mon4 (b : Fin 4 → Bool) : CliffordAlgebra Q4 :=
  ((idx4 b).map fun k => ι Q4 (Pi.single k 1)).prod

/-- Its Pauli string. -/
def L4 (b : Fin 4 → Bool) : List Gen := (idx4 b).map fun k => gen (emb4 k)

lemma rep_mon4 (b : Fin 4 → Bool) : cliffordRep (Φ4 (mon4 b)) = (gprod (L4 b)).toMat := by
  have hg : ∀ i, gammaMap (eb i) = gamma (gen i) := fun i => by
    simp [gammaMap, eb, Pi.single_apply]
  rw [toMat_gprod, mon4, map_list_prod, map_list_prod, List.map_map, List.map_map, L4, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, Φ4_ι, f4L_single, cliffordRep_ι, hg]

theorem tr_off : ∀ b c : Fin 4 → Bool, b ≠ c → (gprod (L4 b) * gprod (L4 c)).tr = 0 := by
  decide

theorem tr_diag : ∀ b : Fin 4 → Bool, (gprod (L4 b) * gprod (L4 b)).tr ≠ 0 := by
  decide

lemma linInd_rep : LinearIndependent ℝ fun b : Fin 4 → Bool => cliffordRep (Φ4 (mon4 b)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h := congrArg (fun M => Matrix.trace (M * cliffordRep (Φ4 (mon4 c)))) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, zero_mul,
    Matrix.trace_zero, rep_mon4, ← PString.toMat_mul, PString.trace_toMat, smul_eq_mul] at h
  rw [Finset.sum_eq_single c] at h
  · have hd := tr_diag c
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hd
  · intro b _ hbc; rw [tr_off b c hbc]; simp
  · simp

lemma linInd_mon : LinearIndependent ℝ (mon4 : (Fin 4 → Bool) → CliffordAlgebra Q4) :=
  LinearIndependent.of_comp Φ4.toLinearMap (LinearIndependent.of_comp cliffordRep.toLinearMap linInd_rep)

/-! ### Injectivity -/

/-- **`Φ : Cl(Q₄) → Cl(7,7)` is injective.** -/
theorem Φ4_injective : Function.Injective Φ4 := by
  have hcard : Fintype.card (Fin 4 → Bool) = Module.finrank ℝ (CliffordAlgebra Q4) := by
    rw [finrank_Cl4]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank linInd_mon hcard
  have hB : ⇑B = mon4 := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hli : LinearIndependent ℝ fun b => Φ4 (mon4 b) :=
    LinearIndependent.of_comp cliffordRep.toLinearMap linInd_rep
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum := B.sum_repr x
  rw [hB] at hsum
  rw [← hsum, map_sum] at hx
  simp only [map_smul] at hx
  have h0 := (Fintype.linearIndependent_iff.mp hli) _ hx
  rw [← hsum]; simp [h0]

/-! ### `Φ` on the spin group -/

lemma star_algebraMap_Cl {N : Type*} [AddCommGroup N] [Module ℝ N] (Q : QuadraticForm ℝ N) (r : ℝ) :
    star (algebraMap ℝ (CliffordAlgebra Q) r) = algebraMap ℝ (CliffordAlgebra Q) r := by
  rw [CliffordAlgebra.star_def, involute.commutes, reverse.commutes]

lemma Φ4_star (x : CliffordAlgebra Q4) : Φ4 (star x) = star (Φ4 x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [star_algebraMap_Cl, AlgHom.commutes, star_algebraMap_Cl]
  | ι v => rw [CliffordAlgebra.star_ι, map_neg, Φ4_ι, CliffordAlgebra.star_ι]
  | mul a b ha hb => rw [star_mul, map_mul, map_mul, ha, hb, star_mul]
  | add a b ha hb => rw [star_add, map_add, map_add, ha, hb, star_add]

lemma Φ4_even {x : CliffordAlgebra Q4} (hx : x ∈ evenOdd Q4 0) : Φ4 x ∈ evenOdd Q77 0 := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Φ4_ι, Φ4_ι]
    exact Submodule.mul_le.mp (evenOdd_mul_le Q77 0 0) _
      (ι_mul_ι_mem_evenOdd_zero Q77 _ _) _ hx

lemma f4L_low (v : Fin 4 → ℝ) {j : Fin 14} (hj : (j : ℕ) < 10) : f4L v j = 0 := by
  simp only [f4L, LinearMap.coe_mk, AddHom.coe_mk]; rw [dif_neg (show ¬ 10 ≤ (j : ℕ) by omega)]

lemma Φ4_comm {x : CliffordAlgebra Q4} (hx : x ∈ evenOdd Q4 0) {j : Fin 14} (hj : (j : ℕ) < 10) :
    Φ4 x * ι Q77 (eb j) = ι Q77 (eb j) * Φ4 x := by
  have hp : ∀ v, QuadraticMap.polar Q77 (f4L v) (eb j) = 0 := fun v => by
    rw [polar_eb_right, f4L_low v hj]; ring
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r (ι Q77 (eb j))
  | add x y _ _ hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Φ4_ι, Φ4_ι, mul_assoc, hx, ← mul_assoc, pair_comm (hp m₁) (hp m₂),
      mul_assoc]

lemma Φ4_lipschitz {u : (CliffordAlgebra Q4)ˣ} (hu : u ∈ lipschitzGroup Q4) :
    Units.map Φ4.toMonoidHom u ∈ lipschitzGroup Q77 := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨v, hv⟩ := hu
    exact Subgroup.subset_closure ⟨f4L v, by
      show ι Q77 (f4L v) = Φ4 u
      rw [← hv, Φ4_ι]⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul u w _ _ hu hw => rw [map_mul]; exact Subgroup.mul_mem _ hu hw
  | inv u _ hu => rw [map_inv]; exact Subgroup.inv_mem _ hu

lemma Φ4_spin {x : CliffordAlgebra Q4} (hx : x ∈ spinGroup Q4) : Φ4 x ∈ spinGroup Q77 := by
  obtain ⟨hpin, heven⟩ := spinGroup.mem_iff.mp hx
  obtain ⟨⟨u, hu, hux⟩, hunit⟩ := pinGroup.mem_iff.mp hpin
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨⟨Units.map Φ4.toMonoidHom u,
    Φ4_lipschitz hu, by rw [← hux]; rfl⟩, ?_⟩, Φ4_even heven⟩
  rw [Unitary.mem_iff] at hunit ⊢
  constructor
  · rw [← Φ4_star, ← map_mul, hunit.1, map_one]
  · rw [← Φ4_star, ← map_mul, hunit.2, map_one]

/-- `Φ` as a group homomorphism `spinGroup Q₄ → Spin(7,7)`. -/
noncomputable def spin4Hom : spinGroup Q4 →* Spin77 where
  toFun x := ⟨Φ4 (x : CliffordAlgebra Q4), Φ4_spin x.2⟩
  map_one' := Subtype.ext (map_one Φ4)
  map_mul' x y := Subtype.ext (map_mul Φ4 (x : CliffordAlgebra Q4) (y : CliffordAlgebra Q4))

lemma spin4Hom_mem (x : spinGroup Q4) : spin4Hom x ∈ Spin4 := by
  rw [spin4_iff]
  refine ⟨vecRep_isometry _, det_vecRep _, fun j hj => ?_⟩
  have hj' : (j : ℕ) < 10 := (by decide : ∀ j : Fin 14, j ∉ S4 → (j : ℕ) < 10) j hj
  apply ι_injective
  show ι Q77 (vecL _ _) = _
  rw [ι_vecL]
  show Φ4 (x : CliffordAlgebra Q4) * ι Q77 (eb j) * star (Φ4 (x : CliffordAlgebra Q4)) = _
  have heven := (spinGroup.mem_iff.mp x.2).2
  rw [Φ4_comm heven hj', mul_assoc, ← Φ4_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
    map_one, mul_one]

/-- Generic: `ι a ι b ∈ spinGroup Q` when `Q a · Q b = 1`. -/
lemma pair_mem_gen {N : Type*} [AddCommGroup N] [Module ℝ N] (Q : QuadraticForm ℝ N) (a b : N)
    (h : Q a * Q b = 1) : ι Q a * ι Q b ∈ spinGroup Q := by
  have ha : Q a ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hb : Q b ≠ 0 := right_ne_zero_of_mul_eq_one h
  have unit : ∀ c : N, Q c ≠ 0 → ∃ u : (CliffordAlgebra Q)ˣ, (u : CliffordAlgebra Q) = ι Q c ∧
      u ∈ lipschitzGroup Q := fun c hc =>
    ⟨⟨ι Q c, (Q c)⁻¹ • ι Q c,
      by rw [mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
        inv_mul_cancel₀ hc, one_smul],
      by rw [smul_mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
        inv_mul_cancel₀ hc, one_smul]⟩, rfl, Subgroup.subset_closure ⟨c, rfl⟩⟩
  obtain ⟨u, hu, hul⟩ := unit a ha
  obtain ⟨w, hw, hwl⟩ := unit b hb
  have hstar : star (ι Q a * ι Q b) = ι Q b * ι Q a := by
    rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι, neg_mul_neg]
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨⟨u * w, (lipschitzGroup Q).mul_mem hul hwl, ?_⟩,
    ?_⟩, ?_⟩
  · simp [hu, hw]
  · rw [Unitary.mem_iff, hstar]
    constructor
    · rw [show ι Q b * ι Q a * (ι Q a * ι Q b) = ι Q b * (ι Q a * ι Q a) * ι Q b by
        simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar, ← map_mul,
        h, map_one]
    · rw [show ι Q a * ι Q b * (ι Q b * ι Q a) = ι Q a * (ι Q b * ι Q b) * ι Q a by
        simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar, ← map_mul,
        mul_comm (Q b), h, map_one]
  · exact ι_mul_ι_mem_evenOdd_zero Q a b

/-- Restriction of a `W4`-supported vector to `ℝ⁴`. -/
def res4 (a : Fin 14 → ℝ) : Fin 4 → ℝ := fun k => a (emb4 k)

lemma f4L_res4 {a : Fin 14 → ℝ} (ha : SuppIn S4 a) : f4L (res4 a) = a := by
  funext i
  simp only [f4L, LinearMap.coe_mk, AddHom.coe_mk, res4]
  by_cases h : 10 ≤ (i : ℕ)
  · rw [dif_pos h]; congr 1; ext; simp [emb4]; omega
  · rw [dif_neg h, ha i ((by decide : ∀ i : Fin 14, ¬ 10 ≤ (i : ℕ) → i ∉ S4) i h)]

lemma spin4_le_range : Spin4 ≤ spin4Hom.range := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨a, b, ha, hb, hqa, hqb, hx⟩ := hx
  have hQ : ∀ c, SuppIn S4 c → Q4 (res4 c) = Q77 c := fun c hc => by rw [← Q77_f4L, f4L_res4 hc]
  refine ⟨⟨ι Q4 (res4 a) * ι Q4 (res4 b), pair_mem_gen Q4 _ _ (by rw [hQ a ha, hQ b hb, hqa, hqb]; norm_num)⟩,
    Subtype.ext ?_⟩
  show Φ4 (ι Q4 (res4 a) * ι Q4 (res4 b)) = x
  rw [map_mul, Φ4_ι, Φ4_ι, f4L_res4 ha, f4L_res4 hb, hx]

/-- **`spinGroup Q₄ ≃* Spin4`**: the Pati–Salam `Spin4 ⊂ Spin(7,7)` is isomorphic to Mathlib's
abstract spin group of the negative-definite form on `ℝ⁴`. -/
noncomputable def spin4Equiv : spinGroup Q4 ≃* Spin4 :=
  MulEquiv.ofBijective (spin4Hom.codRestrict Spin4 spin4Hom_mem)
    ⟨fun x y h => Subtype.ext (Φ4_injective (congrArg (fun z : Spin4 => ((z : Spin77) : Cl77)) h)),
     fun y => by
      obtain ⟨x, hx⟩ := spin4_le_range y.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem spin4Equiv_apply (x : spinGroup Q4) :
    ((spin4Equiv x : Spin77) : Cl77) = Φ4 (x : CliffordAlgebra Q4) := rfl

end GU.Spinor
