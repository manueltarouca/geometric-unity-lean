import GU.Spinor.SpinIso

/-!
# `Spin6 ≅ spinGroup(Q₆)`: the Pati–Salam `Spin6` is isomorphic to Mathlib's abstract `Spin(6)`

Same method as `SpinIso.lean`, applied to the positive-definite block `W6 = span{e₁,…,e₆}` with
`Q₆ = x₁² + ⋯ + x₆²`.
* `Φ₆ = CliffordAlgebra.map f₆ : Cl(Q₆) → Cl(7,7)` is injective. `dim Cl(Q₆) = 64`, and the 64
  monomials map to Pauli strings that are trace-orthogonal (`decide` over `64 × 64` pairs).
* `Φ₆(spinGroup Q₆) = Spin6`.

**`spin6Equiv : spinGroup Q₆ ≃* Spin6`**. Not proved: `Spin(6) ≅ SU(4)`.
-/

namespace GU.Spinor

open CliffordAlgebra

/-- `Q₆ = x₁² + ⋯ + x₆²`. -/
noncomputable def Q6 : QuadraticForm ℝ (Fin 6 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 6 => (1 : ℝ))

/-- Block index `k ↦ 1 + k`. -/
def emb6 (k : Fin 6) : Fin 14 := ⟨k + 1, by omega⟩

/-- In-block test for `W6 = span{e₁,…,e₆}`. -/
def inW6 (i : Fin 14) : Prop := 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 6

instance (i : Fin 14) : Decidable (inW6 i) := by unfold inW6; infer_instance

/-- Extension by zero `ℝ⁶ → ℝ¹⁴` onto `W6`. -/
noncomputable def f6L : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 14 → ℝ) where
  toFun v i := if h : inW6 i then v ⟨i - 1, by unfold inW6 at h; omega⟩ else 0
  map_add' v w := by funext i; by_cases h : inW6 i <;> simp [h]
  map_smul' c v := by funext i; by_cases h : inW6 i <;> simp [h]

lemma f6L_off (v : Fin 6 → ℝ) {j : Fin 14} (hj : ¬ inW6 j) : f6L v j = 0 := by
  simp only [f6L, LinearMap.coe_mk, AddHom.coe_mk]; rw [dif_neg hj]

lemma f6L_emb (v : Fin 6 → ℝ) (k : Fin 6) : f6L v (emb6 k) = v k := by
  have h : inW6 (emb6 k) := by unfold inW6 emb6; simp
  simp only [f6L, LinearMap.coe_mk, AddHom.coe_mk]; rw [dif_pos h]
  congr 1

lemma f6L_single (k : Fin 6) : f6L (Pi.single k 1) = eb (emb6 k) := by
  funext i
  by_cases h : inW6 i
  · have hi : i = emb6 ⟨i - 1, by unfold inW6 at h; omega⟩ := by
      ext; simp [emb6]; unfold inW6 at h; omega
    rw [hi, f6L_emb]
    simp only [eb, Pi.single_apply]
    by_cases hk : (⟨i - 1, by unfold inW6 at h; omega⟩ : Fin 6) = k
    · rw [if_pos hk, if_pos (by rw [hk])]
    · rw [if_neg hk, if_neg]
      intro e; apply hk; ext; have := congrArg Fin.val e; simp [emb6] at this; omega
  · rw [f6L_off _ h]
    simp only [eb, Pi.single_apply]
    rw [if_neg]; intro e; apply h; rw [e]; unfold inW6 emb6; simp

lemma Q77_f6L (v : Fin 6 → ℝ) : Q77 (f6L v) = Q6 v := by
  have hs : SuppIn S6 (f6L v) := fun i hi => f6L_off v (by
    revert hi; revert i; unfold inW6; decide)
  rw [Q_block uniform_S6 hs, one_mul]
  simp only [Q6, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, one_mul]
  rw [show (Finset.univ : Finset (Fin 14)).sum = (Finset.univ : Finset (Fin (7 + 7))).sum from rfl,
    Fin.sum_univ_add, show (Finset.univ : Finset (Fin 7)).sum = (Finset.univ : Finset (Fin (1 + 6))).sum
      from rfl, Fin.sum_univ_add]
  have h0 : ∀ k : Fin 1, f6L v (Fin.castAdd 7 (Fin.castAdd 6 k)) = 0 := fun k => f6L_off v (by
    unfold inW6; simp)
  have h7 : ∀ k : Fin 7, f6L v (Fin.natAdd 7 k) = 0 := fun k => f6L_off v (by
    unfold inW6; simp)
  have h1 : ∀ k : Fin 6, f6L v (Fin.castAdd 7 (Fin.natAdd 1 k)) = v k := fun k => by
    rw [show (Fin.castAdd 7 (Fin.natAdd 1 k) : Fin 14) = emb6 k by ext; simp [emb6]; omega, f6L_emb]
  simp only [h0, h7, h1]; simp [sq]

/-- The isometry `(ℝ⁶, Q₆) → (ℝ¹⁴, Q77)`. -/
noncomputable def f6 : Q6 →qᵢ Q77 := ⟨f6L, Q77_f6L⟩

/-- `Φ : Cl(Q₆) → Cl(7,7)`. -/
noncomputable def Φ6 : CliffordAlgebra Q6 →ₐ[ℝ] Cl77 := CliffordAlgebra.map f6

lemma Φ6_ι (v : Fin 6 → ℝ) : Φ6 (ι Q6 v) = ι Q77 (f6L v) := CliffordAlgebra.map_apply_ι _ v

/-! ### Dimension and monomials -/

noncomputable def ϑ6 : CliffordAlgebra Q6 ≃ₗ[ℝ] ExteriorAlgebra ℝ (Fin 6 → ℝ) :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  CliffordAlgebra.equivExterior Q6

instance : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) :=
  Module.Finite.of_basis ((Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra)

instance : FiniteDimensional ℝ (CliffordAlgebra Q6) := LinearEquiv.finiteDimensional ϑ6.symm

theorem finrank_Cl6 : Module.finrank ℝ (CliffordAlgebra Q6) = 64 := by
  rw [ϑ6.finrank_eq, Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra),
    Fintype.card_finset, Fintype.card_fin]; rfl

/-- Indices selected by a bitmask. -/
def idx6 (b : Fin 6 → Bool) : List (Fin 6) := (List.finRange 6).filter fun k => b k

/-- The monomial `e_S`. -/
noncomputable def mon6 (b : Fin 6 → Bool) : CliffordAlgebra Q6 :=
  ((idx6 b).map fun k => ι Q6 (Pi.single k 1)).prod

/-- Its Pauli string. -/
def L6 (b : Fin 6 → Bool) : List Gen := (idx6 b).map fun k => gen (emb6 k)

lemma rep_mon6 (b : Fin 6 → Bool) : cliffordRep (Φ6 (mon6 b)) = (gprod (L6 b)).toMat := by
  have hg : ∀ i, gammaMap (eb i) = gamma (gen i) := fun i => by
    simp [gammaMap, eb, Pi.single_apply]
  rw [toMat_gprod, mon6, map_list_prod, map_list_prod, List.map_map, List.map_map, L6, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, Φ6_ι, f6L_single, cliffordRep_ι, hg]

set_option maxRecDepth 100000 in
theorem tr_off6 : ∀ b c : Fin 6 → Bool, b ≠ c → (gprod (L6 b) * gprod (L6 c)).tr = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tr_diag6 : ∀ b : Fin 6 → Bool, (gprod (L6 b) * gprod (L6 b)).tr ≠ 0 := by
  decide +kernel

lemma linInd_rep6 : LinearIndependent ℝ fun b : Fin 6 → Bool => cliffordRep (Φ6 (mon6 b)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h := congrArg (fun M => Matrix.trace (M * cliffordRep (Φ6 (mon6 c)))) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, zero_mul,
    Matrix.trace_zero, rep_mon6, ← PString.toMat_mul, PString.trace_toMat, smul_eq_mul] at h
  rw [Finset.sum_eq_single c] at h
  · have hd := tr_diag6 c
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hd
  · intro b _ hbc; rw [tr_off6 b c hbc]; simp
  · simp

lemma linInd_mon6 : LinearIndependent ℝ (mon6 : (Fin 6 → Bool) → CliffordAlgebra Q6) :=
  LinearIndependent.of_comp Φ6.toLinearMap (LinearIndependent.of_comp cliffordRep.toLinearMap linInd_rep6)

/-! ### Injectivity -/

/-- **`Φ : Cl(Q₆) → Cl(7,7)` is injective.** -/
theorem Φ6_injective : Function.Injective Φ6 := by
  have hcard : Fintype.card (Fin 6 → Bool) = Module.finrank ℝ (CliffordAlgebra Q6) := by
    rw [finrank_Cl6]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank linInd_mon6 hcard
  have hB : ⇑B = mon6 := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hli : LinearIndependent ℝ fun b => Φ6 (mon6 b) :=
    LinearIndependent.of_comp cliffordRep.toLinearMap linInd_rep6
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum := B.sum_repr x
  rw [hB] at hsum
  rw [← hsum, map_sum] at hx
  simp only [map_smul] at hx
  have h0 := (Fintype.linearIndependent_iff.mp hli) _ hx
  rw [← hsum]; simp [h0]

/-! ### `Φ` on the spin group -/

lemma Φ6_star (x : CliffordAlgebra Q6) : Φ6 (star x) = star (Φ6 x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [star_algebraMap_Cl, AlgHom.commutes, star_algebraMap_Cl]
  | ι v => rw [CliffordAlgebra.star_ι, map_neg, Φ6_ι, CliffordAlgebra.star_ι]
  | mul a b ha hb => rw [star_mul, map_mul, map_mul, ha, hb, star_mul]
  | add a b ha hb => rw [star_add, map_add, map_add, ha, hb, star_add]

lemma Φ6_even {x : CliffordAlgebra Q6} (hx : x ∈ evenOdd Q6 0) : Φ6 x ∈ evenOdd Q77 0 := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Φ6_ι, Φ6_ι]
    exact Submodule.mul_le.mp (evenOdd_mul_le Q77 0 0) _
      (ι_mul_ι_mem_evenOdd_zero Q77 _ _) _ hx

lemma Φ6_comm {x : CliffordAlgebra Q6} (hx : x ∈ evenOdd Q6 0) {j : Fin 14} (hj : ¬ inW6 j) :
    Φ6 x * ι Q77 (eb j) = ι Q77 (eb j) * Φ6 x := by
  have hp : ∀ v, QuadraticMap.polar Q77 (f6L v) (eb j) = 0 := fun v => by
    rw [polar_eb_right, f6L_off v hj]; ring
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r (ι Q77 (eb j))
  | add x y _ _ hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, Φ6_ι, Φ6_ι, mul_assoc, hx, ← mul_assoc, pair_comm (hp m₁) (hp m₂),
      mul_assoc]

lemma Φ6_lipschitz {u : (CliffordAlgebra Q6)ˣ} (hu : u ∈ lipschitzGroup Q6) :
    Units.map Φ6.toMonoidHom u ∈ lipschitzGroup Q77 := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨v, hv⟩ := hu
    exact Subgroup.subset_closure ⟨f6L v, by
      show ι Q77 (f6L v) = Φ6 u
      rw [← hv, Φ6_ι]⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul u w _ _ hu hw => rw [map_mul]; exact Subgroup.mul_mem _ hu hw
  | inv u _ hu => rw [map_inv]; exact Subgroup.inv_mem _ hu

lemma Φ6_spin {x : CliffordAlgebra Q6} (hx : x ∈ spinGroup Q6) : Φ6 x ∈ spinGroup Q77 := by
  obtain ⟨hpin, heven⟩ := spinGroup.mem_iff.mp hx
  obtain ⟨⟨u, hu, hux⟩, hunit⟩ := pinGroup.mem_iff.mp hpin
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨⟨Units.map Φ6.toMonoidHom u,
    Φ6_lipschitz hu, by rw [← hux]; rfl⟩, ?_⟩, Φ6_even heven⟩
  rw [Unitary.mem_iff] at hunit ⊢
  constructor
  · rw [← Φ6_star, ← map_mul, hunit.1, map_one]
  · rw [← Φ6_star, ← map_mul, hunit.2, map_one]

/-- `Φ` as a group homomorphism `spinGroup Q₆ → Spin(7,7)`. -/
noncomputable def spin6Hom : spinGroup Q6 →* Spin77 where
  toFun x := ⟨Φ6 (x : CliffordAlgebra Q6), Φ6_spin x.2⟩
  map_one' := Subtype.ext (map_one Φ6)
  map_mul' x y := Subtype.ext (map_mul Φ6 (x : CliffordAlgebra Q6) (y : CliffordAlgebra Q6))

lemma spin6Hom_mem (x : spinGroup Q6) : spin6Hom x ∈ Spin6 := by
  rw [spin6_iff]
  refine ⟨vecRep_isometry _, det_vecRep _, fun j hj => ?_⟩
  have hj' : ¬ inW6 j := by revert hj; revert j; unfold inW6; decide
  apply ι_injective
  show ι Q77 (vecL _ _) = _
  rw [ι_vecL]
  show Φ6 (x : CliffordAlgebra Q6) * ι Q77 (eb j) * star (Φ6 (x : CliffordAlgebra Q6)) = _
  have heven := (spinGroup.mem_iff.mp x.2).2
  rw [Φ6_comm heven hj', mul_assoc, ← Φ6_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
    map_one, mul_one]

/-- Restriction of a `W6`-supported vector to `ℝ⁶`. -/
def res6 (a : Fin 14 → ℝ) : Fin 6 → ℝ := fun k => a (emb6 k)

lemma f6L_res6 {a : Fin 14 → ℝ} (ha : SuppIn S6 a) : f6L (res6 a) = a := by
  funext i
  by_cases h : inW6 i
  · have hi : i = emb6 ⟨i - 1, by unfold inW6 at h; omega⟩ := by
      ext; simp [emb6]; unfold inW6 at h; omega
    rw [hi, f6L_emb]; rfl
  · rw [f6L_off _ h, ha i (by revert h; revert i; unfold inW6; decide)]

lemma spin6_le_range : Spin6 ≤ spin6Hom.range := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨a, b, ha, hb, hqa, hqb, hx⟩ := hx
  have hQ : ∀ c, SuppIn S6 c → Q6 (res6 c) = Q77 c := fun c hc => by rw [← Q77_f6L, f6L_res6 hc]
  refine ⟨⟨ι Q6 (res6 a) * ι Q6 (res6 b), pair_mem_gen Q6 _ _ (by rw [hQ a ha, hQ b hb, hqa, hqb]; norm_num)⟩,
    Subtype.ext ?_⟩
  show Φ6 (ι Q6 (res6 a) * ι Q6 (res6 b)) = x
  rw [map_mul, Φ6_ι, Φ6_ι, f6L_res6 ha, f6L_res6 hb, hx]

/-- **`spinGroup Q₆ ≃* Spin6`**: the Pati–Salam `Spin6 ⊂ Spin(7,7)` is isomorphic to Mathlib's
abstract spin group of the positive-definite form on `ℝ⁶`. -/
noncomputable def spin6Equiv : spinGroup Q6 ≃* Spin6 :=
  MulEquiv.ofBijective (spin6Hom.codRestrict Spin6 spin6Hom_mem)
    ⟨fun x y h => Subtype.ext (Φ6_injective (congrArg (fun z : Spin6 => ((z : Spin77) : Cl77)) h)),
     fun y => by
      obtain ⟨x, hx⟩ := spin6_le_range y.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem spin6Equiv_apply (x : spinGroup Q6) :
    ((spin6Equiv x : Spin77) : Cl77) = Φ6 (x : CliffordAlgebra Q6) := rfl

end GU.Spinor
