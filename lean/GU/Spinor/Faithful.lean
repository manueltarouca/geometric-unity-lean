import GU.Spinor.Basis
import GU.Bundle.MainBundle

/-!
# `Cl(7,7) ≅ ℝ(128)` and faithfulness of `ρ_D` (the `↪` of (3.28))

1. The image of `cliffordRep` contains every single-slot operator `slot n Y`:
   * `γ_(n,+) γ_(n,-) = slot n (σ₁ε) = -slot n σ₃`;
   * the Jordan–Wigner string `σ₃^{⊗n}` is a product of those;
   * `string n · γ_(n,t) = slot n X_t`.
   Slot operators in different slots multiply to Kronecker products, so the image contains every
   `tprod A`, hence every matrix unit: `cliffordRep` is surjective.
2. `dim Cl(7,7) = 2¹⁴ = dim ℝ(128)`, via `ϑ : Cl ≃ Λ*` and Mathlib's exterior-algebra basis.
   So `cliffordRep` is bijective (`cliffordRep_bijective`), which proves (3.18).
3. Hence `ρ_D` is injective (`rhoD_injective`), and `diracRep.Faithful` holds.
-/

namespace GU.Spinor

open Matrix

/-- `Y` in slot `n`, identity elsewhere. -/
def slot (n : Fin 7) (Y : Matrix (Fin 2) (Fin 2) ℝ) : M128 :=
  tprod (fun i => if i = n then Y else 1)

lemma tprod_update_apply (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) (n : Fin 7) (W) (a b : Idx) :
    tprod (Function.update A n W) a b = W (a n) (b n) * ∏ x ∈ Finset.univ.erase n, A x (a x) (b x) := by
  simp only [tprod, of_apply]
  rw [← Finset.mul_prod_erase Finset.univ (fun x => Function.update A n W x (a x) (b x))
    (Finset.mem_univ n)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]

lemma tprod_update_add (n : Fin 7) (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) (Y Z) :
    tprod (Function.update A n (Y + Z)) =
      tprod (Function.update A n Y) + tprod (Function.update A n Z) := by
  ext a b
  rw [Matrix.add_apply, tprod_update_apply, tprod_update_apply, tprod_update_apply,
    Matrix.add_apply]
  ring

lemma tprod_update_smul (n : Fin 7) (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (Y) :
    tprod (Function.update A n (c • Y)) = c • tprod (Function.update A n Y) := by
  ext a b
  rw [Matrix.smul_apply, tprod_update_apply, tprod_update_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul]
  ring

lemma slot_eq_update (n : Fin 7) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    slot n Y = tprod (Function.update (fun _ => 1) n Y) := by
  rw [slot]; congr 1; funext i
  by_cases h : i = n
  · subst h; simp
  · simp [h]

lemma slot_add (n : Fin 7) (Y Z) : slot n (Y + Z) = slot n Y + slot n Z := by
  simp only [slot_eq_update, tprod_update_add]

lemma slot_smul (n : Fin 7) (c : ℝ) (Y) : slot n (c • Y) = c • slot n Y := by
  simp only [slot_eq_update, tprod_update_smul]

lemma F2.s3_mul_s3 : F2.toM .s3 * F2.toM .s3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [F2.toM, mul_apply]

/-- The range of the Clifford representation, as a subalgebra. -/
abbrev R : Subalgebra ℝ M128 := cliffordRep.range

lemma gen_surjective : Function.Surjective gen := by decide

lemma gamma_mem (g : Gen) : gamma g ∈ R := by
  obtain ⟨i, rfl⟩ := gen_surjective g
  refine ⟨CliffordAlgebra.ι Q77 (Pi.single i 1), ?_⟩
  show cliffordRep (CliffordAlgebra.ι Q77 (Pi.single i 1)) = gamma (gen i)
  rw [cliffordRep_ι, gammaMap, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma slot_mem_s3 (n : Fin 7) : slot n (F2.toM .s3) ∈ R := by
  have h : gamma (n, false) * gamma (n, true) = slot n (F2.toM .s1 * F2.toM .ep) := by
    rw [gamma, gamma, tprod_mul, slot]; congr 1; funext i
    simp only [sym]
    by_cases h1 : i < n
    · simp [h1, ne_of_lt h1, F2.s3_mul_s3]
    · by_cases h2 : i = n
      · subst h2; simp
      · simp [h1, h2]
  have h2 : F2.toM .s1 * F2.toM .ep = (-1 : ℝ) • F2.toM .s3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [F2.toM, mul_apply]
  rw [h2, slot_smul] at h
  have := R.neg_mem (R.mul_mem (gamma_mem (n, false)) (gamma_mem (n, true)))
  rwa [h, neg_one_smul, neg_neg] at this

/-- Jordan–Wigner string `σ₃` in slots `< n`. -/
def string (n : ℕ) : M128 := tprod (fun i => if (i : ℕ) < n then F2.toM .s3 else 1)

/-- Partial Kronecker product: `A i` in slots `< n`, identity elsewhere. -/
def partialT (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) : M128 :=
  tprod (fun i => if (i : ℕ) < n then A i else 1)

lemma partialT_succ (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (hn : n < 7) :
    partialT A (n + 1) = partialT A n * slot ⟨n, hn⟩ (A ⟨n, hn⟩) := by
  rw [partialT, partialT, slot, tprod_mul]; congr 1; funext i
  by_cases h1 : (i : ℕ) < n
  · have : i ≠ ⟨n, hn⟩ := fun h => by subst h; simp at h1
    simp [h1, Nat.lt_succ_of_lt h1, this]
  · by_cases h2 : (i : ℕ) = n
    · have : i = ⟨n, hn⟩ := Fin.ext h2
      subst this; simp
    · have h3 : ¬ (i : ℕ) < n + 1 := by omega
      have : i ≠ ⟨n, hn⟩ := fun h => h2 (by simp [h])
      simp [h1, h3, this]

lemma string_mem (n : ℕ) (hn : n ≤ 7) : string n ∈ R := by
  induction n with
  | zero =>
    have : string 0 = 1 := by rw [string, ← tprod_one]; simp
    rw [this]; exact R.one_mem
  | succ n ih =>
    have h := partialT_succ (fun _ => F2.toM .s3) n (by omega)
    simp only [partialT] at h
    rw [string, h]
    exact R.mul_mem (ih (by omega)) (slot_mem_s3 _)

lemma slot_mem_gen (n : Fin 7) (t : Bool) :
    slot n (F2.toM (if t then .ep else .s1)) ∈ R := by
  have h : string n * gamma (n, t) = slot n (F2.toM (if t then .ep else .s1)) := by
    rw [string, gamma, tprod_mul, slot]; congr 1; funext i
    simp only [sym]
    by_cases h1 : i < n
    · simp [h1, ne_of_lt h1, Fin.lt_def.mp h1, F2.s3_mul_s3]
    · by_cases h2 : i = n
      · subst h2; simp
      · have : ¬ (i : ℕ) < n := fun h => h1 (Fin.lt_def.mpr h)
        simp [h1, h2, this]
  rw [← h]; exact R.mul_mem (string_mem n n.2.le) (gamma_mem _)

lemma slot_one (n : Fin 7) : slot n 1 = 1 := by
  rw [slot, ← tprod_one]; congr 1; funext i; split_ifs <;> rfl

lemma decomp2 (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Y = ((Y 0 0 + Y 1 1) / 2) • F2.toM .one + ((Y 0 0 - Y 1 1) / 2) • F2.toM .s3 +
      ((Y 0 1 + Y 1 0) / 2) • F2.toM .s1 + ((Y 0 1 - Y 1 0) / 2) • F2.toM .ep := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [F2.toM] <;> ring

lemma slot_mem (n : Fin 7) (Y : Matrix (Fin 2) (Fin 2) ℝ) : slot n Y ∈ R := by
  have h1 : slot n (F2.toM .one) ∈ R := by
    rw [F2.toM_one, slot_one]
    exact R.one_mem
  have h3 := slot_mem_s3 n
  have hs1 := slot_mem_gen n false
  have hep := slot_mem_gen n true
  simp only [Bool.false_eq_true, ite_false, ite_true] at hs1 hep
  rw [decomp2 Y, slot_add, slot_add, slot_add, slot_smul, slot_smul, slot_smul, slot_smul]
  exact R.add_mem (R.add_mem (R.add_mem (R.smul_mem h1 _) (R.smul_mem h3 _))
    (R.smul_mem hs1 _)) (R.smul_mem hep _)

lemma tprod_mem (A : Fin 7 → Matrix (Fin 2) (Fin 2) ℝ) : tprod A ∈ R := by
  have : ∀ n ≤ 7, partialT A n ∈ R := by
    intro n hn
    induction n with
    | zero =>
      have : partialT A 0 = 1 := by rw [partialT, ← tprod_one]; simp
      rw [this]; exact R.one_mem
    | succ n ih =>
      rw [partialT_succ A n (by omega)]
      exact R.mul_mem (ih (by omega)) (slot_mem _ _)
  have h := this 7 le_rfl
  rwa [show partialT A 7 = tprod A by rw [partialT]; congr 1; funext i; simp [i.2]] at h

lemma tprod_single (a b : Idx) :
    tprod (fun k => single (a k) (b k) (1 : ℝ)) = single a b 1 := by
  ext x y
  simp only [tprod, of_apply, single_apply]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, funext_iff]
  exact propext forall_and

theorem cliffordRep_surjective : Function.Surjective cliffordRep := by
  intro M
  have hM : M ∈ R := by
    rw [matrix_eq_sum_single M]
    refine R.sum_mem fun a _ => R.sum_mem fun b _ => ?_
    rw [show single a b (M a b) = M a b • single a b (1 : ℝ) by
      ext x y; simp [single_apply], ← tprod_single]
    exact R.smul_mem (tprod_mem _) _
  exact hM

instance : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 14 → ℝ)) :=
  Module.Finite.of_basis ((Pi.basisFun ℝ (Fin 14)).ExteriorAlgebra)

instance : FiniteDimensional ℝ Cl77 :=
  LinearEquiv.finiteDimensional ϑ.symm

theorem finrank_Cl77 : Module.finrank ℝ Cl77 = 2 ^ 14 := by
  rw [ϑ.finrank_eq, Module.finrank_eq_card_basis
    ((Pi.basisFun ℝ (Fin 14)).ExteriorAlgebra), Fintype.card_finset, Fintype.card_fin]

theorem cliffordRep_bijective : Function.Bijective cliffordRep := by
  refine ⟨?_, cliffordRep_surjective⟩
  have H : Module.finrank ℝ Cl77 = Module.finrank ℝ M128 := by
    rw [finrank_Cl77, Module.finrank_matrix]; simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank H
    (f := cliffordRep.toLinearMap)).mpr cliffordRep_surjective

/-- (3.18): `Cl(7,7) ≅ ℝ(128)` as `ℝ`-algebras. -/
noncomputable def cl77Equiv : Cl77 ≃ₐ[ℝ] M128 := AlgEquiv.ofBijective cliffordRep cliffordRep_bijective

/-- The `↪` of (3.28): `ρ_D` is injective. -/
theorem rhoD_injective : Function.Injective rhoD := by
  intro x y h
  have h1 : toC (cliffordRep x) = toC (cliffordRep y) := congrArg Subtype.val h
  have h2 : cliffordRep x = cliffordRep y := by
    ext a b
    have := congrFun (congrFun h1 a) b
    simpa [toC] using this
  exact Subtype.ext (cliffordRep_bijective.1 h2)

end GU.Spinor

namespace GU

theorem diracRep_faithful : diracRep.Faithful :=
  Spinor.UC_equiv_U6464.injective.comp Spinor.rhoD_injective

end GU
