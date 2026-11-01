/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.TorusKernel

/-!
# The torus kernel on `U(1)⁵ = ℝ⁵/2πℤ⁵` is `(ℤ/2)⁴` as a group

The parity map `kpar : ker torus →* (ℤ/2)⁵` sends `s = nπ` to `n mod 2`. Its kernel is exactly the lattice
`2πℤ⁵` (`mem_ker_kpar`), and its range is the even-weight subgroup `evenSub` (`range_kpar`). The first
isomorphism theorem gives `ker torus / 2πℤ⁵ ≃* evenSub` (`torusKer_quot_equiv`), and dropping the last
coordinate gives `evenSub ≃+ (ℤ/2)⁴` (`evenSub_equiv`). So `ker torus / 2πℤ⁵ ≃* (ℤ/2)⁴` (**`torusKer_quot_equiv_four`**). The induced map on
`U(1)⁵ = ℝ⁵/2πℤ⁵` is not constructed; its kernel is by definition `ker torus / 2πℤ⁵` (by hand).
-/

namespace GU.Spinor

open Real

/-- Even-weight vectors in `(ℤ/2)⁵`. -/
def evenSub : AddSubgroup (Fin 5 → ZMod 2) :=
  (AddMonoidHom.mk' (fun v : Fin 5 → ZMod 2 => ∑ k, v k) (fun v w => by
    simp [Finset.sum_add_distrib])).ker

lemma mem_evenSub (v : Fin 5 → ZMod 2) : v ∈ evenSub ↔ ∑ k, v k = 0 := Iff.rfl

/-- **`evenSub ≅ (ℤ/2)⁴`**: drop the last coordinate. -/
def evenSub_equiv : evenSub ≃+ (Fin 4 → ZMod 2) where
  toFun v := fun i => v.1 (Fin.castSucc i)
  invFun w := ⟨Fin.snoc w (∑ i, w i), by
    rw [mem_evenSub, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]⟩
  left_inv v := by
    apply Subtype.ext
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [Fin.snoc_last]
      have h := (mem_evenSub _).mp v.2
      rw [Fin.sum_univ_castSucc] at h
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ h
    · simp
  right_inv w := by funext i; simp
  map_add' v w := by funext i; rfl

lemma ker_coord (x : torus.ker) (k : Fin 5) :
    Multiplicative.toAdd (x.1 k) / π = (⌊Multiplicative.toAdd (x.1 k) / π⌋ : ℝ) := by
  have hx : torus (fun k => Multiplicative.ofAdd (Multiplicative.toAdd (x.1 k))) = 1 := x.2
  obtain ⟨n, hn, -⟩ := (torus_eq_one_iff _).mp hx
  rw [hn k, mul_div_cancel_right₀ _ pi_ne_zero, Int.floor_intCast]

lemma ker_even (x : torus.ker) : Even (∑ k, ⌊Multiplicative.toAdd (x.1 k) / π⌋) := by
  have hx : torus (fun k => Multiplicative.ofAdd (Multiplicative.toAdd (x.1 k))) = 1 := x.2
  obtain ⟨n, hn, he⟩ := (torus_eq_one_iff _).mp hx
  have : ∀ k, ⌊Multiplicative.toAdd (x.1 k) / π⌋ = n k := fun k => by
    rw [hn k, mul_div_cancel_right₀ _ pi_ne_zero, Int.floor_intCast]
  simpa only [this] using he

/-- `s = nπ ↦ n mod 2`. -/
noncomputable def kpar : torus.ker →* Multiplicative (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun k => ((⌊Multiplicative.toAdd (x.1 k) / π⌋ : ℤ) : ZMod 2)
  map_one' := by
    apply congrArg Multiplicative.ofAdd; funext k; simp
  map_mul' x y := by
    apply congrArg Multiplicative.ofAdd
    funext k
    have hx := ker_coord x k
    have hy := ker_coord y k
    have hxy : ⌊Multiplicative.toAdd ((x * y).1 k) / π⌋ =
        ⌊Multiplicative.toAdd (x.1 k) / π⌋ + ⌊Multiplicative.toAdd (y.1 k) / π⌋ := by
      show ⌊(Multiplicative.toAdd (x.1 k) + Multiplicative.toAdd (y.1 k)) / π⌋ = _
      rw [add_div, hx, hy, ← Int.cast_add, Int.floor_intCast]
      simp only [Int.floor_intCast]
    simp only [Pi.add_apply]
    rw [hxy, Int.cast_add]
    rfl

lemma zmod2_eq_zero_iff (n : ℤ) : ((n : ZMod 2) = 0) ↔ Even n := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]; norm_num

/-- **The kernel of `kpar` is the lattice `2πℤ⁵`.** -/
theorem mem_ker_kpar (x : torus.ker) :
    x ∈ kpar.ker ↔ ∀ k, ∃ m : ℤ, Multiplicative.toAdd (x.1 k) = m * (2 * π) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h k
    have hk := congrFun (congrArg Multiplicative.toAdd h) k
    change ((⌊Multiplicative.toAdd (x.1 k) / π⌋ : ℤ) : ZMod 2) = 0 at hk
    obtain ⟨m, hm⟩ := (zmod2_eq_zero_iff _).mp hk
    refine ⟨m, ?_⟩
    have hc := ker_coord x k
    rw [hm] at hc
    push_cast at hc
    field_simp at hc
    linarith
  · intro h
    apply congrArg Multiplicative.ofAdd
    funext k
    obtain ⟨m, hm⟩ := h k
    show ((⌊Multiplicative.toAdd (x.1 k) / π⌋ : ℤ) : ZMod 2) = 0
    rw [hm, show (m : ℝ) * (2 * π) / π = ((m + m : ℤ) : ℝ) by
      push_cast; field_simp; ring, Int.floor_intCast, zmod2_eq_zero_iff]
    exact ⟨m, rfl⟩

/-- **The range of `kpar` is the even-weight subgroup.** -/
theorem range_kpar (v : Fin 5 → ZMod 2) :
    Multiplicative.ofAdd v ∈ kpar.range ↔ v ∈ evenSub := by
  constructor
  · rintro ⟨x, hx⟩
    have hv : v = fun k => ((⌊Multiplicative.toAdd (x.1 k) / π⌋ : ℤ) : ZMod 2) :=
      (congrArg Multiplicative.toAdd hx).symm
    rw [mem_evenSub, hv, ← Int.cast_sum, zmod2_eq_zero_iff]
    exact ker_even x
  · intro hv
    let n : Fin 5 → ℤ := fun k => ((v k).val : ℤ)
    have hn : (fun k => Multiplicative.ofAdd ((n k : ℝ) * π)) ∈ torus.ker := by
      rw [MonoidHom.mem_ker]
      refine (torus_eq_one_iff _).mpr ⟨n, fun k => rfl, ?_⟩
      rw [← zmod2_eq_zero_iff, Int.cast_sum]
      simpa [n] using (mem_evenSub v).mp hv
    refine ⟨⟨_, hn⟩, ?_⟩
    apply congrArg Multiplicative.ofAdd
    funext k
    show ((⌊(n k : ℝ) * π / π⌋ : ℤ) : ZMod 2) = v k
    rw [mul_div_cancel_right₀ _ pi_ne_zero, Int.floor_intCast]
    simp [n]

/-- **`ker torus / 2πℤ⁵ ≃* evenSub`** (first isomorphism theorem for `kpar`). -/
noncomputable def torusKer_quot_equiv :
    torus.ker ⧸ kpar.ker ≃* Multiplicative evenSub :=
  (QuotientGroup.quotientKerEquivRange kpar).trans
    { toFun := fun y => Multiplicative.ofAdd ⟨Multiplicative.toAdd y.1, (range_kpar _).mp y.2⟩
      invFun := fun v => ⟨Multiplicative.ofAdd (Multiplicative.toAdd v).1,
        (range_kpar _).mpr (Multiplicative.toAdd v).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

/-- **`ker torus / 2πℤ⁵ ≃* (ℤ/2)⁴`** (the kernel on `U(1)⁵`, by hand via the quotient), where
`kpar.ker` is exactly the lattice `2πℤ⁵` (`mem_ker_kpar`). -/
noncomputable def torusKer_quot_equiv_four :
    torus.ker ⧸ kpar.ker ≃* Multiplicative (Fin 4 → ZMod 2) :=
  torusKer_quot_equiv.trans (AddEquiv.toMultiplicative evenSub_equiv)

end GU.Spinor
