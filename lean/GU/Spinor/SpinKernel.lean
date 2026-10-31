import GU.Spinor.SpinCover

/-!
# The kernel of `Spin(7,7) → O(7,7)` is exactly `{±1}`

`vecRep_ker`: if `x ∈ Spin(7,7)` acts trivially on `ℝ¹⁴` then `x = ±1`.
Proof: `x ι(v) x* = ι(v)` and `x* x = 1` give `x ι(v) = ι(v) x`; the `ι(v)` generate `Cl(7,7)`
(`adjoin_range_ι`), so `x` is central; under `Cl(7,7) ≅ ℝ(128)` (`cl77Equiv`) the centre is the
scalars (`Matrix.center_eq_range`), so `x = c·1`, and `x* x = 1` gives `c² = 1`.
With `vecRep_neg_one` the cover is exactly two-to-one onto its image.
-/

namespace GU.Spinor

open CliffordAlgebra

lemma comm_ι_of_vecRep (x : Spin77) (hx : ∀ v, vecRep x v = v) (v : Fin 14 → ℝ) :
    (x : Cl77) * ι Q77 v = ι Q77 v * (x : Cl77) := by
  have h : (x : Cl77) * ι Q77 v * star (x : Cl77) = ι Q77 v := by
    rw [← ι_vecL]; exact congrArg _ (hx v)
  calc (x : Cl77) * ι Q77 v = (x : Cl77) * ι Q77 v * (star (x : Cl77) * (x : Cl77)) := by
        rw [spinGroup.star_mul_self_of_mem x.2, mul_one]
    _ = ι Q77 v * (x : Cl77) := by rw [← mul_assoc, h]

lemma central_of_vecRep (x : Spin77) (hx : ∀ v, vecRep x v = v) (y : Cl77) :
    (x : Cl77) * y = y * (x : Cl77) := by
  have hy : y ∈ Algebra.adjoin ℝ (Set.range (ι Q77)) := by rw [adjoin_range_ι]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem z hz => obtain ⟨v, rfl⟩ := hz; exact comm_ι_of_vecRep x hx v
  | algebraMap r => exact (Algebra.commutes r _).symm
  | add a b _ _ ha hb => rw [mul_add, add_mul, ha, hb]
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

lemma scalar_of_vecRep (x : Spin77) (hx : ∀ v, vecRep x v = v) :
    ∃ c : ℝ, (x : Cl77) = algebraMap ℝ Cl77 c := by
  have hc : cl77Equiv (x : Cl77) ∈ Set.center M128 := by
    rw [Semigroup.mem_center_iff]
    intro m
    obtain ⟨y, rfl⟩ := cl77Equiv.surjective m
    rw [← map_mul, ← map_mul, central_of_vecRep x hx y]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, cl77Equiv.injective ?_⟩
  rw [← hc, AlgEquiv.commutes]
  rfl

/-- **Kernel of the vector representation**: only `±1` act trivially. -/
theorem vecRep_ker (x : Spin77) (hx : ∀ v, vecRep x v = v) :
    (x : Cl77) = 1 ∨ (x : Cl77) = -1 := by
  obtain ⟨c, hc⟩ := scalar_of_vecRep x hx
  have h1 := spinGroup.star_mul_self_of_mem x.2
  rw [hc, show star (algebraMap ℝ Cl77 c) = algebraMap ℝ Cl77 c by
    rw [CliffordAlgebra.star_def, involute.commutes, reverse.commutes], ← map_mul] at h1
  have hc2 : c * c = 1 := (algebraMap ℝ Cl77).injective (by rw [h1, map_one])
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · left; rw [hc, h, map_one]
  · right; rw [hc, h, map_neg, map_one]

/-- **The covering is exactly two-to-one**: `vecRep x = vecRep y ↔ x = ±y`. -/
theorem vecRep_eq_iff (x y : Spin77) :
    vecRep x = vecRep y ↔ (x : Cl77) = y ∨ (x : Cl77) = -y := by
  constructor
  · intro h
    have hk : ∀ v, vecRep (x * star y) v = v := fun v => by
      rw [map_mul, LinearEquiv.mul_apply, h, ← LinearEquiv.mul_apply, ← map_mul,
        spinGroup.mul_star_self, map_one]; rfl
    have hy : (star (y : Cl77)) * y = 1 := spinGroup.star_mul_self_of_mem y.2
    rcases vecRep_ker _ hk with e | e
    · left
      have : (x : Cl77) * star (y : Cl77) * y = y := by change (x : Cl77) * star (y : Cl77) = 1 at e; rw [e, one_mul]
      rwa [mul_assoc, hy, mul_one] at this
    · right
      have : (x : Cl77) * star (y : Cl77) * y = -y := by
        change (x : Cl77) * star (y : Cl77) = -1 at e; rw [e, neg_one_mul]
      rwa [mul_assoc, hy, mul_one] at this
  · rintro (e | e)
    · rw [Subtype.ext e]
    · have : x = ⟨-1, neg_one_mem_spin⟩ * y := Subtype.ext (by rw [Submonoid.coe_mul, e, neg_one_mul])
      rw [this, map_mul]
      ext v
      rw [LinearEquiv.mul_apply, vecRep_neg_one]

end GU.Spinor
