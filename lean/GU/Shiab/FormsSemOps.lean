/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.FormsSem

/-!
# Track 2, F1 step 2: semantic `star`, `wedge` and `twoShiab`

On functions `f : Idx4 → M128` (semantic forms):
* `starS f J = Σ_I [compl I = J] sign(I, Iᶜ) • f I`;
* `wedgeS BR f g K = Σ_I Σ_J [sortIdx (I ++ J) = K] sign(I, J) • BR (f I) (g J)`.
`semF_star` and `semF_wedge` show the list operations compute these on canonical forms.
`semF_twoShiab` follows: `semF (twoShiab ξ) = twoShiabS (semF ξ)`.
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

/-- Semantic Hodge star. -/
noncomputable def starS (f : Idx4 → M128) (J : Idx4) : M128 :=
  (allIdx.map fun I => if compl I = J then ((mergeSign I (compl I) : ℤ) : ℝ) • f I else 0).sum

/-- Semantic wedge with a bracket `BR` on the values. -/
noncomputable def wedgeS (BR : M128 → M128 → M128) (f g : Idx4 → M128) (K : Idx4) : M128 :=
  (allIdx.map fun I => (allIdx.map fun J =>
    if sortIdx (I ++ J) = K then ((mergeSign I J : ℤ) : ℝ) • BR (f I) (g J) else 0).sum).sum

lemma semF_star {A : Form} (hA : Canon A) (J : Idx4) : semF (star A) J = starS (semF A) J := by
  have h1 : semF (star A) J = (A.map fun y => if compl y.1 = J then
      ((mergeSign y.1 (compl y.1) : ℤ) : ℝ) • CSum.toMat y.2 else 0).sum := by
    simp only [star, semF, List.map_map, Function.comp_def, toMat_smul]
  rw [h1]
  let g : Idx4 → M128 →+ M128 := fun I =>
    { toFun := fun X => if compl I = J then ((mergeSign I (compl I) : ℤ) : ℝ) • X else 0
      map_zero' := by simp
      map_add' := fun X Y => by split_ifs <;> simp [smul_add] }
  exact sum_regroup g A hA

/-- Brackets that are additive in each argument. -/
structure BiAdd (BR : M128 → M128 → M128) : Prop where
  add_left : ∀ X X' Y, BR (X + X') Y = BR X Y + BR X' Y
  add_right : ∀ X Y Y', BR X (Y + Y') = BR X Y + BR X Y'
  zero_left : ∀ Y, BR 0 Y = 0
  zero_right : ∀ X, BR X 0 = 0

lemma semF_wedge_row {br : CSum → CSum → CSum} {BR : M128 → M128 → M128}
    (hbr : ∀ x y, CSum.toMat (br x y) = BR (CSum.toMat x) (CSum.toMat y)) (x : Idx4 × CSum)
    (B : Form) (K : Idx4) :
    semF (B.filterMap fun y => let s := mergeSign x.1 y.1
      if s = 0 then none else some (sortIdx (x.1 ++ y.1), smul s (br x.2 y.2))) K =
    (B.map fun y => if sortIdx (x.1 ++ y.1) = K then ((mergeSign x.1 y.1 : ℤ) : ℝ) •
      BR (CSum.toMat x.2) (CSum.toMat y.2) else 0).sum := by
  induction B with
  | nil => rfl
  | cons y B ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← ih]
    by_cases hs : mergeSign x.1 y.1 = 0
    · simp [hs]
    · simp only [hs, if_false, semF_cons, toMat_smul, hbr]

lemma semF_wedge {br : CSum → CSum → CSum} {BR : M128 → M128 → M128} (hBR : BiAdd BR)
    (hbr : ∀ x y, CSum.toMat (br x y) = BR (CSum.toMat x) (CSum.toMat y)) {A B : Form}
    (hA : Canon A) (hB : Canon B) (K : Idx4) :
    semF (wedge br A B) K = wedgeS BR (semF A) (semF B) K := by
  have h1 : semF (wedge br A B) K = (A.map fun x => (B.map fun y =>
      if sortIdx (x.1 ++ y.1) = K then ((mergeSign x.1 y.1 : ℤ) : ℝ) •
        BR (CSum.toMat x.2) (CSum.toMat y.2) else 0).sum).sum := by
    rw [wedge, semF_flatMap]
    congr 1; exact List.map_congr_left fun x _ => semF_wedge_row hbr x B K
  rw [h1]
  -- regroup the inner sum over `B`, then the outer sum over `A`
  have inner : ∀ (I : Idx4) (X : M128), (B.map fun y => if sortIdx (I ++ y.1) = K then
      ((mergeSign I y.1 : ℤ) : ℝ) • BR X (CSum.toMat y.2) else 0).sum =
      (allIdx.map fun J => if sortIdx (I ++ J) = K then ((mergeSign I J : ℤ) : ℝ) • BR X (semF B J)
        else 0).sum := fun I X => by
    let g : Idx4 → M128 →+ M128 := fun J =>
      { toFun := fun Y => if sortIdx (I ++ J) = K then ((mergeSign I J : ℤ) : ℝ) • BR X Y else 0
        map_zero' := by simp [hBR.zero_right]
        map_add' := fun Y Y' => by split_ifs <;> simp [hBR.add_right, smul_add] }
    exact sum_regroup g B hB
  simp only [inner]
  let g : Idx4 → M128 →+ M128 := fun I =>
    { toFun := fun X => (allIdx.map fun J => if sortIdx (I ++ J) = K then
        ((mergeSign I J : ℤ) : ℝ) • BR X (semF B J) else 0).sum
      map_zero' := by simp [hBR.zero_left]
      map_add' := fun X X' => by
        rw [← List.sum_map_add]
        congr 1; refine List.map_congr_left fun J _ => ?_
        split_ifs <;> simp [hBR.add_left, smul_add] }
  exact sum_regroup g A hA

/-! ### `twoShiab` in semantics -/

/-- Commutator and anticommutator brackets on matrices. -/
def CMR (X Y : M128) : M128 := X * Y - Y * X
def ACR (X Y : M128) : M128 := X * Y + Y * X

lemma biAdd_CMR : BiAdd CMR :=
  ⟨fun _ _ _ => by simp [CMR, add_mul, mul_add]; abel, fun _ _ _ => by simp [CMR, add_mul, mul_add]; abel,
   fun _ => by simp [CMR], fun _ => by simp [CMR]⟩

lemma biAdd_ACR : BiAdd ACR :=
  ⟨fun _ _ _ => by simp [ACR, add_mul, mul_add]; abel, fun _ _ _ => by simp [ACR, add_mul, mul_add]; abel,
   fun _ => by simp [ACR], fun _ => by simp [ACR]⟩

lemma canon_Φ1 : Canon Φ1 := by unfold Canon; decide
lemma canon_Φ2 : Canon Φ2 := by unfold Canon; decide

/-- Semantic `twoShiab`. -/
noncomputable def twoShiabS (f : Idx4 → M128) (K : Idx4) : M128 :=
  (2 : ℝ) • wedgeS CMR (semF Φ1) (starS f) K -
    starS (wedgeS ACR (semF Φ1) (starS (wedgeS ACR (semF Φ2) (starS f)))) K

/-- **`twoShiab` computes `twoShiabS`** on canonical forms. -/
theorem semF_twoShiab {ξ : Form} (hξ : Canon ξ) (K : Idx4) :
    semF (twoShiab ξ) K = twoShiabS (semF ξ) K := by
  have h2 : ∀ c, CSum.toMat (smul 2 c) = (2 : ℝ) • CSum.toMat c := fun c => by
    rw [toMat_smul]; norm_num
  let two : M128 →+ M128 := ⟨⟨fun X => (2 : ℝ) • X, smul_zero _⟩, fun X Y => smul_add _ X Y⟩
  let ng : M128 →+ M128 := ⟨⟨fun X => -X, neg_zero⟩, fun X Y => neg_add _ _⟩
  rw [twoShiab, semF_append, semF_map_snd _ _ two h2,
    semF_map_snd _ _ ng (fun c => by simp [ng, toMat_neg])]
  show (2 : ℝ) • semF (wedge cm Φ1 (star ξ)) K + -semF (star (wedge acm Φ1 (star (wedge acm Φ2 (star ξ))))) K = _
  have hs : semF (star ξ) = starS (semF ξ) := funext (semF_star hξ)
  have hw2 : semF (wedge acm Φ2 (star ξ)) = wedgeS ACR (semF Φ2) (starS (semF ξ)) := funext fun L => by
    rw [semF_wedge biAdd_ACR toMat_acm canon_Φ2 (canon_star _), hs]
  have hs2 : semF (star (wedge acm Φ2 (star ξ))) = starS (wedgeS ACR (semF Φ2) (starS (semF ξ))) :=
    funext fun L => by rw [semF_star (canon_wedge _ _ _), hw2]
  have hw1 : semF (wedge acm Φ1 (star (wedge acm Φ2 (star ξ)))) =
      wedgeS ACR (semF Φ1) (starS (wedgeS ACR (semF Φ2) (starS (semF ξ)))) := funext fun L => by
    rw [semF_wedge biAdd_ACR toMat_acm canon_Φ1 (canon_star _), hs2]
  have hw0 : semF (wedge cm Φ1 (star ξ)) K = wedgeS CMR (semF Φ1) (starS (semF ξ)) K := by
    rw [semF_wedge biAdd_CMR toMat_cm canon_Φ1 (canon_star _), hs]
  rw [hw0, semF_star (canon_wedge _ _ _), hw1, twoShiabS, sub_eq_add_neg]

end GU.FormsW
