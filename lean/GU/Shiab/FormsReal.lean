import GU.Shiab.FormsCurvSpan

/-!
# Track 2 (real version), part 1: real-linear semantic operators

`curvR`, `einR : (Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) → (Idx4 → M128)` are the real-coefficient versions
of `semF ∘ curvForm` and `semF ∘ einsteinForm`. They are ℝ-linear (`curvR_add`, `curvR_smul`, …) and
agree with the integer ones on integer tensors (`curvR_cast`, `einR_cast`). `twoShiabS` is
ℝ-homogeneous (`twoShiabS_smul`).
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

abbrev TensR := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Real curvature form, semantically. -/
noncomputable def curvR (R : TensR) (I : Idx4) : M128 :=
  (pairs.map fun ab => if [ab.1, ab.2] = I then
    (pairs.map fun cd => R ab.1 ab.2 cd.1 cd.2 • CSum.toMat (mul (γ4 cd.1) (γ4 cd.2))).sum else 0).sum

lemma curvR_cast (R : Tens) : curvR (fun a b c d => (R a b c d : ℝ)) = semF (curvForm R) := by
  funext I
  simp only [curvR, curvForm, semF, List.map_map, Function.comp_def]
  congr 1; refine List.map_congr_left fun ab _ => ?_
  split_ifs
  · rw [toMat_flatMap]; simp only [toMat_smul]
  · rfl

lemma curvR_add (R R' : TensR) : curvR (R + R') = curvR R + curvR R' := by
  funext I
  simp only [curvR, Pi.add_apply, ← List.sum_map_add]
  congr 1; refine List.map_congr_left fun ab _ => ?_
  split_ifs
  · rw [← List.sum_map_add]; congr 1; refine List.map_congr_left fun cd _ => ?_; rw [add_smul]
  · simp

lemma curvR_smul (c : ℝ) (R : TensR) : curvR (c • R) = c • curvR R := by
  funext I
  simp only [curvR, Pi.smul_apply, smul_eq_mul, List.smul_sum, List.map_map, Function.comp_def]
  congr 1; refine List.map_congr_left fun ab _ => ?_
  split_ifs
  · rw [List.smul_sum, List.map_map]; congr 1; refine List.map_congr_left fun cd _ => ?_
    simp [mul_smul]
  · simp

lemma starS_smul (c : ℝ) (f : Idx4 → M128) : starS (c • f) = c • starS f := by
  funext J
  simp only [starS, Pi.smul_apply, List.smul_sum, List.map_map, Function.comp_def]
  congr 1; refine List.map_congr_left fun I _ => ?_
  split_ifs <;> simp [smul_comm c]

lemma wedgeS_smul {BR : M128 → M128 → M128} (hs : ∀ X (c : ℝ) Y, BR X (c • Y) = c • BR X Y)
    (F g : Idx4 → M128) (c : ℝ) : wedgeS BR F (c • g) = c • wedgeS BR F g := by
  funext K
  simp only [wedgeS, Pi.smul_apply, List.smul_sum, List.map_map, Function.comp_def]
  congr 1; refine List.map_congr_left fun I _ => ?_
  congr 1; refine List.map_congr_left fun J _ => ?_
  split_ifs <;> simp [hs, smul_comm c]

lemma CMR_smul (X : M128) (c : ℝ) (Y : M128) : CMR X (c • Y) = c • CMR X Y := by
  simp [CMR, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
lemma ACR_smul (X : M128) (c : ℝ) (Y : M128) : ACR X (c • Y) = c • ACR X Y := by
  simp [ACR, smul_add, Matrix.mul_smul, Matrix.smul_mul]

lemma twoShiabS_smul (c : ℝ) (f : Idx4 → M128) : twoShiabS (c • f) = c • twoShiabS f := by
  funext K
  simp only [twoShiabS, starS_smul, wedgeS_smul ACR_smul, wedgeS_smul CMR_smul, Pi.smul_apply,
    smul_sub, smul_comm (2 : ℝ) c]

/-- `twoShiabS` as an ℝ-linear map. -/
noncomputable def twoShiabL : (Idx4 → M128) →ₗ[ℝ] (Idx4 → M128) where
  toFun := twoShiabS
  map_add' := twoShiabS_add
  map_smul' := twoShiabS_smul

/-- `curvR` as an ℝ-linear map. -/
noncomputable def curvRL : TensR →ₗ[ℝ] (Idx4 → M128) where
  toFun := curvR
  map_add' := curvR_add
  map_smul' := curvR_smul

/-- Real Ricci and scalar curvature. -/
def ricR (R : TensR) (b d : Fin 4) : ℝ := ((List.finRange 4).map fun a => R a b a d).sum
def scalR (R : TensR) : ℝ := ((List.finRange 4).map fun b => ricR R b b).sum

/-- Real version of the inner list of `einsteinForm` (before `star`), semantically. -/
noncomputable def einInnerR (R : TensR) (I : Idx4) : M128 :=
  ((List.finRange 4).map fun a => if [a] = I then
    ((List.finRange 4).map fun b => (-2 * (2 * ricR R a b - (if a = b then scalR R else 0))) •
      CSum.toMat (γ4 b)).sum else 0).sum

/-- Real Einstein form, semantically: `−4 ⋆(Σ_a e^a ⊗ Σ_b G_ab γ_b)`. -/
noncomputable def einR (R : TensR) : Idx4 → M128 := starS (einInnerR R)

lemma ricR_cast (R : Tens) (b d : Fin 4) : ricR (fun a b c d => (R a b c d : ℝ)) b d = (ric R b d : ℝ) := by
  rw [ricR, ric, Int.cast_list_sum, List.map_map]; rfl
lemma scalR_cast (R : Tens) : scalR (fun a b c d => (R a b c d : ℝ)) = (scal R : ℝ) := by
  rw [scalR, scal, Int.cast_list_sum, List.map_map]
  congr 1; refine List.map_congr_left fun b _ => ?_
  exact ricR_cast R b b

lemma canon_einInner (R : Tens) : Canon ((List.finRange 4).map fun a => ([a],
    (List.finRange 4).flatMap fun b => smul (-2 * (2 * ric R a b - (if a = b then scal R else 0))) (γ4 b))) := by
  have hs : ∀ a : Fin 4, [a] ∈ allIdx := by decide
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact hs a

lemma einR_cast (R : Tens) : einR (fun a b c d => (R a b c d : ℝ)) = semF (einsteinForm R) := by
  funext J
  rw [einsteinForm, semF_star (canon_einInner R), einR]
  congr 1; funext I
  simp only [einInnerR, semF, List.map_map, Function.comp_def, ricR_cast, scalR_cast]
  congr 1; refine List.map_congr_left fun a _ => ?_
  split_ifs
  · rw [toMat_flatMap]; congr 1; refine List.map_congr_left fun b _ => ?_
    rw [toMat_smul]; push_cast; split_ifs <;> simp
  · rfl

lemma ricR_add (R R' : TensR) (b d : Fin 4) : ricR (R + R') b d = ricR R b d + ricR R' b d := by
  simp [ricR, List.sum_map_add]
lemma scalR_add (R R' : TensR) : scalR (R + R') = scalR R + scalR R' := by
  simp [scalR, ricR_add, List.sum_map_add]
lemma ricR_smul (c : ℝ) (R : TensR) (b d : Fin 4) : ricR (c • R) b d = c * ricR R b d := by
  simp [ricR, List.sum_map_mul_left]
lemma scalR_smul (c : ℝ) (R : TensR) : scalR (c • R) = c * scalR R := by
  simp [scalR, ricR_smul, List.sum_map_mul_left]

lemma einInnerR_add (R R' : TensR) : einInnerR (R + R') = einInnerR R + einInnerR R' := by
  funext I
  simp only [einInnerR, Pi.add_apply, ← List.sum_map_add]
  congr 1; refine List.map_congr_left fun a _ => ?_
  split_ifs
  · rw [← List.sum_map_add]; congr 1; refine List.map_congr_left fun b _ => ?_
    rw [ricR_add, scalR_add, ← add_smul]; congr 1; split_ifs <;> ring
  · simp

lemma einInnerR_smul (c : ℝ) (R : TensR) : einInnerR (c • R) = c • einInnerR R := by
  funext I
  simp only [einInnerR, Pi.smul_apply, List.smul_sum, List.map_map, Function.comp_def]
  congr 1; refine List.map_congr_left fun a _ => ?_
  split_ifs
  · rw [List.smul_sum, List.map_map]; congr 1; refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, ricR_smul, scalR_smul, smul_smul]; congr 1; split_ifs <;> ring
  · simp

/-- `einR` as an ℝ-linear map. -/
noncomputable def einRL : TensR →ₗ[ℝ] (Idx4 → M128) where
  toFun := einR
  map_add' R R' := by simp only [einR, einInnerR_add, starS_add']
  map_smul' c R := by simp only [einR, einInnerR_smul, starS_smul, RingHom.id_apply]

end GU.FormsW
