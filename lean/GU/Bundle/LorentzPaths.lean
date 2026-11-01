import GU.Bundle.LorentzFrames

/-!
# Phase 6, item 1 (the general-X clause of Phase 5 item 5): paths of matrices

* **`joinedIn_GP3`**: `GL⁺(3, ℝ)` is path-connected (every `N` with `det N > 0` is joined to `1` inside
  `{det > 0}`), from Mathlib's decomposition into transvections and a diagonal matrix.
* **`joinedIn_SP`**: the matrices with `det > 0` and future timelike first row (`SP`) are joined to `1`
  inside `SP`.
* **`lorO_mem_SO0`**: for every orthochronous Lorentz transformation `Λ`, `lorM Λ ∈ SO₀(7,7)`.
-/

namespace GU.Library

open Matrix GU GU.Observerse GU.Spinor GU.Chimeric TopologicalSpace Topology
open scoped ContDiff Manifold

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

noncomputable section

/-- A path from a continuous function on `ℝ`. -/
lemma joinedIn_of_fun {X : Type*} [TopologicalSpace X] {F : Set X} {x y : X} (f : ℝ → X)
    (hf : Continuous f) (h0 : f 0 = x) (h1 : f 1 = y) (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ F) :
    JoinedIn F x y :=
  ⟨⟨⟨fun t => f t, hf.comp continuous_subtype_val⟩, h0, h1⟩, fun t => hm t t.2⟩

/-! ### `GL⁺(3)` -/

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

/-- `GL⁺(3)`. -/
def GP3 : Set M3 := {N | 0 < N.det}

lemma GP3_joined_mul {A B : M3} (hA : JoinedIn GP3 1 A) (hB : JoinedIn GP3 1 B) :
    JoinedIn GP3 1 (A * B) := by
  refine ⟨⟨⟨fun t => hA.somePath t * hB.somePath t,
    hA.somePath.continuous.mul hB.somePath.continuous⟩, by simp, by simp⟩, fun t => ?_⟩
  show 0 < (hA.somePath t * hB.somePath t).det
  rw [Matrix.det_mul]
  exact mul_pos (hA.somePath_mem t) (hB.somePath_mem t)

lemma GP3_transvection {i j : Fin 3} (hij : i ≠ j) (c : ℝ) :
    JoinedIn GP3 1 (transvection i j c) := by
  refine joinedIn_of_fun (fun t => transvection i j (t * c)) ?_ (by simp) (by simp) fun t _ => ?_
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show 0 < (transvection i j (t * c)).det
    rw [det_transvection_of_ne (h := hij)]; exact one_pos

lemma GP3_list (L : List (TransvectionStruct (Fin 3) ℝ)) :
    JoinedIn GP3 1 (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => exact JoinedIn.refl (show (0 : ℝ) < (1 : M3).det by simp)
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    exact GP3_joined_mul (GP3_transvection t.hij t.c) ih

lemma GP3_posdiag {D : Fin 3 → ℝ} (hD : ∀ i, 0 < D i) : JoinedIn GP3 1 (diagonal D) := by
  refine joinedIn_of_fun (fun t => diagonal fun i => (1 - t) + t * D i) ?_ (by simp) (by simp)
    fun t ht => ?_
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  · show 0 < (diagonal fun i => (1 - t) + t * D i).det
    rw [det_diagonal]
    refine Finset.prod_pos fun i _ => ?_
    have := hD i
    rcases ht with ⟨h0, h1⟩
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; linarith
    · have := mul_nonneg h0 this.le
      linarith

/-- `diag(−1,−1,1)` and its permutations are products of transvections. -/
lemma GP3_signpair {a b : Fin 3} (hab : a ≠ b) :
    JoinedIn GP3 1 ((transvection a b 1 * transvection b a (-1) * transvection a b 1) *
      (transvection a b 1 * transvection b a (-1) * transvection a b 1)) := by
  have h := fun c => GP3_transvection hab c
  have h' := fun c => GP3_transvection hab.symm c
  exact GP3_joined_mul (GP3_joined_mul (GP3_joined_mul (h 1) (h' (-1))) (h 1))
    (GP3_joined_mul (GP3_joined_mul (h 1) (h' (-1))) (h 1))

lemma signpair_eq {a b : Fin 3} (hab : a ≠ b) :
    (transvection a b (1 : ℝ) * transvection b a (-1) * transvection a b 1) *
      (transvection a b 1 * transvection b a (-1) * transvection a b 1) =
    diagonal fun i => if i = a ∨ i = b then (-1 : ℝ) else 1 := by
  fin_cases a <;> fin_cases b <;> (try exact absurd rfl hab) <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single,
        Matrix.diagonal])

lemma GP3_signdiag {a b : Fin 3} (hab : a ≠ b) :
    JoinedIn GP3 1 (diagonal fun i => if i = a ∨ i = b then -1 else 1) := by
  rw [← signpair_eq hab]
  exact GP3_signpair hab

lemma GP3_diag {D : Fin 3 → ℝ} (hD : 0 < (diagonal D).det) : JoinedIn GP3 1 (diagonal D) := by
  rw [det_diagonal, Fin.prod_univ_three] at hD
  have hne : ∀ i, D i ≠ 0 := by
    intro i h
    fin_cases i <;> simp_all
  -- write `D = s · |D|` with `s` a sign vector having an even number of `−1`
  have habs : ∀ i, 0 < |D i| := fun i => abs_pos.mpr (hne i)
  have hsplit : ∀ s : Fin 3 → ℝ, (∀ i, s i * |D i| = D i) →
      diagonal D = diagonal s * diagonal fun i => |D i| := by
    intro s hs
    rw [diagonal_mul_diagonal]
    congr 1; funext i; exact (hs i).symm
  have hpos := GP3_posdiag habs
  rcases lt_or_gt_of_ne (hne 0) with h0 | h0 <;> rcases lt_or_gt_of_ne (hne 1) with h1 | h1 <;>
    rcases lt_or_gt_of_ne (hne 2) with h2 | h2
  · exfalso; nlinarith [mul_pos_of_neg_of_neg h0 h1]
  · rw [hsplit (fun i => if i = 0 ∨ i = 1 then -1 else 1) (fun i => by
      fin_cases i <;> simp [abs_of_neg h0, abs_of_neg h1, abs_of_pos h2])]
    have hs := GP3_signdiag (show (0 : Fin 3) ≠ 1 by decide)
    exact GP3_joined_mul (by convert hs using 3) hpos
  · rw [hsplit (fun i => if i = 0 ∨ i = 2 then -1 else 1) (fun i => by
      fin_cases i <;> simp [abs_of_neg h0, abs_of_pos h1, abs_of_neg h2])]
    have hs := GP3_signdiag (show (0 : Fin 3) ≠ 2 by decide)
    exact GP3_joined_mul (by convert hs using 3) hpos
  · exfalso; nlinarith [mul_neg_of_neg_of_pos h0 h1]
  · rw [hsplit (fun i => if i = 1 ∨ i = 2 then -1 else 1) (fun i => by
      fin_cases i <;> simp [abs_of_pos h0, abs_of_neg h1, abs_of_neg h2])]
    have hs := GP3_signdiag (show (1 : Fin 3) ≠ 2 by decide)
    exact GP3_joined_mul (by convert hs using 3) hpos
  · exfalso; nlinarith [mul_neg_of_pos_of_neg h0 h1]
  · exfalso; nlinarith [mul_pos h0 h1]
  · rw [show diagonal D = diagonal fun i => |D i| by
      congr 1; funext i; fin_cases i <;> simp [abs_of_pos h0, abs_of_pos h1, abs_of_pos h2]]
    exact hpos

lemma det_list_transvec (L : List (TransvectionStruct (Fin 3) ℝ)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, det_mul, ih, mul_one]
    exact det_transvection_of_ne t.i t.j t.hij t.c

/-- **`GL⁺(3)` is path-connected.** -/
theorem joinedIn_GP3 {N : M3} (hN : 0 < N.det) : JoinedIn GP3 1 N := by
  obtain ⟨L, L', D, hLD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec N
  have hD : 0 < (diagonal D).det := by
    rw [hLD, det_mul, det_mul, det_list_transvec, det_list_transvec] at hN
    simpa using hN
  rw [hLD]
  exact GP3_joined_mul (GP3_joined_mul (GP3_list L) (GP3_diag hD)) (GP3_list L')

/-! ### Matrices with future timelike first row -/

/-- `det > 0` and future timelike first row. -/
def SP : Set M4 := {P | 0 < P.det ∧ 0 < P 0 0 ∧ P 0 1 ^ 2 + P 0 2 ^ 2 + P 0 3 ^ 2 < P 0 0 ^ 2}

/-- The `3 × 3` block in the lower right. -/
def blk (N : M3) : M4 :=
  !![1, 0, 0, 0; 0, N 0 0, N 0 1, N 0 2; 0, N 1 0, N 1 1, N 1 2; 0, N 2 0, N 2 1, N 2 2]

lemma det_blk (N : M3) : (blk N).det = N.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_three, Matrix.det_fin_three]
  simp [blk, Matrix.det_fin_three, Fin.succAbove]

lemma continuous_blk : Continuous blk := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop

lemma blk_one : blk 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.one_apply]

lemma diag_ones : diagonal ![(1 : ℝ), 1, 1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply]

lemma SP_blk {N : M3} (hN : 0 < N.det) : blk N ∈ SP := by
  refine ⟨by rw [det_blk]; exact hN, by simp [blk], by simp [blk]⟩

lemma SP_joined_blk {N : M3} (hN : 0 < N.det) : JoinedIn SP 1 (blk N) := by
  obtain ⟨γ, hγ⟩ := joinedIn_GP3 hN
  refine ⟨⟨⟨fun t => blk (γ t), continuous_blk.comp γ.continuous⟩, by simp [blk_one], by simp⟩,
    fun t => SP_blk (hγ t)⟩

/-- Step 1: clear the first row. -/
def Ucl (P : M4) (t : ℝ) : M4 :=
  transvection 0 1 (-(t * P 0 1 / P 0 0)) * transvection 0 2 (-(t * P 0 2 / P 0 0)) *
    transvection 0 3 (-(t * P 0 3 / P 0 0))

lemma det_Ucl (P : M4) (t : ℝ) : (Ucl P t).det = 1 := by
  unfold Ucl
  rw [det_mul, det_mul, det_transvection_of_ne _ _ (by decide), det_transvection_of_ne _ _ (by decide),
    det_transvection_of_ne _ _ (by decide)]
  simp

lemma row0_Ucl (P : M4) (hP : P 0 0 ≠ 0) (t : ℝ) (j : Fin 4) :
    (P * Ucl P t) 0 j = if j = 0 then P 0 0 else (1 - t) * P 0 j := by
  fin_cases j <;>
    simp [Ucl, transvection, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single] <;>
    field_simp <;> ring

lemma continuous_Ucl (P : M4) : Continuous (Ucl P) := by
  unfold Ucl
  refine ((Continuous.mul ?_ ?_).mul ?_) <;>
    (refine continuous_pi fun a => continuous_pi fun b => ?_;
     simp only [transvection, Matrix.add_apply, Matrix.single_apply]; split_ifs <;> fun_prop)

lemma SP_step1 {P : M4} (hP : P ∈ SP) : JoinedIn SP P (P * Ucl P 1) := by
  obtain ⟨hd, h0, ht⟩ := hP
  refine joinedIn_of_fun (fun t => P * Ucl P t) (continuous_const.mul (continuous_Ucl P)) ?_ rfl
    fun t ht' => ?_
  · show P * Ucl P 0 = P
    unfold Ucl; simp
  · refine ⟨by rw [det_mul, det_Ucl, mul_one]; exact hd, ?_, ?_⟩
    · rw [row0_Ucl P h0.ne']; simp; exact h0
    · rw [row0_Ucl P h0.ne', row0_Ucl P h0.ne', row0_Ucl P h0.ne', row0_Ucl P h0.ne']
      simp only [show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
        show (3 : Fin 4) ≠ 0 by decide, if_false, if_true]
      have hq : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht'.1, ht'.2]
      have hS : 0 ≤ P 0 1 ^ 2 + P 0 2 ^ 2 + P 0 3 ^ 2 := by positivity
      nlinarith

/-- Step 2: clear the first column. -/
def Vcl (P : M4) (t : ℝ) : M4 :=
  transvection 1 0 (-(t * P 1 0 / P 0 0)) * transvection 2 0 (-(t * P 2 0 / P 0 0)) *
    transvection 3 0 (-(t * P 3 0 / P 0 0))

lemma det_Vcl (P : M4) (t : ℝ) : (Vcl P t).det = 1 := by
  unfold Vcl
  rw [det_mul, det_mul, det_transvection_of_ne _ _ (by decide), det_transvection_of_ne _ _ (by decide),
    det_transvection_of_ne _ _ (by decide)]
  simp

lemma continuous_Vcl (P : M4) : Continuous (Vcl P) := by
  unfold Vcl
  refine ((Continuous.mul ?_ ?_).mul ?_) <;>
    (refine continuous_pi fun a => continuous_pi fun b => ?_;
     simp only [transvection, Matrix.add_apply, Matrix.single_apply]; split_ifs <;> fun_prop)

lemma Vcl_entry (P : M4) (hP : P 0 0 ≠ 0) (h1 : P 0 1 = 0) (h2 : P 0 2 = 0) (h3 : P 0 3 = 0)
    (t : ℝ) (i j : Fin 4) :
    (Vcl P t * P) i j = if i ≠ 0 ∧ j = 0 then (1 - t) * P i 0 else P i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Vcl, transvection, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single,
      h1, h2, h3] <;> field_simp <;> ring

lemma SP_step2 {P : M4} (hP : P ∈ SP) (h1 : P 0 1 = 0) (h2 : P 0 2 = 0) (h3 : P 0 3 = 0) :
    JoinedIn SP P (Vcl P 1 * P) := by
  obtain ⟨hd, h0, ht⟩ := hP
  refine joinedIn_of_fun (fun t => Vcl P t * P) ((continuous_Vcl P).mul continuous_const) ?_ rfl
    fun t _ => ?_
  · show Vcl P 0 * P = P
    unfold Vcl; simp
  · refine ⟨by rw [det_mul, det_Vcl, one_mul]; exact hd, ?_, ?_⟩
    · rw [Vcl_entry P h0.ne' h1 h2 h3]; simp; exact h0
    · simp only [Vcl_entry P h0.ne' h1 h2 h3]
      simp [h1, h2, h3]; nlinarith

/-- Step 3: a block matrix. -/
lemma eq_diag_blk {P : M4} (h1 : P 0 1 = 0) (h2 : P 0 2 = 0) (h3 : P 0 3 = 0) (g1 : P 1 0 = 0)
    (g2 : P 2 0 = 0) (g3 : P 3 0 = 0) :
    P = diagonal ![P 0 0, 1, 1, 1] * blk (Matrix.of fun i j => P i.succ j.succ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_four, *] <;> rfl

lemma SP_step3 {a : ℝ} (ha : 0 < a) {N : M3} (hN : 0 < N.det) :
    JoinedIn SP (diagonal ![a, 1, 1, 1] * blk N) (blk N) := by
  refine joinedIn_of_fun (fun t => diagonal ![(1 - t) * a + t, 1, 1, 1] * blk N) ?_ (by simp) ?_
    fun t ht => ?_
  · refine Continuous.mul ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs
    · fin_cases i <;> simp <;> fun_prop
    · fun_prop
  · simp [diag_ones]
  · have hp : 0 < (1 - t) * a + t := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h; norm_num
      · nlinarith [ht.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [det_mul, det_diagonal, Fin.prod_univ_four, det_blk]
      simp; exact mul_pos hp hN
    · simp [Matrix.mul_apply, Fin.sum_univ_four, blk, Matrix.diagonal]; exact hp
    · simp [Matrix.mul_apply, Fin.sum_univ_four, blk, Matrix.diagonal]; nlinarith

/-- **Every matrix with `det > 0` and future timelike first row is joined to `1` inside `SP`.** -/
theorem joinedIn_SP {P : M4} (hP : P ∈ SP) : JoinedIn SP 1 P := by
  have h00 := hP.2.1
  set P1 := P * Ucl P 1 with hP1
  have j1 := SP_step1 hP
  have hP1m : P1 ∈ SP := j1.target_mem
  have r : ∀ j : Fin 4, j ≠ 0 → P1 0 j = 0 := fun j hj => by
    rw [hP1, row0_Ucl P h00.ne', if_neg hj]; ring
  have e1 := r 1 (by decide)
  have e2 := r 2 (by decide)
  have e3 := r 3 (by decide)
  have h10 : P1 0 0 ≠ 0 := hP1m.2.1.ne'
  set P2 := Vcl P1 1 * P1 with hP2
  have j2 := SP_step2 hP1m e1 e2 e3
  have hent := Vcl_entry P1 h10 e1 e2 e3 1
  have f : ∀ i j : Fin 4, P2 i j = if i ≠ 0 ∧ j = 0 then 0 else P1 i j := fun i j => by
    rw [hP2, hent]; split_ifs <;> ring
  have hP2m : P2 ∈ SP := j2.target_mem
  have hb := eq_diag_blk (P := P2) (by rw [f]; simp [e1]) (by rw [f]; simp [e2]) (by rw [f]; simp [e3])
    (by rw [f]; simp) (by rw [f]; simp) (by rw [f]; simp)
  have hNd : 0 < (Matrix.of fun i j : Fin 3 => P2 i.succ j.succ).det := by
    have hd := hP2m.1
    rw [hb, det_mul, det_diagonal, Fin.prod_univ_four, det_blk] at hd
    have ha : 0 < P2 0 0 := hP2m.2.1
    have hd' : 0 < P2 0 0 * (Matrix.of fun i j : Fin 3 => P2 i.succ j.succ).det := by simpa using hd
    exact pos_of_mul_pos_right hd' ha.le
  have j3 := SP_step3 hP2m.2.1 hNd
  rw [← hb] at j3
  exact ((j1.trans j2).trans (j3.trans (SP_joined_blk hNd).symm)).symm

/-! ### Orthochronous Lorentz transformations land in `SO₀` -/

lemma eta00 (P : M4) : (P * ηR * Pᵀ) 0 0 = P 0 0 ^ 2 - P 0 1 ^ 2 - P 0 2 ^ 2 - P 0 3 ^ 2 := by
  rw [GU.Iso77.ηR_eq, ηr]
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal]
  ring

lemma gaugeP_eta : gaugeP ηR = 1 := by
  rw [GU.Iso77.ηR_eq, ηr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeP, c11, c21, c31, c22, c32, c33, m2, m3, schur, Matrix.diagonal, Matrix.one_apply]

lemma eta_symm : (ηR : M4).IsSymm := by
  rw [GU.Iso77.ηR_eq, ηr]
  exact Matrix.isSymm_diagonal _

lemma mem_gaugeSet_of_SP {P : M4} (hP : P ∈ SP) : P * ηR * Pᵀ ∈ gaugeSet := by
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hP.1.ne')
  refine (mem_gaugeSet_iff hu rfl).mpr ?_
  rw [eta00]
  have := hP.2.2
  linarith

lemma symm_conj (P : M4) : (P * ηR * Pᵀ).IsSymm := by
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, eta_symm.eq, Matrix.mul_assoc]

/-- The Lorentz part of a matrix in `SP`. -/
def lorPart (P : M4) : M4 := (gaugeP (P * ηR * Pᵀ))⁻¹ * P

lemma isUnit_gaugeP_SP {P : M4} (hP : P ∈ SP) : IsUnit (gaugeP (P * ηR * Pᵀ)) := by
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hP.1.ne')
  have h := gaugeP_eq (symm_conj P) (mem_gaugeSet_of_SP hP)
  exact isUnit_of_eta_eq hu h

lemma isLorentz_lorPart {P : M4} (hP : P ∈ SP) : IsLorentz (lorPart P) := by
  have h := gaugeP_eq (symm_conj P) (mem_gaugeSet_of_SP hP)
  have hu := isUnit_gaugeP_SP hP
  set A := gaugeP (P * ηR * Pᵀ)
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  unfold IsLorentz lorPart
  rw [transpose_mul, transpose_nonsing_inv]
  calc A⁻¹ * P * ηR * (Pᵀ * Aᵀ⁻¹) = A⁻¹ * (P * ηR * Pᵀ) * Aᵀ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * (A * ηR * Aᵀ) * Aᵀ⁻¹ := by rw [h]
    _ = (A⁻¹ * A) * ηR * (Aᵀ * Aᵀ⁻¹) := by simp only [Matrix.mul_assoc]
    _ = ηR := by
      rw [Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ (by rw [det_transpose]; exact hd)]
      simp

/-- **Orthochronous Lorentz transformations of positive determinant give elements of `SO₀`.** -/
theorem lorO_mem_SO0_pos {Λ : M4} (hL : IsLorentz Λ) (h0 : 0 < Λ 0 0) (hd : 0 < Λ.det) :
    lorO Λ hL ∈ SO0 := by
  have hΛ : Λ ∈ SP := by
    refine ⟨hd, h0, ?_⟩
    have := eta00 Λ
    rw [hL, GU.Iso77.ηR_eq, ηr] at this
    simp [Matrix.diagonal] at this
    nlinarith
  obtain ⟨γ, hγ⟩ := joinedIn_SP hΛ
  have hcG : Continuous fun t => γ t * ηR * (γ t)ᵀ :=
    (γ.continuous.matrix_mul continuous_const).matrix_mul γ.continuous.matrix_transpose
  have hcA : Continuous fun t => gaugeP (γ t * ηR * (γ t)ᵀ) :=
    continuousOn_gaugeP.comp_continuous hcG fun t => mem_gaugeSet_of_SP (hγ t)
  have hcI : Continuous fun t => (gaugeP (γ t * ηR * (γ t)ᵀ))⁻¹ :=
    continuousOn_univ.mp (continuousOn_inv_of_unit (A := Set.univ) hcA.continuousOn
      fun t _ => isUnit_gaugeP_SP (hγ t))
  have hcL : Continuous fun t => lorPart (γ t) := hcI.matrix_mul γ.continuous
  let f : unitInterval → O77 := fun t => lorO (lorPart (γ t)) (isLorentz_lorPart (hγ t))
  have hf : Continuous f :=
    (continuous_lorM hcL fun t => (isLorentz_lorPart (hγ t)).isUnit).subtype_mk _
  have hη : (1 : M4) * ηR * (1 : M4)ᵀ = ηR := by simp
  have f0 : f 0 = 1 := by
    rw [← lorO_one]
    apply Subtype.ext
    show lorM (lorPart (γ 0)) = lorM 1
    rw [γ.source]
    unfold lorPart
    rw [hη, gaugeP_eta, inv_one, Matrix.one_mul]
  have f1 : f 1 = lorO Λ hL := by
    apply Subtype.ext
    show lorM (lorPart (γ 1)) = lorM Λ
    rw [γ.target]
    unfold lorPart
    rw [show Λ * ηR * Λᵀ = ηR from hL, gaugeP_eta, inv_one, Matrix.one_mul]
  have hsub := isPreconnected_univ.image f hf.continuousOn
  have := hsub.subset_connectedComponent (x := (1 : O77)) ⟨0, Set.mem_univ _, f0⟩
    ⟨1, Set.mem_univ _, f1⟩
  exact this

lemma isLorentz_rR : IsLorentz rR := rR_eta

lemma isLorentz_mul {A B : M4} (hA : IsLorentz A) (hB : IsLorentz B) : IsLorentz (A * B) := by
  unfold IsLorentz at *
  rw [transpose_mul]
  calc A * B * ηR * (Bᵀ * Aᵀ) = A * (B * ηR * Bᵀ) * Aᵀ := by simp only [Matrix.mul_assoc]
    _ = ηR := by rw [hB, hA]

lemma det_lorentz {Λ : M4} (h : IsLorentz Λ) : Λ.det = 1 ∨ Λ.det = -1 := by
  have hd := congrArg Matrix.det h
  have he : (ηR : M4).det = -1 := by
    rw [GU.Iso77.ηR_eq]; simp [ηr, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [det_mul, det_mul, det_transpose, he] at hd
  have : (Λ.det - 1) * (Λ.det + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

/-- **Every orthochronous Lorentz transformation gives an element of `SO₀`**, whatever its
determinant. -/
theorem lorO_mem_SO0 {Λ : M4} (hL : IsLorentz Λ) (h0 : 0 < Λ 0 0) : lorO Λ hL ∈ SO0 := by
  rcases det_lorentz hL with hd | hd
  · exact lorO_mem_SO0_pos hL h0 (by rw [hd]; exact one_pos)
  · have hL' : IsLorentz (rR * Λ) := isLorentz_mul isLorentz_rR hL
    have h0' : 0 < (rR * Λ) 0 0 := by
      simpa [rR, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] using h0
    have hd' : 0 < (rR * Λ).det := by
      rw [det_mul, hd]; simp [rR, Matrix.det_diagonal, Fin.prod_univ_four]
    have hpos := lorO_mem_SO0_pos hL' h0' hd'
    have hrr : rR * (rR * Λ) = Λ := by rw [← Matrix.mul_assoc, rR_mul_self, Matrix.one_mul]
    have hm := lorO_mul isLorentz_rR hL' (by rw [hrr]; exact hL)
    have hrefl : lorO rR isLorentz_rR = gRefl := Subtype.ext lorM_rR
    have : lorO Λ hL = lorO rR isLorentz_rR * lorO (rR * Λ) hL' := by
      rw [← hm]
      apply Subtype.ext
      show lorM Λ = lorM (rR * (rR * Λ))
      rw [hrr]
    rw [this, hrefl]
    exact mul_mem gRefl_mem_SO0 hpos

end

end GU.Library
