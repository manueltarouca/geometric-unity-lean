import GU.Shiab.FormsEinsteinAll

/-!
# Track 2, F1 (foundation): semantics of the computable forms layer

`semF A I = Σ_{(J, c) ∈ A, J = I} toMat c` is the 128 × 128 coefficient matrix of the basis form
`e^I` in the list-based `Form` of `FormsWitness.lean`. It compares raw index lists, so `semF`-equality
is form equality only for canonical forms (`Canon`: sorted index lists); every theorem here is
stated for canonical forms. Lemmas: `semF` is additive under
`++` (`semF_append`) and turns `flatMap` into sums (`semF_flatMap`). On canonical forms (all index
lists in `allIdx`), sums over the entries of `A` regroup into sums over the 16 index sets
(`sum_regroup`). These are the tools for proving that `twoShiab` is linear in semantics, which
extends `einstein_all` from the 55 spanning tensors to their span (Track 2 in
`MULTISESSION_PLAN.md`).
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

/-- Coefficient matrix of `e^I` in `A`. -/
noncomputable def semF (A : Form) (I : Idx4) : M128 :=
  (A.map fun x => if x.1 = I then CSum.toMat x.2 else 0).sum

@[simp] lemma semF_nil (I : Idx4) : semF [] I = 0 := rfl

@[simp] lemma semF_cons (x : Idx4 × CSum) (A : Form) (I : Idx4) :
    semF (x :: A) I = (if x.1 = I then CSum.toMat x.2 else 0) + semF A I := by
  simp [semF]

@[simp] lemma semF_append (A B : Form) (I : Idx4) : semF (A ++ B) I = semF A I + semF B I := by
  simp [semF]

lemma semF_flatMap {α : Type*} (L : List α) (g : α → Form) (I : Idx4) :
    semF (L.flatMap g) I = (L.map fun a => semF (g a) I).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The semantic coefficient read off by `coefAt`. -/
lemma toMat_coefAt (A : Form) (I : Idx4) : CSum.toMat (coefAt A I) = semF A I := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [coefAt, List.filter_cons, semF_cons] at ih ⊢
    by_cases h : x.1 = I
    · simp [h, List.flatMap_cons, toMat_append, ← ih, coefAt]
    · simp [h, ← ih, coefAt]

/-- **A passing `formEq` check is a semantic equality on all 16 index sets.** -/
lemma semF_of_formEq {A B : Form} (h : formEq A B = true) : ∀ I ∈ allIdx, semF A I = semF B I := by
  intro I hI
  have := (List.all_eq_true.mp h) I hI
  rw [← toMat_coefAt, ← toMat_coefAt]
  exact toMat_eq_of this

/-- Canonical forms: every index list is one of the 16 sorted ones. -/
def Canon (A : Form) : Prop := ∀ x ∈ A, x.1 ∈ allIdx

lemma allIdx_nodup : allIdx.Nodup := by decide

/-- **Regrouping**: for `g` additive in its second argument, a sum over the entries of a canonical
form is a sum over the 16 index sets. -/
lemma sum_regroup (g : Idx4 → M128 →+ M128) (A : Form) (hA : Canon A) :
    (A.map fun y => g y.1 (CSum.toMat y.2)).sum = (allIdx.map fun I => g I (semF A I)).sum := by
  induction A with
  | nil => simp
  | cons y A ih =>
    have hy : y.1 ∈ allIdx := hA y (List.mem_cons_self ..)
    have ih' := ih fun x hx => hA x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.sum_cons, semF_cons, map_add, ih']
    rw [List.sum_map_add]
    congr 1
    -- only `I = y.1` contributes
    have e : ∀ I, g I (if y.1 = I then CSum.toMat y.2 else 0) =
        if y.1 = I then g y.1 (CSum.toMat y.2) else 0 := fun I => by
      split_ifs with h
      · rw [h]
      · exact map_zero _
    simp only [e]
    rw [← List.sum_toFinset _ allIdx_nodup, Finset.sum_ite_eq]
    simp [hy]

/-! ### CSum-level semantics and canonicity -/

lemma toMat_smul (c : ℤ) (L : CSum) : CSum.toMat (smul c L) = (c : ℝ) • CSum.toMat L := by
  induction L with
  | nil => simp [smul]
  | cons p L ih =>
    rw [smul, List.map_cons, toMat_cons, ← smul, ih, toMat_cons, smul_add]
    congr 1
    simp [PString.toMat, mul_smul, Int.cast_mul]

lemma toMat_flatMap {α : Type*} (L : List α) (g : α → CSum) :
    CSum.toMat (L.flatMap g) = (L.map fun a => CSum.toMat (g a)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_cons, ih]

lemma toMat_acm (x y : CSum) : CSum.toMat (acm x y) = CSum.toMat x * CSum.toMat y + CSum.toMat y * CSum.toMat x := by
  simp [acm, toMat_mul]

lemma toMat_cm (x y : CSum) : CSum.toMat (cm x y) = CSum.toMat x * CSum.toMat y - CSum.toMat y * CSum.toMat x :=
  toMat_comm x y

theorem filter_mem_allIdx (p : Fin 4 → Bool) : (List.finRange 4).filter p ∈ allIdx := by
  revert p; decide

lemma sortIdx_mem (I : Idx4) : sortIdx I ∈ allIdx := filter_mem_allIdx _
lemma compl_mem (I : Idx4) : compl I ∈ allIdx := filter_mem_allIdx _

lemma canon_star (A : Form) : Canon (star A) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact compl_mem _

lemma canon_wedge (br : CSum → CSum → CSum) (A B : Form) : Canon (wedge br A B) := by
  intro x hx
  simp only [wedge, List.mem_flatMap, List.mem_filterMap] at hx
  obtain ⟨a, -, b, -, hb⟩ := hx
  split_ifs at hb with hs
  simp only [Option.some.injEq] at hb; rw [← hb]; exact sortIdx_mem _

lemma canon_append {A B : Form} (hA : Canon A) (hB : Canon B) : Canon (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

lemma canon_map_snd (A : Form) (f : CSum → CSum) (hA : Canon A) : Canon (A.map fun x => (x.1, f x.2)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hA y hy

lemma canon_twoShiab (ξ : Form) : Canon (twoShiab ξ) :=
  canon_append (canon_map_snd _ _ (canon_wedge _ _ _)) (canon_map_snd _ _ (canon_star _))

/-- Canonical forms vanish semantically off the 16 index sets. -/
lemma semF_zero_off {A : Form} (hA : Canon A) {I : Idx4} (hI : I ∉ allIdx) : semF A I = 0 := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    rw [semF_cons, ih fun y hy => hA y (List.mem_cons_of_mem _ hy)]
    have : x.1 ≠ I := fun h => hI (h ▸ hA x (List.mem_cons_self ..))
    simp [this]

/-- `semF` of a coefficientwise map by a semantically linear operation. -/
lemma semF_map_snd (A : Form) (f : CSum → CSum) (F : M128 →+ M128)
    (hf : ∀ c, CSum.toMat (f c) = F (CSum.toMat c)) (I : Idx4) :
    semF (A.map fun x => (x.1, f x.2)) I = F (semF A I) := by
  induction A with
  | nil => simp
  | cons x A ih =>
    simp only [List.map_cons, semF_cons, ih, map_add, hf]
    split_ifs <;> simp

end GU.FormsW
