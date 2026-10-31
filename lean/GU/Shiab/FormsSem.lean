import GU.Shiab.FormsEinsteinAll

/-!
# Track 2, F1 (foundation): semantics of the computable forms layer

`semF A I = Σ_{(J, c) ∈ A, J = I} toMat c` is the 128 × 128 coefficient matrix of the basis form
`e^I` in the list-based `Form` of `FormsWitness.lean`. Lemmas: `semF` is additive under
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

end GU.FormsW
