import GU.Shiab.FormsSemOps

/-!
# Track 2, F1 step 3: Einstein output on the whole ℤ-span of the 55 KN tensors

`twoShiabS` is additive (`twoShiabS_add`). `semF (curvForm R)` and `semF (einsteinForm R)` are additive
in `R` (`curvH`, `einH`). Together with the 55 checked cases (`einstein_all`), this gives
**`einstein_span`**: for every integer combination `R = Σ c_p KN_p` of the Kulkarni–Nomizu tensors,
the doubled printed Shiab of the curvature form equals `−4 ⋆(Einstein form)` semantically, on every
index set.
-/

namespace GU.FormsW

open GU.Spinor GU.Spinor.CSum

abbrev Tens := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ

lemma starS_add (f g : Idx4 → M128) (J : Idx4) : starS (f + g) J = starS f J + starS g J := by
  simp only [starS, ← List.sum_map_add]
  congr 1; refine List.map_congr_left fun I _ => ?_
  split_ifs <;> simp [smul_add]

lemma wedgeS_add {BR : M128 → M128 → M128} (hBR : BiAdd BR) (F g h : Idx4 → M128) (K : Idx4) :
    wedgeS BR F (g + h) K = wedgeS BR F g K + wedgeS BR F h K := by
  simp only [wedgeS, ← List.sum_map_add]
  congr 1; refine List.map_congr_left fun I _ => ?_
  congr 1; refine List.map_congr_left fun J _ => ?_
  split_ifs <;> simp [hBR.add_right, smul_add]

lemma starS_add' (f g : Idx4 → M128) : starS (f + g) = starS f + starS g := funext (starS_add f g)

lemma wedgeS_add' {BR : M128 → M128 → M128} (hBR : BiAdd BR) (F g h : Idx4 → M128) :
    wedgeS BR F (g + h) = wedgeS BR F g + wedgeS BR F h := funext (wedgeS_add hBR F g h)

lemma twoShiabS_add (f g : Idx4 → M128) : twoShiabS (f + g) = twoShiabS f + twoShiabS g := by
  funext K
  simp only [twoShiabS, starS_add', wedgeS_add' biAdd_ACR, wedgeS_add' biAdd_CMR, Pi.add_apply,
    smul_add]
  abel

/-- `twoShiabS` as an additive map. -/
noncomputable def twoShiabH : (Idx4 → M128) →+ (Idx4 → M128) :=
  AddMonoidHom.mk' twoShiabS twoShiabS_add

/-- `R ↦ semF (curvForm R)` is additive. -/
noncomputable def curvH : Tens →+ (Idx4 → M128) :=
  AddMonoidHom.mk' (fun R => semF (curvForm R)) fun R R' => by
    funext I
    simp only [curvForm, semF, List.map_map, Function.comp_def, Pi.add_apply, ← List.sum_map_add]
    congr 1; refine List.map_congr_left fun ab _ => ?_
    split_ifs
    · simp only [toMat_flatMap, toMat_smul, ← List.sum_map_add, Int.cast_add, add_smul]
    · simp

lemma ric_add (R R' : Tens) (b d : Fin 4) : ric (R + R') b d = ric R b d + ric R' b d := by
  simp [ric, List.sum_map_add]

lemma scal_add (R R' : Tens) : scal (R + R') = scal R + scal R' := by
  simp [scal, ric_add, List.sum_map_add]

/-- `R ↦ semF (einsteinForm R)` is additive. -/
noncomputable def einH : Tens →+ (Idx4 → M128) :=
  AddMonoidHom.mk' (fun R => semF (einsteinForm R)) fun R R' => by
    funext I
    simp only [einsteinForm, star, semF, List.map_map, Function.comp_def, Pi.add_apply,
      ← List.sum_map_add]
    congr 1; refine List.map_congr_left fun a _ => ?_
    split_ifs
    · simp only [toMat_smul, toMat_flatMap, ← List.sum_map_add, ← smul_add]
      congr 1; congr 1; refine List.map_congr_left fun b _ => ?_
      rw [← add_smul]; congr 1
      simp only [ric_add, scal_add]; push_cast
      split_ifs <;> ring
    · simp

lemma pairs_mem : ∀ ab ∈ pairs, [ab.1, ab.2] ∈ allIdx := by decide

lemma canon_curvForm (R : Tens) : Canon (curvForm R) := by
  intro x hx
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hx
  exact pairs_mem ab hab

lemma canon_einsteinForm (R : Tens) : Canon (einsteinForm R) := canon_star _

/-- The Kulkarni–Nomizu tensor of a pair of symmetric generators. -/
def knT (p : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) : Tens := kn (esym p.1.1 p.1.2) (esym p.2.1 p.2.2)

lemma basis_eq (p : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) (hp : p ∈ knPairs) :
    semF (twoShiab (curvForm (knT p))) = semF (einsteinForm (knT p)) := by
  funext I
  by_cases hI : I ∈ allIdx
  · exact semF_of_formEq (einstein_all p hp) I hI
  · rw [semF_zero_off (canon_twoShiab _) hI, semF_zero_off (canon_einsteinForm _) hI]

/-- **Einstein output on the ℤ-span of the 55 Kulkarni–Nomizu tensors**: for every integer
combination `R = Σ c_p KN_p`, `twoShiab (curvForm R)` and `einsteinForm R` have the same
coefficient matrix on every index set. -/
theorem einstein_span (c : (Fin 4 × Fin 4) × (Fin 4 × Fin 4) → ℤ) (I : Idx4) :
    semF (twoShiab (curvForm ((knPairs.map fun p => c p • knT p).sum))) I =
      semF (einsteinForm ((knPairs.map fun p => c p • knT p).sum)) I := by
  have hL : ∀ R : Tens, semF (twoShiab (curvForm R)) = twoShiabH (curvH R) := fun R =>
    funext (semF_twoShiab (canon_curvForm R))
  have hbasis : ∀ p ∈ knPairs, twoShiabH (curvH (knT p)) = einH (knT p) := fun p hp => by
    rw [← hL]; exact basis_eq p hp
  have key : twoShiabH (curvH ((knPairs.map fun p => c p • knT p).sum)) =
      einH ((knPairs.map fun p => c p • knT p).sum) := by
    rw [map_list_sum, map_list_sum, map_list_sum, List.map_map, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply, map_zsmul, hbasis p hp]
  rw [hL]
  exact congrFun key I

end GU.FormsW
