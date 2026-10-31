import GU.Bundle.SmoothFrames

/-!
# The smooth frame bundle and the chimeric bundle `Cb`: agreement of transition data

`SmoothFrames.lean` built `frameCore` from the cocycle `gX` directly. Here its transition data are
compared with the bundle `Cb = π*Sym²(TX) ×ᵇ π*T*X` of `ChimericBundle.lean` (Mathlib's
pullback/product/hom machinery):

* `Cb_triv_apply`: `Cb`'s trivialisation at `y`, applied to a raw fibre element over `z`, is
  `gX (chart at π z) (chart at π y)`. The `Sym²` component holds by definition (`symCore` is built
  from `symAct`); the `T*X` component is a genuine comparison with Mathlib's hom-bundle
  trivialisation of `TangentSpace →L ℝ` (`TangentBundle.symmL_trivializationAt_eq_core`).
* **`Cb_coordChange`**: the coordinate changes of `Cb` between `trivializationAt y` and
  `trivializationAt y'` are exactly `gX (chart π y) (chart π y')`. So `Cb` and `frameCore`'s
  underlying bundle have the same transition cocycle.
* `Cb_baseSet`: the base sets agree with `frameCore`'s.
* `frameCore_localTriv_eq`: fibrewise, `frameCore.localTriv (chart π y)` is post-composition with
  `Cb`'s trivialisation at `y`.

What this is NOT: a bundle isomorphism or an equality of total-space topologies with Mathlib's hom
bundle `Trivial Y ℝ¹⁴ →L Cb`. That bundle is awkward to instantiate here (pullback fibres lack the
`AddCommGroup`/topological-group instances, and `Trivial Y CFib` hits a product-bundle instance
diamond because `CFib` is a product type). Only the `trivializationAt` family is compared, and
"`FrY` = isomorphisms `ℝ¹⁴ ≅ Cb_z`" holds by definitional unfolding (`Cb z ≡ CFib`).
-/

namespace GU.Observerse

open Bundle Manifold
open scoped ContDiff

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Fin 4 → ℝ) X]
  [IsManifold (modelWithCornersSelf ℝ (Fin 4 → ℝ)) ∞ X]

/-- **`Cb`'s trivialisations realise the cocycle `gX`.** -/
theorem Cb_triv_apply (y z : Yobs X) (v : CFib)
    (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) :
    ((trivializationAt CFib (Cb (X := X)) y) ⟨z, v⟩).2 =
      gX (achart (Fin 4 → ℝ) (πY z)) (achart (Fin 4 → ℝ) (πY y)) (πY z) v := by
  refine Prod.ext ?_ ?_
  · rfl
  · have hb : πY z ∈ (chartAt (Fin 4 → ℝ) (πY y)).source := hz.1
    have key : ((trivializationAt CFib (Cb (X := X)) y) ⟨z, v⟩).2.2 =
        (Trivialization.continuousLinearMapAt ℝ (trivializationAt ℝ (fun _ : X => ℝ) (πY y)) (πY z)).comp
          ((v.2).comp ((trivializationAt (Fin 4 → ℝ)
            (TangentSpace (modelWithCornersSelf ℝ (Fin 4 → ℝ))) (πY y)).symmL ℝ (πY z))) := rfl
    rw [key, TangentBundle.symmL_trivializationAt_eq_core hb]
    ext w
    simp [gX, covT]

/-- Fibrewise, `frameCore`'s trivialisation at the chart of `π y` is post-composition with `Cb`'s
trivialisation at `y`. -/
theorem frameCore_localTriv_eq (y : Yobs X) (p : HomTot X)
    (hp : p.proj ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet) (w : CFib) :
    (((frameCore (X := X)).localTriv (achart (Fin 4 → ℝ) (πY y)) p).2 : EndC) w =
      ((trivializationAt CFib (Cb (X := X)) y) ⟨p.proj, (show EndC from p.2) w⟩).2 := by
  rw [Cb_triv_apply y p.proj _ hp, VectorBundleCore.localTriv_apply]
  rfl

lemma Cb_baseSet (y : Yobs X) :
    (trivializationAt CFib (Cb (X := X)) y).baseSet =
      ((frameCore (X := X)).localTriv (achart (Fin 4 → ℝ) (πY y))).baseSet :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, h, Set.mem_univ _⟩⟩

/-- **`Cb` has transition cocycle `gX`.** -/
theorem Cb_coordChange (y y' z : Yobs X)
    (hz : z ∈ (trivializationAt CFib (Cb (X := X)) y).baseSet ∩
      (trivializationAt CFib (Cb (X := X)) y').baseSet) (v : CFib) :
    Trivialization.coordChangeL ℝ (trivializationAt CFib (Cb (X := X)) y)
        (trivializationAt CFib (Cb (X := X)) y') z v =
      gX (achart (Fin 4 → ℝ) (πY y)) (achart (Fin 4 → ℝ) (πY y')) (πY z) v := by
  set e := trivializationAt CFib (Cb (X := X)) y
  rw [Trivialization.coordChangeL_apply _ _ hz]
  set u : CFib := e.symm z v
  refine (Cb_triv_apply y' z u hz.2).trans ?_
  have hu : gX (achart (Fin 4 → ℝ) (πY z)) (achart (Fin 4 → ℝ) (πY y)) (πY z) u = v := by
    exact (Cb_triv_apply y z u hz.1).symm.trans (congrArg Prod.snd (e.apply_mk_symm hz.1 v))
  have hzz : πY z ∈ (Zt X).baseSet (achart (Fin 4 → ℝ) (πY z)) := (Zt X).mem_baseSet_at _
  have hy : πY z ∈ (Zt X).baseSet (achart (Fin 4 → ℝ) (πY y)) := hz.1.1
  have hy' : πY z ∈ (Zt X).baseSet (achart (Fin 4 → ℝ) (πY y')) := hz.2.1
  rw [← hu, gX_comp _ _ _ _ ⟨⟨hzz, hy⟩, hy'⟩]

end GU.Observerse
