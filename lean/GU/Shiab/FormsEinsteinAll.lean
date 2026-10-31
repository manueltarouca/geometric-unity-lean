import GU.Shiab.FE.P00
import GU.Shiab.FE.P01
import GU.Shiab.FE.P02
import GU.Shiab.FE.P03
import GU.Shiab.FE.P04
import GU.Shiab.FE.P05
import GU.Shiab.FE.P06
import GU.Shiab.FE.P07
import GU.Shiab.FE.P08
import GU.Shiab.FE.P09
import GU.Shiab.FE.P10
import GU.Shiab.FE.P11
import GU.Shiab.FE.P12
import GU.Shiab.FE.P13
import GU.Shiab.FE.P14
import GU.Shiab.FE.P15
import GU.Shiab.FE.P16
import GU.Shiab.FE.P17
import GU.Shiab.FE.P18

/-!
# Printed (9.3) with Hodge stars outputs the Einstein form on all 55 spanning tensors (n = 4)

Assembled from the per-case theorems in `GU/Shiab/FE/` (each a `decide +kernel` check, compiled
one file at a time to stay within memory).
-/

namespace GU.FormsW

def cases55 : List ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) := [((0, 0), (0, 0)), ((0, 0), (0, 1)), ((0, 0), (0, 2)), ((0, 0), (0, 3)), ((0, 0), (1, 1)), ((0, 0), (1, 2)), ((0, 0), (1, 3)), ((0, 0), (2, 2)), ((0, 0), (2, 3)), ((0, 0), (3, 3)), ((0, 1), (0, 1)), ((0, 1), (0, 2)), ((0, 1), (0, 3)), ((0, 1), (1, 1)), ((0, 1), (1, 2)), ((0, 1), (1, 3)), ((0, 1), (2, 2)), ((0, 1), (2, 3)), ((0, 1), (3, 3)), ((0, 2), (0, 2)), ((0, 2), (0, 3)), ((0, 2), (1, 1)), ((0, 2), (1, 2)), ((0, 2), (1, 3)), ((0, 2), (2, 2)), ((0, 2), (2, 3)), ((0, 2), (3, 3)), ((0, 3), (0, 3)), ((0, 3), (1, 1)), ((0, 3), (1, 2)), ((0, 3), (1, 3)), ((0, 3), (2, 2)), ((0, 3), (2, 3)), ((0, 3), (3, 3)), ((1, 1), (1, 1)), ((1, 1), (1, 2)), ((1, 1), (1, 3)), ((1, 1), (2, 2)), ((1, 1), (2, 3)), ((1, 1), (3, 3)), ((1, 2), (1, 2)), ((1, 2), (1, 3)), ((1, 2), (2, 2)), ((1, 2), (2, 3)), ((1, 2), (3, 3)), ((1, 3), (1, 3)), ((1, 3), (2, 2)), ((1, 3), (2, 3)), ((1, 3), (3, 3)), ((2, 2), (2, 2)), ((2, 2), (2, 3)), ((2, 2), (3, 3)), ((2, 3), (2, 3)), ((2, 3), (3, 3)), ((3, 3), (3, 3))]

theorem knPairs_eq : knPairs = cases55 := by decide

set_option maxHeartbeats 0 in
theorem einstein_all : ∀ pq ∈ knPairs, checkKN pq.1 pq.2 = true := by
  rw [knPairs_eq]
  intro pq hpq
  simp only [cases55, List.mem_cons, List.not_mem_nil, or_false] at hpq
  repeat' (rcases hpq with rfl | hpq)
  exacts [ein_00_00, ein_00_01, ein_00_02, ein_00_03, ein_00_11, ein_00_12, ein_00_13, ein_00_22, ein_00_23, ein_00_33, ein_01_01, ein_01_02, ein_01_03, ein_01_11, ein_01_12, ein_01_13, ein_01_22, ein_01_23, ein_01_33, ein_02_02, ein_02_03, ein_02_11, ein_02_12, ein_02_13, ein_02_22, ein_02_23, ein_02_33, ein_03_03, ein_03_11, ein_03_12, ein_03_13, ein_03_22, ein_03_23, ein_03_33, ein_11_11, ein_11_12, ein_11_13, ein_11_22, ein_11_23, ein_11_33, ein_12_12, ein_12_13, ein_12_22, ein_12_23, ein_12_33, ein_13_13, ein_13_22, ein_13_23, ein_13_33, ein_22_22, ein_22_23, ein_22_33, ein_23_23, ein_23_33, ein_33_33]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Non-vacuity: the Einstein form of `E₀₀ ⊙ E₁₁` is nonzero. -/
theorem einstein_nonzero : formEq (einsteinForm (kn (esym 0 0) (esym 1 1))) [] = false := by
  decide +kernel

end GU.FormsW
