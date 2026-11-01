/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow0 : ∀ j : Fin 45, (0 : Fin 45) ≠ j → trPair (U 0) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow1 : ∀ j : Fin 45, (1 : Fin 45) ≠ j → trPair (U 1) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow2 : ∀ j : Fin 45, (2 : Fin 45) ≠ j → trPair (U 2) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow3 : ∀ j : Fin 45, (3 : Fin 45) ≠ j → trPair (U 3) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow4 : ∀ j : Fin 45, (4 : Fin 45) ≠ j → trPair (U 4) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow5 : ∀ j : Fin 45, (5 : Fin 45) ≠ j → trPair (U 5) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow6 : ∀ j : Fin 45, (6 : Fin 45) ≠ j → trPair (U 6) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow7 : ∀ j : Fin 45, (7 : Fin 45) ≠ j → trPair (U 7) (U j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Urow8 : ∀ j : Fin 45, (8 : Fin 45) ≠ j → trPair (U 8) (U j) = 0 := by decide +kernel

end GU.Spinor
