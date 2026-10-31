import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow14 : ∀ j : Fin 20, (14 : Fin 20) ≠ j → trPair (V 14) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow15 : ∀ j : Fin 20, (15 : Fin 20) ≠ j → trPair (V 15) (V j) = 0 := by decide +kernel

end GU.Spinor
