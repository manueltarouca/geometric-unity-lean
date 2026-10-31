import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow0 : ∀ j : Fin 20, (0 : Fin 20) ≠ j → trPair (V 0) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow1 : ∀ j : Fin 20, (1 : Fin 20) ≠ j → trPair (V 1) (V j) = 0 := by decide +kernel

end GU.Spinor
