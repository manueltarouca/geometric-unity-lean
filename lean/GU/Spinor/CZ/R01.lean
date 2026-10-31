import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow2 : ∀ j : Fin 20, (2 : Fin 20) ≠ j → trPair (V 2) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow3 : ∀ j : Fin 20, (3 : Fin 20) ≠ j → trPair (V 3) (V j) = 0 := by decide +kernel

end GU.Spinor
