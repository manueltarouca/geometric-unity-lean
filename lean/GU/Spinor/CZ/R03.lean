import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow6 : ∀ j : Fin 20, (6 : Fin 20) ≠ j → trPair (V 6) (V j) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Vrow7 : ∀ j : Fin 20, (7 : Fin 20) ≠ j → trPair (V 7) (V j) = 0 := by decide +kernel

end GU.Spinor
