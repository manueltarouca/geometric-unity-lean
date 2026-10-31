import GU.Spinor.Centralizer

namespace GU.Spinor

open CSum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem U_gram_diag : ∀ i : Fin 45, trPair (U i) (U i) ≠ 0 := by decide +kernel

end GU.Spinor
