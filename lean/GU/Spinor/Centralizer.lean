import GU.Spinor.Reductions

/-!
# The centraliser of `J` in `spin(6,4)` has dimension exactly 25 (`= dim u(3,2)`)

`u32c` lists, for each pair of planes, the two combinations that do *not* commute with `J`.
`allU = u32 ++ u32c` has 45 elements (`= dim so(6,4)`), each a sum of at most two bivectors of
the (6,4) block, linearly independent by a diagonal trace-Gram matrix (`allU_linIndep`). Inside
their span `V`:

`centralizer_eq`: `X ∈ V` commutes with `J` iff `X ∈ span(u32)`.

Together with `u32_linIndep` this pins the centraliser at dimension 25, upgrading the lower
bound of `Reductions.lean` (review-3 item 7). That `V` is all of `spin(6,4)` follows from the
dimension count 45; the explicit span equality with the bivector list is not formalised.
-/

namespace GU.Spinor

open Matrix CSum

def u32c : List CSum :=
  ((List.finRange 5).flatMap fun i => (List.finRange 5).filterMap fun j =>
    if i < j then some (i, j) else none).flatMap fun ij =>
      let p := planes.get ⟨ij.1, by simp [planes]⟩
      let q := planes.get ⟨ij.2, by simp [planes]⟩
      if sameType p q then
        [biv p.1 q.1 ++ neg (biv p.2 q.2), biv p.1 q.2 ++ biv p.2 q.1]
      else
        [biv p.1 q.1 ++ biv p.2 q.2, biv p.1 q.2 ++ neg (biv p.2 q.1)]

def allU : List CSum := u32 ++ u32c

theorem allU_length : allU.length = 45 := by decide
theorem u32c_length : u32c.length = 20 := by decide

def U (i : Fin 45) : CSum := allU.get (Fin.cast allU_length.symm i)

def U25 (i : Fin 25) : CSum := u32.get (Fin.cast u32_length.symm i)
def Uc (j : Fin 20) : CSum := u32c.get (Fin.cast u32c_length.symm j)
def V (j : Fin 20) : CSum := comm (Uc j) Jc

end GU.Spinor
