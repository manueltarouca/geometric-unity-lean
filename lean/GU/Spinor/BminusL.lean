import GU.Spinor.Hypercharge

/-!
# The extra `U(1)` is `B − L`

On the 16 odd-chirality weights, `X = s₀+s₁+s₂` (the `J₊` charge) equals `−3(B−L)` state by state,
with `B−L = 1/3` for `Q`, `−1/3` for `u^c, d^c`, `−1` for `L`, `+1` for `e^c, ν^c`.
`bminusL_table`: the multiset of pairs `(12Y, 3(B−L))` is exactly the SM one. So the contingent
`Z′` of `synthetic_predictions` is the gauge boson of `U(1)_{B−L}`.
-/

namespace GU.Spinor

def threeBL (s : Fin 5 → Bool) : ℤ := -(sgn (s 0) + sgn (s 1) + sgn (s 2))

theorem bminusL_table :
    (oddWeights.map fun s => (twelveY s, threeBL s)).Perm
      [(2, 1), (2, 1), (2, 1), (2, 1), (2, 1), (2, 1),
       (-8, -1), (-8, -1), (-8, -1), (4, -1), (4, -1), (4, -1),
       (-6, -3), (-6, -3), (12, 3), (0, 3)] := by decide

end GU.Spinor
