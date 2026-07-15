# QuadraticFormBound

## 2026-07-12 branch-alignment compatibility

Quadratic homogeneity now applies `map_smul_univ` as an explicit equality and normalizes the two
finite slots with `Fin.prod_univ_two`. Negated quadratic evaluations are exposed with `change`
instead of coercion-sensitive rewrites. Focused verification and targeted build passed; the
quadratic-form bound theorems are complete (100%).
