# ParabolicRescaling.lean — curvature norm scaling

## 2026-07-09

`paraRmNormSq` is proved.  For the parabolically rescaled solution it identifies
the squared norm of the lowered Riemann tensor with `(R⁻¹)^2` times the original
time-slice squared norm.  The proof composes the checked `rm04` scaling law with
`normSq0S_scale` and `normSq0S_smul` from the tensor layer.

This closes the scaling bridge consumed by the proved Hamilton theorem
`ham3_rm_control`; it does not prove the still-open `ham3_noncollapse` producer.
Focused verification and the targeted module build both passed.

`paraRmNormSq`: **100% checked**.  Whole-HCG accounting remains approximately
**45% machinery** and **0% endpoint theorems**.
