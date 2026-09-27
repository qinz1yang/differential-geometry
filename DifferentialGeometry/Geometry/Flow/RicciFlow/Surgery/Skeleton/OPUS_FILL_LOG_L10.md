# OPUS_FILL_LOG_L10 (DESIGN_C3B L10a / L10b)

## 2026-09-26 entry 1 (delivered)

File: `Surgery/Topology/DerivativeBoundExtension.lean` (new, 263 lines, not registered in the
root aggregate). Compiled in place with `LEAN_NUM_THREADS=2 lake env lean
-Dweak.linter.mathlibStandardSet=true`: no output. Scratch `#print axioms` (4 headline decls):
propext, Classical.choice, Quot.sound. Scratch `#lint`: 13 decls, 14 linters, clean. Public names
grep-unique. No sorry, no options besides `autoImplicit false`.

Argument (no uniform continuity needed): with `Q t x := 2q < R(t,x) → |∂ₜ⁺R| ≤ 2C R²`, each
`(t₀, y)` has a neighborhood within `Ici t₀ ×ˢ univ` on which `Q` holds: if `R(t₀,y) > q`, the
slice bound `|∂ₜR(t₀,y)| ≤ C R²` (B1 continuity lemma) gives `|∂ₜR| − 2CR² ≤ −CR² < 0` at
`(t₀,y)` (needs `C > 0`, `q > 0`), an open condition; if `R(t₀,y) ≤ q < 2q`, `R < 2q` nearby.
Tube lemma (`IsCompact.eventually_forall_of_forall_eventually`, carrier compact) gives `η`.
For `t < t₀` the old bound with `C ≤ 2C`, `q < 2q` suffices. Gradient: same with
`|∇R|² ≤ (2C R√R)²`, converted to/from the `∀ v` form by Cauchy–Schwarz and `v = ∇R`.

Hypothesis `0 < C` is necessary (with `C = 0` the conclusion `∂ₜR = 0` does not propagate).

L10b (`t₀ = a`): proved with two explicit slice hypotheses, both genuine and dischargeable:
- regularity: `ContinuousWithinAt (z ↦ derivWithin (R · z.2) (Ici z.1) z.1) (Ici a ×ˢ univ) (a,y)`
  (right derivative jointly continuous up to the slab start; should follow from
  `IncomingSlab.smoothUpTo` (the smooth Gram extension across `a`), not yet proved); for the
  gradient, `ContinuousWithinAt |∇R|²_g (Ici a ×ˢ univ) (a,y)`.
- slice bound at `a`: `q < R(a,y) → |derivWithin (R · y) (Ici a) a| ≤ C R(a,y)²` (right
  derivative), and B1's gradient slice form. To come from the previous slab + event continuity on
  the retained region and the standard-cap evolution on fresh caps.
