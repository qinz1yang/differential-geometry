# Heat-potential positivity

## State — 2026-07-09

`heat_pot_nonneg` is the conditional positivity consumer for the canonical
`IsHeatPotOn` interface.  A classical solution of
`∂ₜu = Δu + V u` on `[0,T]`, with `V ≤ C` and nonnegative initial data,
remains nonnegative through the terminal endpoint.

The equation in `IsHeatPotOn` is intentionally available only on `(0,T)`.
The proof therefore applies the positive-time strict barrier on every shorter
interval `[0,T']`, `T' < T`, and obtains the value at `T` from `jointCont`.
Spatial and gradient regularity are derived from `sliceSmooth`; no new
regularity assumptions are added.

Focused verification passed without `sorry` or warnings.  This consumer does
not construct a time-dependent heat solution.  The heat-potential existence
theorem and Perelman no-local-collapsing theorem remain 0%; this consumer is a
small part of their dedicated analytic machinery.  Conditional
heat-potential positivity is now 100%; the dedicated conjugate-heat/entropy
machinery is about 20%, while the whole HCG machinery remains about 45% and
its endpoint theorems remain 0%.

## State — 2026-07-16

`heat_pot_pos` strengthens the consumer to strict positivity under the natural
two-sided coefficient bound `|V| ≤ C` and pointwise strictly positive initial
data.  It does not ask the caller for `Nonempty M` or for a uniform positive
lower bound.  The empty-manifold case is vacuous; otherwise compactness and
continuity of the smooth initial slice produce a minimum `c > 0`.

On every shorter interval the proof applies `strict_barrier_posReg` to
`exp (C*t) * u - c`.  The already verified nonnegativity theorem gives
`u ≥ 0`, while `|V| ≤ C` gives `V + C ≥ 0`, so the rescaled field has
nonnegative parabolic operator.  The resulting quantitative estimate
`exp (C*t) * u ≥ c` is retained through the terminal left limit; consequently
closed-endpoint continuity does not weaken strict positivity to mere
nonnegativity.

Focused verification and the targeted module build pass without local
warnings or `sorry`.  `heat_pot_pos` is theorem-level **100%** and the maximum-
principle positivity machinery is **100%**.  The actual Galerkin consumer is
recorded separately in `ConjGalerkinClassical.md`.  Perelman no-local-
collapsing and `ham3_noncollapse` remain theorem-level **0%**; broader
entropy/noncollapse machinery is about **55%**, and whole HCG machinery remains
conservatively about **60%**.
