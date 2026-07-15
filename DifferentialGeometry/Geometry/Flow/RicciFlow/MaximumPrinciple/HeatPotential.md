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
