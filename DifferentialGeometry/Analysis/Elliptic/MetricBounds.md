# MetricBounds

## 2026-07-17 metric fibre triangle inequality

`gNorm_add_le` records the triangle inequality for the square root of the
metric quadratic form on a tangent fibre.  Two curvature modules had private
copies of this algebra; the public result belongs beside the existing metric
nonnegativity and Cauchy--Schwarz lemmas and is now reusable by the finite-POU
Sobolev bridge.

Focused verification passed.  The remaining warnings are pre-existing
unused-section-variable warnings on older declarations; the new theorem's
local warning is suppressed because the lower Cauchy--Schwarz API still
carries the ambient finite-module instance.
