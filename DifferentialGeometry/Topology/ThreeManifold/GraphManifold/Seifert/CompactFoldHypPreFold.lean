import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypBlend

/-!
# The piecewise hyperbolic fold before the core replacement

Lane CF-H3, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, curvature `-1`). A `HypLayout` collects the
real parameters of the layout: the apex germ radius `g` and the inner radial blend `[a, b]` (in the
pseudo-hyperbolic distances `hd 0`, `hd 1` to `v₁`, `v₂`), the corner shrink `e` (the corner
regions are `canon j < -e`, and `e` is also the scale `δ` of the outer weight `nuThree 1 e`), the
lens half-width `β` and the switch top `β'` (in the lens coordinate, the hyperbolic sine of the
signed distance to the geodesic of wall 2), the outer germ radius `g₃` and the outer radial blend
`[a₃, b₃]` (in `‖z‖`, the pseudo-hyperbolic distance to `v₃ = 0`).

The map `hypPreFold σ L` is, in this order of precedence: the apex model
`3/2 + rotOne^{p₁}/2` on `hd 0 < g`, the apex model `-3/2 + rotTwo^{p₂}/2` on `hd 1 < g`, the outer
germ `compactOuterGerm p₃` on `‖z‖ < g₃`, the corner `cornerOne` on `canon 0 < -e`, the corner
`cornerTwo` on `canon 1 < -e`, the bridge `bridgeTwo` on the lens `|lensCoord| < β`, and the
corner `cornerThree` elsewhere. The concrete parameters (shape dependent, proportional to the
canonical radii) and the layout certificates are in `CompactFoldHypLayout`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

structure HypLayout where
  g : ℝ
  a : ℝ
  b : ℝ
  e : ℝ
  β : ℝ
  β' : ℝ
  g₃ : ℝ
  a₃ : ℝ
  b₃ : ℝ

variable (σ : CompactShape)

def hypPreFold (L : HypLayout) (z : ℂ) : ℂ :=
  if hd σ 0 z < L.g then 3 / 2 + σ.rotOne z ^ σ.p₁ / 2
  else if hd σ 1 z < L.g then -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2
  else if ‖z‖ < L.g₃ then compactOuterGerm σ.p₃ z
  else if canon σ 0 z < -L.e then cornerOne σ L.a L.b L.β L.β' z
  else if canon σ 1 z < -L.e then cornerTwo σ L.a L.b L.β L.β' z
  else if |lensCoord σ z| < L.β then bridgeTwo σ z
  else cornerThree σ L.a₃ L.b₃ 1 L.e z

end HypFold

end GC.Seifert
