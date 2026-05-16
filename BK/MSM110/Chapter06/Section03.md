# MSM110 Chapter 6.3

## 2026-05-13 curvature-operator structure scaffold

The Section 6.3 companion imports
`RicciFlower.RicciFlow.Evolution.CurvatureOperator` and exposes thin
book-label wrappers for:

- `eq:inner_product_for_wedge_two`
- curvature-operator self-adjointness
- `eq:define_square_of_riemann`
- `eq:define_lie_square`
- Lie-square nonnegativity
- `eq:lie_bracket_for_wedge_two`
- `item:lie_square_of_riemann`
- `thm:uhlenbeck_curvature_evolution_two`
- `cor:pc_opreserved`

The companion is label-facing only.  The intentional `sorry` frontiers live in
the RicciFlower curvature-operator module.

Verification: focused file check passed and targeted Section 6.3 module build
passed.  The aggregate Chapter 6 build is currently blocked by an unrelated
current failure in `RicciFlower/Curvature/Components.lean`, where the proof near
lines 1220 and 1227 leaves coordinate-input equality goals unsolved.
