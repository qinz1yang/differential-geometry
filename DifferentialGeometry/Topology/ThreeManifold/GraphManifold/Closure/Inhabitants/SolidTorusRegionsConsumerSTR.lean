import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRegionsSTR

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G3 consumer (partial G3)

What a consumer of the regions reads: the ball zero domain with the descending ratio has the same
piece, sublevel and boundary as `ballZeroDomains_STI`; the regions of the cut `D` (with the ball
zero domains `ballZeroDomainsL_STR`, the X135 cusp cores and the empty slim stage) are
`M₂ = M₁ = {u ≤ κ, h ≤ -1/4}`, `M^edge = {u ≤ κ, h ≤ -7/8}`,
`M₃ = {u ≤ κ, -7/8 ≤ h ≤ -1/4}` (`u = Re z₂`, `h` the Clifford height).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- The descending ratio has the same sublevel and zero set as the old ratio. -/
theorem ball_sublevel_STR :
    range (ballZeroDomainsL_STR.piece (0 : Fin 1)).map =
        {p | ballZeroDomainsL_STR.ratio (0 : Fin 1) p ≤ 0} ∧
      pieceBoundary (ballZeroDomainsL_STR.piece (0 : Fin 1)) =
        {p | ballZeroDomainsL_STR.ratio (0 : Fin 1) p = 0} :=
  ⟨ballZeroDomainsL_STR.range_eq (0 : Fin 1), ballZeroDomainsL_STR.boundary_eq (0 : Fin 1)⟩

/-- The regions of the cut in the coordinates `u = Re z₂` and the height `h`. -/
theorem regions_STR :
    (cutChoice_STR ballZeroDomainsL_STR).M₂ = M1set_STR ∧
      (cutChoice_STR ballZeroDomainsL_STR).edgeSet =
        {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)} ∧
      (cutChoice_STR ballZeroDomainsL_STR).M₃ =
        {p | uW_STR p ≤ 4 / 5 ∧ -(7 / 8 : ℝ) ≤ X135Radial.height p ∧
          X135Radial.height p ≤ -(1 / 4 : ℝ)} :=
  ⟨M2_eq_STR, edgeSet_eq_STR, M3_eq_STR⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
