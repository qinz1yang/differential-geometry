import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusBallSTI

/-!
# S-SOLIDTORUS (suffix `_STI`), G1a consumer

The ball zero domains of the solid torus instance against the X135 cusp cores: the
`zero_cusp_disjoint` field of `JunctionsV2` for `Z = ballZeroDomains_STI`,
`C = X135Radial.radialCuspCores`, and the ratio / count data a consumer reads.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI

theorem ballZeroDomains_count_STI : ballZeroDomains_STI.count = 1 := rfl

/-- The `zero_cusp_disjoint` field of the junctions for the ball zero domains and the X135 cusp
cores. -/
theorem ball_zero_cusp_disjoint_STI :
    ∀ (i : Fin ballZeroDomains_STI.count) (b : Fin 1),
      Disjoint (range (ballZeroDomains_STI.piece i).map)
        (range (X135Radial.radialCuspCores.piece b).map) := by
  intro i b
  have hb : b = 0 := Subsingleton.elim b 0
  subst hb
  exact ball_cusp_disjoint_STI

/-- The ball is the global sublevel `{ratio ≤ 0}` and its model boundary the zero set. -/
theorem ball_sublevel_STI :
    range (ballZeroDomains_STI.piece (0 : Fin 1)).map =
        {p | ballZeroDomains_STI.ratio (0 : Fin 1) p ≤ 0} ∧
      pieceBoundary (ballZeroDomains_STI.piece (0 : Fin 1)) =
        {p | ballZeroDomains_STI.ratio (0 : Fin 1) p = 0} :=
  ⟨ballZeroDomains_STI.range_eq (0 : Fin 1), ballZeroDomains_STI.boundary_eq (0 : Fin 1)⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI
