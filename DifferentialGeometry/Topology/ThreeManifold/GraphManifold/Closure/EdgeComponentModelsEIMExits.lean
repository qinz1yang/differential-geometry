import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# The edge component registry of the ACTUAL edge bundle of the rows (lane S-EDGE-INT2)

Draft 74 exits: `EDP04WholeDiskExitU74.models` and `StageCutRows74.edgeModels` ask for an
`EdgeComponentModels (edgeBundle74 A D F)` on the actual restriction of the stage's edge map to the
good open edge base. `edgeBundle74_models_EIM` produces it from the cut-dependent edge facts
`F : EdgeCutFacts74 A D` alone (every `EdgeBundle` has one, `exists_edgeComponentModels_EIM`);
use `Classical.choice` for the structure field.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **The edge models of the actual edge bundle of the rows.** -/
theorem edgeBundle74_models_EIM (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : EdgeCutFacts74 A D) : Nonempty (EdgeComponentModels (edgeBundle74 A D F)) :=
  (edgeBundle74 A D F).exists_edgeComponentModels_EIM

end GC.GraphManifold.Assembly.FC39P0
