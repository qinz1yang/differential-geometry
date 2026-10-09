import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStage74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLoopInhabitant74

/-!
# Non-vacuous consumer of the stage-link bridge (`RowsLinkOfStage74`)

Lane S-LANDING (`_LND74`), G2c. On the `S² × S¹` loop of the abstract assembler (lane
S-JUNCTIONS, `FC39StageLoopInhabitant74`: ONE slim component, `K₃ = D₃ = S¹`, whole slim piece),
with the identification `ψ = id`, `ι = id`, `q = f₃`: the assembled rows (J1,
`rowsOfStageGeometry74`) satisfy the plain-data slim table `SlimLink_LND74` obtained from
`StageRowsLink74` through the bridge lemma `slimLink_of_stage_LND74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- The slim stage map of the loop on the carrier. -/
def slimLoopQ_LND74 (x : slimWc.Carrier) : Circle := slimLoopProj74 ⟨x, trivial⟩

/-- **Bridge consumer (slim, NON-empty)**: the J1 rows of the `S² × S¹` loop satisfy the slim table
of `RowsLinkKernel74`: ONE slim piece, the whole `f₃`-preimage of the single component of `D₃`. -/
theorem slimLoop_slimLink_LND74 :
    SlimLink_LND74 (Equiv.refl slimWc.Carrier)
      (rowsOfStageGeometry74 slimLoopStageGeometry74 slimLoopCutChoice74
        slimLoopCutGeometry74).slim
      (fun c : ActualComponent slimLoopCutChoice74.D₃ => slimLoopQ_LND74 ⁻¹' c.1)
      (slimLoopQ_LND74 ⁻¹' slimLoopCutChoice74.D₃) := by
  have hid : StageIdent_LND74 (Equiv.refl slimWc.Carrier)
      slimLoopStageGeometry74.slim.toStageProj74 slimLoopQ_LND74
      (id : slimLoopStageGeometry74.slim.Base → Circle) :=
    ⟨Topology.IsEmbedding.id, fun x => rfl, fun p _ => trivial⟩
  exact slimLink_of_stage_LND74
    (rowsOfStageGeometry74_link slimLoopStageGeometry74 slimLoopCutChoice74
      slimLoopCutGeometry74).zeroSlim hid (D₃c := slimLoopCutChoice74.D₃) (image_id _)
    (Equiv.refl _) (fun c => image_id _)

end GC.GraphManifold.Assembly.FC39P0.X136
