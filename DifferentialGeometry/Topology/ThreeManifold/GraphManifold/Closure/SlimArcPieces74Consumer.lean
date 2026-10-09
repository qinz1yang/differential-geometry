import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimArcPieces74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74Consumer

/-!
# Draft 74, S0: consumer on the S³ slim shell (real inhabitant)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G29 (consumer). The `S² × [0, 1]` slim map of the S³
inhabitant (`slimMap`, the shell `1/2 ≤ r ≤ 1`, `FC39P0SphereSlim`) carried along the identity
carrier diffeomorphism `sphereId74` by `sphereArcPiece74`: the slim piece has the range of the
height band `−15/17 ≤ q₀ ≤ −3/5` and the two end slices are the height levels `q₀ = −15/17`,
`q₀ = −3/5` — the data the kernel `…exists_slimPiece_sphere74` reads off a whole interval product.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open GC.GraphManifold.Assembly.FC39P0 (slimModelEnd)
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The S³ slim shell carried along the identity: the slim piece of `sphereArcPiece74`. -/
def sphereSlimArcPiece74 : PieceEmbedding FC39P0.sphereW :=
  sphereArcPiece74 FC39P0.sphereId74 FC39P0.slimMap FC39P0.contMDiff_slimMap
    (fun z => (FC39P0.mfderiv_slimMap_bijective z).1) FC39P0.slimMap_injective

/-- Its slim model. -/
def sphereSlimArcModel74 : SlimModel sphereSlimArcPiece74 :=
  sphereArcModel74 FC39P0.sphereId74 FC39P0.slimMap FC39P0.contMDiff_slimMap
    (fun z => (FC39P0.mfderiv_slimMap_bijective z).1) FC39P0.slimMap_injective

/-- Its range is the height band `−15/17 ≤ q₀ ≤ −3/5`. -/
theorem range_sphereSlimArcPiece74 :
    range sphereSlimArcPiece74.map =
      {x | -15 / 17 ≤ FC39P0.sphereHeight x ∧ FC39P0.sphereHeight x ≤ -3 / 5} := by
  rw [← FC39P0.range_slimMap]
  exact (range_sphereArcPiece74 FC39P0.sphereId74 FC39P0.slimMap FC39P0.contMDiff_slimMap
    (fun z => (FC39P0.mfderiv_slimMap_bijective z).1) FC39P0.slimMap_injective).trans
    (Set.image_id' _)

/-- Its end slices are the height levels `q₀ = −15/17` (end `0`) and `q₀ = −3/5` (end `1`). -/
theorem image_end_sphereSlimArcModel74 (b : Bool) :
    sphereSlimArcPiece74.map '' slimModelEnd sphereSlimArcModel74 b =
      {x | FC39P0.sphereHeight x = FC39P0.slimEndHeight b} := by
  rw [← FC39P0.range_slimMap_end b]
  exact (image_end_sphereArcModel74 FC39P0.sphereId74 FC39P0.slimMap FC39P0.contMDiff_slimMap
    (fun z => (FC39P0.mfderiv_slimMap_bijective z).1) FC39P0.slimMap_injective b).trans
    (Set.image_id' _)

end GC.GraphManifold.Assembly
