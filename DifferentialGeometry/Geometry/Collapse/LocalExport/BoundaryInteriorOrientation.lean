import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

/-!
# LC88 / BCP04: an orientation of the interior carrier in the interior atlas (lane BDRY-5, G18)

The shared regionalised kernel (`exists_regional_chartFamilyEA_BDRY4`) takes an orientation of its
carrier in the model `𝓡 3`. On `W° = W.pieceInterior ⊤` with the interior atlas
(`interiorCharted_BDRY1`), one is obtained from the carrier's orientation `W.orientation`:
restrict it to the open set `W°` (`ManifoldOrientation.restrictOpen`), pass to the smooth
orientation, and pull it back along the identity diffeomorphism from the interior atlas to the
restricted atlas (`interiorAtlasDiffeomorph`).

* `nonempty_interiorOrientation_BDRY5`: `Nonempty (ManifoldOrientation (𝓡 3) W° 3)` for the
  interior atlas (consumer: the binding `exists_interior_chartFamilyEA_BDRY5` of the shared
  regionalised kernel, module `BoundaryRegionalBinding`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

/-- **An orientation of `W°` in the interior atlas** (model `𝓡 3`), from `W.orientation`. -/
theorem nonempty_interiorOrientation_BDRY5 (W : CompactCarrier.{u}) :
    letI := interiorCharted_BDRY1 W
    haveI := interiorManifold_BDRY1 W
    Nonempty (ManifoldOrientation (𝓡 3) (W.pieceInterior ⊤) 3) := by
  let _ := interiorCharted_BDRY1 W
  have _ := interiorManifold_BDRY1 W
  let o₀ : ManifoldOrientation W.model (W.pieceInterior ⊤) 3 :=
    W.orientation.restrictOpen (W.pieceInterior ⊤)
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  let o₁ : ManifoldOrientation W.model (W.pieceInterior ⊤) (Module.finrank ℝ E3) :=
    OrientationAssembly.reindexManifoldOrientation W.model (finCongr hdim.symm) o₀
  let so := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation
    W.model o₁
  let F := (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph W.model ∞
    (M := W.pieceInterior ⊤)).symm
  let so' := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation (𝓡 3) W.model F
    F.contMDiff (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) so
  obtain ⟨O, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) so'
  exact ⟨OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr hdim) O⟩

end DifferentialGeometry.Geometry.Collapse
