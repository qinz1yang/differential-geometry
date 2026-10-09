import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCores
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_InteriorX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_InteriorX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialSphereInterior : TopologicalSpace.Opens SphereCarrier.{0} :=
  ⟨{p | cliffordHeight p < 0}, isOpen_lt contMDiff_cliffordHeight.continuous continuous_const⟩

def sphereInteriorToCarrier (p : radialSphereInterior) : carrier.Carrier :=
  ⟨p.val, by
    change cliffordHeight p.val ≤ 0
    exact (show cliffordHeight p.val < 0 from p.property).le⟩

theorem sphereInteriorToCarrier_smooth :
    ContMDiff (𝓡 3) (𝓡∂ 3) ∞ sphereInteriorToCarrier :=
  (solidTorusAtlas.contMDiff_iff_subtype_val sphereInteriorToCarrier).mpr contMDiff_subtype_val

theorem sphereInteriorToCarrier_mfderiv (p : radialSphereInterior) :
    Bijective (mfderiv (𝓡 3) (𝓡∂ 3) sphereInteriorToCarrier p) := by
  have hw : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (sphereInteriorToCarrier p)) :=
    solidTorusAtlas.mfderiv_subtypeVal_bijective (sphereInteriorToCarrier p)
  have hc : Bijective (mfderiv (𝓡 3) (𝓡 3)
      ((Subtype.val : carrier.Carrier → SphereCarrier.{0}) ∘ sphereInteriorToCarrier) p) := by
    change Bijective (mfderiv (𝓡 3) (𝓡 3)
      (Subtype.val : radialSphereInterior → SphereCarrier.{0}) p)
    rw [DifferentialGeometry.mfderiv_subtype_val]
    exact Function.bijective_id
  have hchain := mfderiv_comp p (contMDiff_solidTorus_val.mdifferentiableAt (by simp))
    (sphereInteriorToCarrier_smooth.mdifferentiableAt (by simp))
  have hcomp := hchain ▸ hc
  exact Function.Bijective.of_comp_left
    (f := mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (sphereInteriorToCarrier p))
    (g := mfderiv (𝓡 3) (𝓡∂ 3) sphereInteriorToCarrier p) hcomp hw.1

theorem sphereInteriorToCarrier_interior (p : radialSphereInterior) :
    (𝓡∂ 3).IsInteriorPoint (sphereInteriorToCarrier p) :=
  (solidTorus_isInteriorPoint_iff (sphereInteriorToCarrier p)).mpr
    (show cliffordHeight p.val < 0 from p.property)

theorem sphereInteriorToCarrier_embedding :
    Topology.IsEmbedding sphereInteriorToCarrier := by
  have hv : Topology.IsEmbedding
      ((Subtype.val : carrier.Carrier → SphereCarrier.{0}) ∘ sphereInteriorToCarrier) := by
    change Topology.IsEmbedding (Subtype.val : radialSphereInterior → SphereCarrier.{0})
    exact Topology.IsEmbedding.subtypeVal
  have hw : Topology.IsEmbedding (Subtype.val : carrier.Carrier → SphereCarrier.{0}) :=
    Topology.IsEmbedding.subtypeVal
  exact hw.of_comp_iff.mp hv

theorem sphereInteriorToCarrier_smoothEmbedding :
    IsSmoothEmbedding (𝓡 3) (𝓡∂ 3) ∞ sphereInteriorToCarrier :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    (by simp) sphereInteriorToCarrier_smooth sphereInteriorToCarrier_embedding
    (fun p => (sphereInteriorToCarrier_mfderiv p).injective) sphereInteriorToCarrier_interior

end GC.GraphManifold.Assembly.FC39P0.X135Radial
