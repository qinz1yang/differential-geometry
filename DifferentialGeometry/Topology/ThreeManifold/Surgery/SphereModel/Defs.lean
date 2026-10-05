import DifferentialGeometry.Topology.ThreeManifold.OrientedStage
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ClosedOriented.Sum

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def sphereThreePoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

def sphereThreeStage : OrientedThreeStage where
  Carrier := Sphere 3
  orientation :=
    (DifferentialGeometry.sphereOrientation 3 (by decide))

theorem sphereThreeStage_nonempty : Nonempty sphereThreeStage.Carrier := ⟨sphereThreePoint⟩

theorem sphereThreeStage_sum_nonempty : Nonempty (sphereThreeStage.sum sphereThreeStage).Carrier :=
  ⟨Sum.inl ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
