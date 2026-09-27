import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
  {U : TopologicalSpace.Opens M}

def SpatialNeck.ofRestrictOpen {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z) :
    SpatialNeck g eps z.val :=
  nk.pushforward (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I3 U ⟨z⟩)
    (fun y _ v w => by
      change g.inner y.val (mfderiv I3 I3 (Subtype.val : U → M) y v)
        (mfderiv I3 I3 (Subtype.val : U → M) y w) = g.inner y.val v w
      rw [DifferentialGeometry.mfderiv_subtype_val_apply,
        DifferentialGeometry.mfderiv_subtype_val_apply])
    (fun _ _ => mem_univ _)

theorem SpatialNeck.ofRestrictOpen_map {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z)
    (y : Cylinder) : nk.ofRestrictOpen.map y = (nk.map y).val :=
  rfl

theorem SpatialNeck.ofRestrictOpen_center {z : U} (nk : SpatialNeck (g.restrictOpen U) eps z) :
    nk.ofRestrictOpen.center = nk.center :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
