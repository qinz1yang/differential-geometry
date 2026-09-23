import DifferentialGeometry.Topology.Connected.ComponentCollar
import DifferentialGeometry.Geometry.Neck.Spatial

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)

theorem SpatialNeck.signed_collar_connectedComponentIn
    {K : Set M} {x : M} {level σ r : ℝ}
    (hsource : ∀ z, ∀ t ∈ Ioo (-r) r, (z, level + σ * t) ∈ nk.map.source)
    (hside : ∀ z, ∀ t ∈ Ioo (-r) r, nk.map (z, level + σ * t) ∈ K ↔ t ≤ 0)
    (hinterior : ∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ interior K ↔ t < 0)
    (hzero : ∀ z, nk.map (z, level) ∈ connectedComponentIn K x) :
    (∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ connectedComponentIn K x ↔ t ≤ 0) ∧
    ∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ interior (connectedComponentIn K x) ↔ t < 0 := by
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  apply DifferentialGeometry.Topology.connectedComponentIn_interval_side
    (fun z t => nk.map (z, level + σ * t))
  · intro z
    have hcurve : ContinuousOn (fun t : ℝ => (z, level + σ * t)) (Ioo (-r) r) := by
      exact (continuous_const.prodMk (continuous_const.add
        (continuous_const.mul continuous_id))).continuousOn
    exact nk.map.contMDiffOn_toFun.continuousOn.comp hcurve
      (fun t ht => hsource z t ht)
  · exact hside
  · exact hinterior
  · simpa only [mul_zero, add_zero] using hzero

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
