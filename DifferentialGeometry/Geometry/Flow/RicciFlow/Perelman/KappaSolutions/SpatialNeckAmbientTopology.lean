import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveSoulDiffeomorph
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] [NoncompactSpace N]

private local instance ambientTopologyC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

theorem nonempty_ambient_homeomorph
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    Nonempty (N ≃ₜ E) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : T3Space N := inferInstance
  let _ : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace N := EMetricSpace.ofRiemannianMetric I N
  let _ : CompleteSpace N := W.complete.complete
  have hEnorm : IsMetricNorm (I := I) h := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) h x v
  let _ : MetricSpace N := riemMetricSpace (I := I) (M := N)
  let _ : ProperSpace N := properSpace_riemMetric (I := I) W.complete.complete h hEnorm
  let _ : IsRiemannianManifold I N := ⟨fun x y => by
    rw [edist_dist, riemMetric_dist_eq (I := I)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I) x y)⟩
  obtain ⟨_S, _s, _hs, _hne, _hcompact, _hconv, _hboundary, _hdim, e, _he⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_point_soul_diffeomorph h hEnorm hsec p
  exact ⟨e.toHomeomorph⟩

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
