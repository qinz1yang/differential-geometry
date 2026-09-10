import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannProper

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem spatialNeckControlEpsilon_lt_inverse_five_pi :
    spatialNeckControlEpsilon < (5 * Real.pi)⁻¹ := by
  have h := one_div_lt_one_div_of_lt (by positivity : 0 < 5 * Real.pi)
    (by linarith [Real.pi_pos] : 5 * Real.pi < 100 * (1 + Real.pi))
  simpa only [spatialNeckControlEpsilon, inv_eq_one_div] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] [NoncompactSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance neckDiameterC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

namespace SpatialNeckWitness

theorem busemann_level_diameter_and_proper
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    11 / 12 * spatialNeckScale h p * Real.pi ≤
      Metric.diam {q : N | busemann c q = busemann c p} ∧
    Metric.diam {q : N | busemann c q = busemann c p} ≤
      11 * Real.pi * spatialNeckScale h p ∧
    IsProperMap (busemann c) ∧ BddBelow (range (busemann c)) ∧
    ∃ q : N, busemann c q = (⨅ x : N, busemann c x) ∧
      ∀ x : N, busemann c q ≤ busemann c x := by
  obtain ⟨W', _hchoice, _hsphere, _hcore, _himage, ⟨D⟩⟩ :=
    W.exists_ordered_compact_end_sides hsec
  have hnonneg := hsec.toNonnegative
  obtain ⟨hlower, hupper⟩ := D.busemann_level_diam_bounds hEnorm hsmall hnonneg hc
  exact ⟨hlower, hupper, D.busemann_isProperMap hEnorm hsmall hnonneg hc,
    D.busemann_bddBelow hEnorm hsmall hnonneg hc,
    D.exists_busemann_minimum hEnorm hsmall hnonneg hc⟩

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
