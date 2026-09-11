import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannInward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardAngle

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance outwardBusemannC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

theorem busemann_outward_ge (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.upper (5 * Real.pi)) :
    busemann c p + dist p q / 4 ≤ busemann c q := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hevent : ∀ᶠ t in atTop,
      busemannApprox c t p - busemannApprox c t q ≤ -(dist p q / 4) := by
    filter_upwards [D.ray_eventually_upper hc (5 * Real.pi) hs,
      eventually_ge_atTop ((2 * dist p q + dist (c 0) p).toNNReal)] with t ht htime
    have htimeReal : 2 * dist p q + dist (c 0) p ≤ (t : ℝ) := by
      have hcast : (((2 * dist p q + dist (c 0) p).toNNReal : ℝ≥0) : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast htime
      simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * dist p q + dist (c 0) p)] using hcast
    have hrad : dist (c 0) (c t) = (t : ℝ) := by
      rw [hc.dist_eq]
      change |0 - (t : ℝ)| = (t : ℝ)
      rw [zero_sub, abs_neg, abs_of_nonneg t.coe_nonneg]
    have htriangle := dist_triangle (c 0) p (c t)
    rw [hrad] at htriangle
    have hlarge : 2 * dist p q ≤ dist p (c t) := by linarith
    have hloss := D.outward_distance_loss hEnorm hsmall hsec ht hq hlarge
    rw [dist_comm (c t) q] at hloss
    dsimp only [busemannApprox]
    linarith
  have hlimit := le_of_tendsto ((tendsto_busemannApprox hc p).sub
    (tendsto_busemannApprox hc q)) hevent
  linarith

theorem busemann_outward_lt (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.upper (5 * Real.pi)) : busemann c p < busemann c q := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hp := D.marked_mem_lower (5 * Real.pi) hs (by positivity)
  have hdisjoint := (D.slice_spec (5 * Real.pi) hs).2.2.2.2.1
  have hpq : p ≠ q := by
    intro heq
    have hqlower : q ∈ D.lower (5 * Real.pi) :=
      (congrArg (fun z : N => z ∈ D.lower (5 * Real.pi)) heq).mp hp
    exact Set.disjoint_left.mp hdisjoint hqlower hq
  have hdist : 0 < dist p q := dist_pos.mpr hpq
  have hbound := D.busemann_outward_ge hEnorm hsmall hsec hc hq
  linarith

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
