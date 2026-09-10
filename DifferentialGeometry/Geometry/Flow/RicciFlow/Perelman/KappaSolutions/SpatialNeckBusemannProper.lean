import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannOutward
import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannData

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff Topology NNReal

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

private local instance neckProperC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

include D

theorem busemann_sublevel_isCompact (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) (r : ℝ) :
    IsCompact {q : N | busemann c q ≤ r} := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  let _ : ProperSpace N := completeMetric_compatible_properSpace h hEnorm W.complete
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hK : IsCompact (closure (D.lower (5 * Real.pi))) :=
    (D.slice_spec (5 * Real.pi) hs).2.2.2.2.2.2.1
  have hcont := (lipschitzWith_busemann hc).continuous
  apply (hK.union (isCompact_closedBall p (4 * (r - busemann c p)))).of_isClosed_subset
    (isClosed_le hcont continuous_const)
  intro q hq
  by_cases hqin : q ∈ closure (D.lower (5 * Real.pi))
  · exact Or.inl hqin
  · have hqout : q ∈ D.upper (5 * Real.pi) := by
      simpa only [D.closure_lower_eq_compl_upper (5 * Real.pi) hs,
        mem_compl_iff, not_not] using hqin
    have hbound := D.busemann_outward_ge hEnorm hsmall hsec hc hqout
    right
    rw [Metric.mem_closedBall, dist_comm q p]
    change busemann c q ≤ r at hq
    linarith

theorem busemann_isProperMap (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) : IsProperMap (busemann c) := by
  have hcont := (lipschitzWith_busemann hc).continuous
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont, ?_⟩
  intro K hK
  obtain ⟨r, hr⟩ := hK.bddAbove
  apply (D.busemann_sublevel_isCompact hEnorm hsmall hsec hc r).of_isClosed_subset
    (hK.isClosed.preimage hcont)
  intro q hq
  exact hr hq

theorem busemann_bddBelow (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) : BddBelow (range (busemann c)) := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hK : IsCompact (closure (D.lower (5 * Real.pi))) :=
    (D.slice_spec (5 * Real.pi) hs).2.2.2.2.2.2.1
  obtain ⟨L, hL⟩ := hK.bddBelow_image (lipschitzWith_busemann hc).continuous.continuousOn
  refine ⟨min L (busemann c p), ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hqin : q ∈ closure (D.lower (5 * Real.pi))
  · exact (min_le_left _ _).trans (hL ⟨q, hqin, rfl⟩)
  · have hqout : q ∈ D.upper (5 * Real.pi) := by
      simpa only [D.closure_lower_eq_compl_upper (5 * Real.pi) hs,
        mem_compl_iff, not_not] using hqin
    have hbound := D.busemann_outward_ge hEnorm hsmall hsec hc hqout
    have hle : busemann c p ≤ busemann c q := by linarith [dist_nonneg (x := p) (y := q)]
    exact (min_le_right _ _).trans hle

theorem exists_busemann_minimum (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {c : ℝ≥0 → N} (hc : Isometry c) :
    ∃ q : N, busemann c q = (⨅ x : N, busemann c x) ∧
      ∀ x : N, busemann c q ≤ busemann c x :=
  exists_busemann_minimum_of_proper c
    (D.busemann_isProperMap hEnorm hsmall hsec hc)
    (D.busemann_bddBelow hEnorm hsmall hsec hc)

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
