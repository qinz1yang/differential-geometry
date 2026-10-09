import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideDistance
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannBasic
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

theorem ray_eventually_upper {c : ℝ≥0 → N} (hc : Isometry c)
    (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) :
    ∀ᶠ t in atTop, c t ∈ D.upper s := by
  have hrad (t : ℝ≥0) : dist (c t) (c 0) = (t : ℝ) := by
    rw [hc.dist_eq]
    change |(t : ℝ) - 0| = (t : ℝ)
    rw [sub_zero, abs_of_nonneg t.coe_nonneg]
  have hescape : Tendsto c atTop (cocompact N) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (c 0)
    simpa only [hrad, id_eq] using
      (NNReal.tendsto_coe_atTop.mpr (tendsto_id : Tendsto (fun t : ℝ≥0 => t) atTop atTop))
  have hcompact : IsCompact (closure (D.lower s)) := (D.slice_spec s hs).2.2.2.2.2.2.1
  filter_upwards [hescape.eventually hcompact.compl_mem_cocompact] with t ht
  simpa only [D.closure_lower_eq_compl_upper s hs, mem_compl_iff, not_not] using ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section CompatibleMetric

variable [I.Boundaryless]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance inwardBusemannC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [I.Boundaryless] in
private theorem central_dist_upper (W : SpatialNeckWitness h yStar p epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (z : spatialNeckBuffer epsilon) (hz : z.val.2 = 0) :
    dist p (W.embedding z) ≤ 13 / 12 * spatialNeckScale h p * Real.pi := by
  let x := spatialNeckCentralPoint epsilon W.epsilon_pos yStar
  have hxcore : x ∈ spatialNeckClosedCore epsilon :=
    spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos rfl
  have hzcore : z ∈ spatialNeckClosedCore epsilon :=
    spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos hz
  have hedist := W.slice_edist_upper hsmall x z hxcore hzcore hz
  change riemannianEDistOf (I := I) h
    (W.embedding (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)) (W.embedding z) ≤ _ at hedist
  rw [W.marked, riemannianEDistOf_eq_riemannianEDist h hEnorm,
    ← IsRiemannianManifold.out (I := I)] at hedist
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  exact (edist_le_ofReal (by positivity : 0 ≤ 13 / 12 * spatialNeckScale h p * Real.pi)).mp hedist

theorem busemann_inward_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.lower (-(5 * Real.pi))) :
    busemann c q ≤ busemann c p - 7 / 2 * Real.pi * spatialNeckScale h p := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    rw [abs_zero]
    linarith [Real.pi_pos]
  have hneg : |-(5 * Real.pi)| < epsilon⁻¹ + 1 := by
    rw [abs_neg, abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hqzero : q ∈ D.lower 0 :=
    (D.ordered_band (-(5 * Real.pi)) 0 hneg hzero (by linarith [Real.pi_pos])).1
      (subset_closure hq)
  have hevent : ∀ᶠ t in atTop,
      busemannApprox c t q - busemannApprox c t p ≤
        -(7 / 2 * Real.pi * spatialNeckScale h p) := by
    filter_upwards [D.ray_eventually_upper hc 0 hzero] with t ht
    obtain ⟨z, ⟨w, hw, rfl⟩, hadd⟩ := D.exists_slice_distance_add hEnorm 0 hzero hqzero ht
    have hlower := D.inward_center_distance_lower hEnorm hsmall hq w hw
    have hupper := central_dist_upper W hEnorm hsmall w hw
    have htriangle := dist_triangle p (W.embedding w) (c t)
    dsimp only [busemannApprox]
    nlinarith
  have hlimit := le_of_tendsto ((tendsto_busemannApprox hc q).sub
    (tendsto_busemannApprox hc p)) hevent
  linarith


theorem busemann_inward_lt (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {c : ℝ≥0 → N} (hc : Isometry c) {q : N}
    (hq : q ∈ D.lower (-(5 * Real.pi))) : busemann c q < busemann c p := by
  have hbound := D.busemann_inward_le hEnorm hsmall hc hq
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hpositive : 0 < 7 / 2 * Real.pi * spatialNeckScale h p := by positivity
  linarith

end CompatibleMetric

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
