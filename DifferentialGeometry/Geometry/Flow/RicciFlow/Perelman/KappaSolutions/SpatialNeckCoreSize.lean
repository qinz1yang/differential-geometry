import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreCurves
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def spatialNeckCoreRadiusConstant (epsilon : ℝ) : ℝ :=
  13 / 12 * Real.sqrt 2 * Real.sqrt (Real.pi ^ 2 + (epsilon⁻¹) ^ 2)

theorem spatialNeckCoreRadiusConstant_pos (epsilon : ℝ) :
    0 < spatialNeckCoreRadiusConstant epsilon := by
  unfold spatialNeckCoreRadiusConstant
  positivity

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance coreSizeC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem SpatialNeckWitness.core_dist_le
    {h : SmoothRiemannianMetric I N} {mark : SpatialNeckSphere} {p : N} {epsilon : ℝ}
    (W : SpatialNeckWitness h mark p epsilon) (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) {q : N} (hq : q ∈ W.core) :
    dist p q ≤ spatialNeckCoreRadiusConstant epsilon /
      Real.sqrt (metricScalarAt (I := I) h p) := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hbound := W.core_edist_upper hsmall
    (spatialNeckCentralPoint epsilon W.epsilon_pos mark) z
    (spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos rfl) hz
  rw [W.marked, riemannianEDistOf_eq_riemannianEDist h hEnorm,
    ← IsRiemannianManifold.out (I := I)] at hbound
  change edist p (W.embedding z) ≤ ENNReal.ofReal
    ((13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (z.val.2 - 0) ^ 2)) at hbound
  rw [sub_zero] at hbound
  have hreal := (edist_le_ofReal (by positivity : 0 ≤
    (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + z.val.2 ^ 2))).mp hbound
  have habs : |z.val.2| ≤ epsilon⁻¹ := abs_le.mpr hz
  have hsq : z.val.2 ^ 2 ≤ (epsilon⁻¹) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg z.val.2) (inv_nonneg.mpr W.epsilon_pos.le)).mpr habs
    simpa only [sq_abs] using hh
  calc
    dist p (W.embedding z) ≤
        (13 / 12 * spatialNeckScale h p) * Real.sqrt (Real.pi ^ 2 + (epsilon⁻¹) ^ 2) :=
      hreal.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
    _ = spatialNeckCoreRadiusConstant epsilon / Real.sqrt (metricScalarAt (I := I) h p) := by
      dsimp only [spatialNeckCoreRadiusConstant, spatialNeckScale]
      ring

theorem eventually_spatialNeck_core_subset_ball
    {h : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness h (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hscalar : Tendsto (fun i => metricScalarAt (I := I) h (centers i)) atTop atTop)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ i in atTop, (W i).core ⊆ Metric.ball (centers i) r := by
  let C := spatialNeckCoreRadiusConstant epsilon
  have hC : 0 < C := spatialNeckCoreRadiusConstant_pos epsilon
  filter_upwards [hscalar.eventually_gt_atTop ((C / r) ^ 2)] with i hi
  have hsqrt : 0 < Real.sqrt (metricScalarAt (I := I) h (centers i)) :=
    Real.sqrt_pos.mpr (W i).scalar_pos
  have hlarge : C / r < Real.sqrt (metricScalarAt (I := I) h (centers i)) := by
    by_contra! hn
    have hsq := (sq_le_sq₀ hsqrt.le (by positivity : 0 ≤ C / r)).mpr hn
    rw [Real.sq_sqrt (W i).scalar_pos.le] at hsq
    exact (not_le_of_gt hi) hsq
  have hsmallRadius : C / Real.sqrt (metricScalarAt (I := I) h (centers i)) < r := by
    apply (div_lt_iff₀ hsqrt).mpr
    have hm := (div_lt_iff₀ hr).mp hlarge
    nlinarith
  intro q hq
  rw [Metric.mem_ball, dist_comm q (centers i)]
  exact ((W i).core_dist_le hEnorm hsmall hq).trans_lt hsmallRadius

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
