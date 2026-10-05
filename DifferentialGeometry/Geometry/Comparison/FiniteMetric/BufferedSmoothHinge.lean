import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingLensBounds
import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureHinge
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement

/-!
The smooth hinge comparison only needs nonnegative sectional curvature in the prescribed ball.
The minimizing-lens radius estimate supplies that local hypothesis, and negative-curvature
comparison passes to zero without altering either exponential arm or its initial direction.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [groupE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E] [rankE : NeZero (Module.finrank ℝ E)]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [sigmaM : SigmaCompactSpace M] [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M]
  [continuousBundle : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem comparisonAngle_le_arccos_inner_smooth_of_sectional_nonneg_on_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) (u v : TangentSpace I o) {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (intrinsicGeodesic g hEnorm o u a) = a)
    (hminB : dist o (intrinsicGeodesic g hEnorm o v b) = b)
    (hsec : ∀ y ∈ Metric.ball o R, SectionalBoundedBelowAt g y 0) :
    comparisonAngle a b
      (dist (intrinsicGeodesic g hEnorm o u a) (intrinsicGeodesic g hEnorm o v b)) ≤
        Real.arccos (g.inner o u v) := by
  have hd (x y : M) : (riemannianEDist I x y).toReal = dist x y := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have he (x y : M) : riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
    rw [← IsRiemannianManifold.out, edist_dist]
  have hminA' : (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a)).toReal = a :=
    (hd o _).trans hminA
  have hminB' : (riemannianEDist I o (intrinsicGeodesic g hEnorm o v b)).toReal = b :=
    (hd o _).trans hminB
  have hsum : a + b < R := by linarith
  have hlens (k : ℝ) : ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic g hEnorm o u s) y +
        riemannianEDist I y (intrinsicGeodesic g hEnorm o v t) =
        riemannianEDist I (intrinsicGeodesic g hEnorm o u s)
          (intrinsicGeodesic g hEnorm o v t) →
      SectionalBoundedBelowAt g y (-k ^ 2) := by
    intro s hs t ht y hy
    have hP : dist o (intrinsicGeodesic g hEnorm o u s) = s :=
      (hd o _).symm.trans (unit_intrinsic_subsegment_dist g hEnorm o u hu a s ha
        hs.1 hs.2 hminA')
    have hQ : dist o (intrinsicGeodesic g hEnorm o v t) = t :=
      (hd o _).symm.trans (unit_intrinsic_subsegment_dist g hEnorm o v hv b t hb
        ht.1 ht.2 hminB')
    have hyreal : dist (intrinsicGeodesic g hEnorm o u s) y +
        dist y (intrinsicGeodesic g hEnorm o v t) =
        dist (intrinsicGeodesic g hEnorm o u s) (intrinsicGeodesic g hEnorm o v t) := by
      rw [he, he, he, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hy
      simpa only [ENNReal.toReal_ofReal (add_nonneg dist_nonneg dist_nonneg),
        ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal hy
    have hybound := minimizingLens_dist_le_sum o (intrinsicGeodesic g hEnorm o u s)
      (intrinsicGeodesic g hEnorm o v t) y hyreal
    rw [hP, hQ] at hybound
    have hymem : y ∈ Metric.ball o R := Metric.mem_ball'.mpr (by linarith [hs.2, ht.2])
    exact SectionalBoundedBelowAt.mono (hsec y hymem) (by nlinarith [sq_nonneg k])
  have hcurvature : Tendsto (fun k : ℝ => k ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using
      ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).pow 2
  have hangle := tendsto_comparisonAngleNegCurvature_zero hcurvature
    (tendsto_const_nhds (x := a)) (tendsto_const_nhds (x := b))
    (tendsto_const_nhds (x := dist (intrinsicGeodesic g hEnorm o u a)
      (intrinsicGeodesic g hEnorm o v b)))
    (Eventually.of_forall (fun k => sq_nonneg k)) ha hb
  apply le_of_tendsto hangle
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hkpos : 0 < k := hk
  have hcompare :=
    hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
      g hEnorm o u v hkpos ha hb hu hv hminA' hminB' (hlens k)
  rw [hd] at hcompare
  change comparisonAngleNegCurvature (k ^ 2) a b
    (dist (intrinsicGeodesic g hEnorm o u a) (intrinsicGeodesic g hEnorm o v b)) ≤ _
  simpa only [comparisonAngleNegCurvature, hyperbolicComparisonAngle,
    hyperbolicComparisonCosine, ite_eq_right (pow_ne_zero 2 hkpos.ne'),
    Real.sqrt_sq hkpos.le] using hcompare

theorem local_hinge_for_ported_smooth_arms
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) (u v : TangentSpace I o) {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y ∈ Metric.ball o R, SectionalBoundedBelowAt g y 0) :
    comparisonAngle a b (dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, b • v⟩ : TangentBundle I M))) ≤ Real.arccos (g.inner o u v) := by
  have hA := g.expMap_smul_eq_intrinsicGeodesic hEnorm o u a
  have hB := g.expMap_smul_eq_intrinsicGeodesic hEnorm o v b
  rw [hA, hB]
  rw [hA] at hminA
  rw [hB] at hminB
  exact comparisonAngle_le_arccos_inner_smooth_of_sectional_nonneg_on_ball
    g hEnorm o u v ha hb hR hu hv hminA hminB hsec

end DifferentialGeometry.Geometry.FiniteComparison
