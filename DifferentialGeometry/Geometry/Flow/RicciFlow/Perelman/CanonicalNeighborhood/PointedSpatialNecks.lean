import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedInverseComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckImageRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Metric.Comparison.Inverse

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_spatialNeck_of_pointed_strongNecks_on_compact_ball
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : FlowSequence.{u}) (f : ℕ → ℕ)
      (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
      (maps : PointedRiemannianConvergenceMaps (X.atTime 0) L f)
      (C : MetricConvergenceData maps),
      (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
      ∀ x : L.M, 0 < metricScalarAt L.metric x → ∀ R : ℝ, 0 < R →
        IsCompact (riemannianClosedBallOf L.metric x R) →
        D < Real.sqrt (metricScalarAt L.metric x) * R →
        (∀ᶠ n in atTop, Nonempty (StrongNeck (X.term (f n)).S
          (neckModelTolerance alpha) (maps.partialDiffeomorph n x) 0)) →
        Nonempty (SpatialNeck L.metric (2 * alpha) x) := by
  have htol : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  obtain ⟨D, hD, hdiam⟩ := exists_uniform_neck_image_radius.{u}
    (neckModelTolerance_pos ha) htol
  refine ⟨4 * D, by positivity, ?_⟩
  intro X f L maps C hcanonical x hQ R hR hcompact hsep hnecks
  let Q := metricScalarAt L.metric x
  let q : ℕ → ℝ := fun n => (X.term (f n)).S.scalar 0 (maps.partialDiffeomorph n x)
  let K := riemannianClosedBallOf L.metric x R
  have hxK : x ∈ K := by
    change riemannianEDistOf L.metric _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hscalar : Tendsto q atTop (𝓝 Q) :=
    KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  have hbuf : D / Real.sqrt Q < R / 2 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
    nlinarith
  have hbuflim : Tendsto (fun n => D / Real.sqrt (q n)) atTop (𝓝 (D / Real.sqrt Q)) :=
    tendsto_const_nhds.div hscalar.sqrt (Real.sqrt_pos.mpr hQ).ne'
  have hreference (n : ℕ) : (C.domain n).referenceMetric = (C.domain n).limitMetric := by
    rw [hcanonical n]
    rfl
  obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
    C hreference K hcompact (1 / 2) (by norm_num)
  have hcmp := eventually_rescaled_inverse_metricComparisonOn_on_compact C hcanonical K hcompact
    ⌈(2 * alpha)⁻¹⌉₊ (neckSourceTolerance_pos ha) q (fun _ => Q) hQ hscalar tendsto_const_nhds {0}
  obtain ⟨n, hn, ⟨nk⟩, hbufn, hKn, hqn, hQn, ⟨cmp⟩⟩ :=
    ((eventually_ge_atTop N).and (hnecks.and
      ((hbuflim.eventually (eventually_lt_nhds hbuf)).and hcmp))).exists
  have hquad (z : L.M) (hz : z ∈ K) (v : TangentSpace I3 z) :
      L.metric.inner z v v ≤ 2 ^ 2 * ((X.term (f n)).S.base.metric 0).inner
        (maps.partialDiffeomorph n z) (mfderiv I3 I3 (maps.partialDiffeomorph n) z v)
        (mfderiv I3 I3 (maps.partialDiffeomorph n) z v) := by
    have hh := (abs_le.mp ((hN n hn).2 z hz v)).1
    change -((1 / 2 : ℝ) * L.metric.inner z v v) ≤
      ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n z)
        (mfderiv I3 I3 (maps.partialDiffeomorph n) z v)
        (mfderiv I3 I3 (maps.partialDiffeomorph n) z v) - L.metric.inner z v v at hh
    have hnonneg := inner_self_nonneg ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n z) (mfderiv I3 I3 (maps.partialDiffeomorph n) z v)
    nlinarith
  have houter (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) :
      nk.map y ∈ (maps.partialDiffeomorph n) '' K := by
    have hd := hdiam (X.term (f n)).M (X.interval (f n)) (X.term (f n)).S
      (maps.partialDiffeomorph n x) 0 nk y hy
    have hsqrt : 0 < Real.sqrt (q n) := Real.sqrt_pos.mpr hqn
    have hscale : ENNReal.ofReal (Real.sqrt (q n)) *
        riemannianEDistOf ((X.term (f n)).S.base.metric 0)
          (maps.partialDiffeomorph n x) (nk.map y) ≤ ENNReal.ofReal D := by
      simp only [rescaledMetric, parabolicTime_zero] at hd
      erw [edistOf_scale] at hd
      exact hd
    have hcoef : ENNReal.ofReal (Real.sqrt (q n)) *
        ENNReal.ofReal (D / Real.sqrt (q n)) = ENNReal.ofReal D := by
      rw [← ENNReal.ofReal_mul hsqrt.le]
      congr 1
      field_simp
    have hball : nk.map y ∈ riemannianClosedBallOf ((X.term (f n)).S.base.metric 0)
        (maps.partialDiffeomorph n x) (D / Real.sqrt (q n)) :=
      (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))
        ENNReal.ofReal_ne_top).mp (hscale.trans_eq hcoef.symm)
    obtain ⟨htarget, hinK⟩ := KappaSolutions.inverse_mem_closedBall_of_metric_lower
      L.metric ((X.term (f n)).S.base.metric 0) (maps.partialDiffeomorph n) x
      hR (by norm_num : (0 : ℝ) < 2) hbufn hcompact hKn hquad (nk.map y) hball
    exact ⟨(maps.partialDiffeomorph n).symm (nk.map y), hinK,
      (maps.partialDiffeomorph n).right_inv' htarget⟩
  have hVsource : (maps.partialDiffeomorph n) '' K ⊆ (maps.partialDiffeomorph n).symm.source := by
    rintro y ⟨z, hz, rfl⟩
    exact (maps.partialDiffeomorph n).map_source (hKn hz)
  have hbase : (maps.partialDiffeomorph n).symm (maps.partialDiffeomorph n x) = x :=
    (maps.partialDiffeomorph n).left_inv' (hKn hxK)
  obtain ⟨nk', _⟩ := nk.toSpatialNeck.exists_transport_of_local_comparisons hQ
    (maps.partialDiffeomorph n).symm cmp ha (by linarith)
    (neckSourceTolerance_pos ha).le le_rfl le_rfl hbase houter hVsource
  exact ⟨nk'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
