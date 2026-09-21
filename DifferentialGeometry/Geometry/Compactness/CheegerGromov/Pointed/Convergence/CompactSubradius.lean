import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem PointedRiemannianConvergenceMaps.isCompact_closedBall_of_compact_source_ball_capture
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {Q : PointedRiemannianManifold.{u, uE, uH} I} {chi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X Q chi) (C : MetricConvergenceData F)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    {r R : ℝ} (hR : 0 < R) (hrR : r < R)
    (hcapture : ∃ K : Set Q.M, IsCompact K ∧ ∀ᶠ i in atTop,
      riemannianBallOf (X.obj (chi i)).metric (X.obj (chi i)).basepoint R ⊆ F.map i '' K) :
    IsCompact (riemannianClosedBallOf Q.metric Q.basepoint r) := by
  obtain ⟨K, hK, hcapture⟩ := hcapture
  apply hK.of_isClosed_subset
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist Q.metric Q.basepoint) continuous_const)
  intro x hx
  have hxR : riemannianEDistOf Q.metric Q.basepoint x < ENNReal.ofReal R :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR)
  have hnear := eventually_riemannianEDistOf_map_lt_of_metric_convergence
    C hreference Q.basepoint x hxR
  have hsource : ∀ᶠ i in atTop, x ∈ F.source i := by
    obtain ⟨N, hN⟩ := F.source_subset (isCompact_singleton (x := x))
    filter_upwards [eventually_ge_atTop N] with i hi
    exact hN i hi (mem_singleton x)
  have hKsource : ∀ᶠ i in atTop, K ⊆ F.source i := by
    obtain ⟨N, hN⟩ := F.source_subset hK
    exact eventually_atTop.mpr ⟨N, hN⟩
  obtain ⟨i, hcap, hdist, hxsource, hKsource⟩ :=
    (hcapture.and (hnear.and (hsource.and hKsource))).exists
  have hball : F.map i x ∈ riemannianBallOf (X.obj (chi i)).metric
      (X.obj (chi i)).basepoint R := by
    change riemannianEDistOf (X.obj (chi i)).metric _ _ < ENNReal.ofReal R
    have hb : F.map i Q.basepoint = (X.obj (chi i)).basepoint := F.basepoint_map i
    rwa [hb] at hdist
  obtain ⟨y, hy, hyx⟩ := hcap hball
  have heq : y = x := (F.partialDiffeomorph i).injOn (hKsource hy) hxsource hyx
  exact heq ▸ hy

end DifferentialGeometry.CheegerGromovCompactness

end
