import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedLocalBall_S18
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence
import DifferentialGeometry.Geometry.Metric.Tensor.CompactBounds

/-!
# CH12-S18 / V1a, group C: uniform sectional lower bound on `Φ_k(K)`

Canonical `C²` convergence gives, for a compact `K` of the limit, eventually a uniform bound on
`curvDerivNorm 0` of the actual metrics on `Φ_k(K)`, hence a uniform sectional lower bound.
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Topology ContDiff _root_.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance curvS18ManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance curvS18LimitTopology : TopologicalSpace L.M := L.topology
private local instance curvS18LimitCharted : ChartedSpace H L.M := L.charted
private local instance curvS18LimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance curvS18LimitT2 : T2Space L.M := L.t2
private local instance curvS18LimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance curvS18ApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance curvS18ApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance curvS18ApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance curvS18ApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
private local instance curvS18ApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

private local instance curvS18SourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
private local instance curvS18SourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
private local instance curvS18SourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
private local instance curvS18SourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
private local instance curvS18SourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

private local instance curvS18TargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
private local instance curvS18TargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
private local instance curvS18TargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
private local instance curvS18TargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
private local instance curvS18TargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

omit [I.Boundaryless] in
theorem curvDerivNorm_zero_eq_sqrt_S18 {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    curvDerivNorm 0 g x = Real.sqrt (Tensor0SBundle.normSq0S g x 4 (metricRm04At g x)) := by
  change Real.sqrt (Tensor0SBundle.normSq0S g x 4 (metricRm04 g x)) = _
  rw [metricRm04_apply]

theorem exists_eventually_curvDerivNorm_le_on_compact_S18
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    {K : Set L.M} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, K ⊆ Phi.source k ∧ ∀ x ∈ K,
      curvDerivNorm 0 (X.obj (subseq k)).metric (Phi.map k x) ≤ B := by
  obtain ⟨Cb, hCb0, hCb⟩ := Geometry.Tensor.exists_pos_bound_norm_on_compact L.metric
    (metricRm04 L.metric) hK
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let delta : ℝ := min (1 / 2 : ℝ) (1 / (n ^ 2 * (Cb + 360) + 1))
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hdhalf : delta ≤ 1 / 2 := min_le_left _ _
  have hdC : n ^ 2 * delta * (Cb + 360) ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < n ^ 2 * (Cb + 360) + 1)).mp
      (min_le_right _ _ : delta ≤ 1 / (n ^ 2 * (Cb + 360) + 1))
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv K hK delta hd
  refine ⟨4 * (Cb + 1), by positivity, Filter.eventually_atTop.2 ⟨k0, fun k hk => ?_⟩⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  refine ⟨hsource, fun x hx => ?_⟩
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha hU gU gU (x := xu) hx
    exact ht.trans hsup.le
  have hh := sqrt_normSq_metricRm04At_le_of_metricDerivNorm_le gU hU xu hdhalf hjet
  have hlim : curvDerivNorm 0 gU xu = curvDerivNorm 0 L.metric x :=
    curvDerivNorm_restrictOpen L.metric (metricSourceOpenSubset Phi k) 0 xu
  have hcurv : Real.sqrt (Tensor0SBundle.normSq0S gU xu 4 (metricRm04At gU xu)) ≤ Cb := by
    rw [← curvDerivNorm_zero_eq_sqrt_S18, hlim, curvDerivNorm_zero_eq_sqrt_S18]
    have := hCb x hx
    rwa [metricRm04_apply] at this
  have hpull : curvDerivNorm 0 hU xu =
      curvDerivNorm 0 (X.obj (subseq k)).metric (Phi.map k x) := by
    calc
      _ = curvDerivNorm 0 ((X.obj (subseq k)).metric.restrictOpen (I := I)
          (metricTargetOpenSubset Phi k)) (metricSourceTargetDiffeomorph Phi k xu) := by
        have e := Diffeomorph.pullbackMetricCross_eq_pullbackMetric
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k)
        calc curvDerivNorm 0 hU xu
            = curvDerivNorm 0 (Diffeomorph.pullbackMetricCross
              ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
              (metricSourceTargetDiffeomorph Phi k)) xu := by rw [e]
          _ = _ := curvDerivNorm_pullbackMetricCross _ _ 0 xu
      _ = _ := by
        have hr := curvDerivNorm_restrictOpen (X.obj (subseq k)).metric
          (metricTargetOpenSubset Phi k) 0 (metricSourceTargetDiffeomorph Phi k xu)
        erw [metric_source_target_diffeomorph_apply] at hr
        exact hr
  rw [← hpull, curvDerivNorm_zero_eq_sqrt_S18]
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left (add_le_add hcurv (le_refl 360))
    (mul_nonneg (sq_nonneg n) hd.le)
  change 4 * (Real.sqrt (Tensor0SBundle.normSq0S gU xu 4 (metricRm04At gU xu)) +
    n ^ 2 * delta * (Real.sqrt (Tensor0SBundle.normSq0S gU xu 4 (metricRm04At gU xu)) + 360)) ≤ _
  nlinarith [hmul, hdC, hcurv]

/-- Uniform sectional lower bound on `Φ_k(K)` from canonical `C²` convergence. -/
theorem exists_eventually_sectional_lower_on_compact_S18
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    {K : Set L.M} (hK : IsCompact K) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ᶠ k in atTop, K ⊆ Phi.source k ∧ ∀ x ∈ K,
      Geometry.Riemannian.SectionalBoundedBelowAt (X.obj (subseq k)).metric (Phi.map k x) (-Λ) := by
  obtain ⟨B, hB, hev⟩ := exists_eventually_curvDerivNorm_le_on_compact_S18 hconv hK
  refine ⟨B, hB, hev.mono fun k hk => ⟨hk.1, fun x hx => ?_⟩⟩
  apply sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le
  rw [← curvDerivNorm_zero_eq_sqrt_S18]
  exact hk.2 x hx

end DifferentialGeometry.CheegerGromovCompactness
