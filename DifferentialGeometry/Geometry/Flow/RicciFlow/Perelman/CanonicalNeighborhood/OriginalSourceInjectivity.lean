import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

noncomputable section
open Filter Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem RealizedFiniteHorn.exists_original_source_curvature_derivative_bounds_and_injectivity
    {kappa : ℝ} (hkappa : 0 < kappa) (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, ∃ hc : 0 < c, 0 < epsStar ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∃ B : ℕ → ℝ, ∃ eta : ℝ, (∀ m, 0 ≤ B m) ∧ 0 < eta ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence, ∀ x : ℕ → H.space,
              ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (x n),
                ∃ threshold : ℕ → ℕ, ∀ n j, threshold n ≤ j →
                  ∃ S : SolutionOn (I := I3) (M := (X.term (H.subseq j)).M)
                    (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                    IsSolutionOn S ∧
                    (∀ t, S.base.metric t =
                      scaleMetric (metricScalarAt H.metric (x n))
                        (zero_lt_one.trans_le (hQ n))
                        ((X.term (H.subseq j)).S.base.metric
                          (t / metricScalarAt H.metric (x n)))) ∧
                    (∀ t ∈ Icc (-(c / 6)) 0, RiemannianMetricComplete (S.base.metric t)) ∧
                    |S.scalar 0 (H.maps j (x n)) - 1| < 1 / ((n : ℝ) + 2) ∧
                    (∀ y : (X.term (H.subseq j)).M, ∀ t ∈ Icc (-(c / 6)) 0,
                      y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / Real.sqrt 3) →
                      S.scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C * (3 + 13 * Phi 1)) ∧
                    (∀ m : ℕ, ∀ t ∈ Icc (-(c / 24)) 0,
                      ∀ y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / (2 * Real.sqrt 3)),
                      curvDerivNorm (I := I3) m (S.base.metric t) y ≤ B m) ∧
                    let P : PointedRiemannianManifold.{u, 0, 0} I3 :=
                      { (X.term (H.subseq j)).atTime 0 with
                        basepoint := H.maps j (x n)
                        metric := S.base.metric 0 }
                    ∀ y ∈ riemannianClosedBallOf P.metric P.basepoint
                      (c / (2 * Real.sqrt 3)), HasInjRadiusAt P y eta := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨epsSrc, c, C, hc, hepsSrc, hC, hsolutions⟩ :=
    RealizedFiniteHorn.exists_original_source_curvature_derivative_bounds hmod
  obtain ⟨epsNC, hepsNC, hncAll⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  refine ⟨min epsSrc epsNC, c, C, hc, lt_min hepsSrc hepsNC, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi
  obtain ⟨B, hB, hsolutions'⟩ := hsolutions eps heps (hepsStar'.trans (min_le_left _ _)) sigma
    hsigma Phi hPhi
  obtain ⟨kappa', hkappa', hncX⟩ := hncAll Phi hPhi
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hkappa'
  let K : ℝ := C * (3 + 13 * Phi 1)
  have hK : 0 < K := mul_pos hC (by linarith [hPhi.pos 1])
  let r : ℝ := c / Real.sqrt 3
  have hr : 0 < r := by dsimp only [r]; positivity
  let rho : ℝ := min (r / 2) (min 1 (1 / K))
  have hrho : 0 < rho := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hrhohalf : rho ≤ r / 2 := min_le_left _ _
  have hrhoone : rho ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhoK : rho * K ≤ 1 := (le_div_iff₀ hK).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  have hrhoSq : rho ^ 2 * K ≤ 1 := by
    calc
      rho ^ 2 * K = rho * (rho * K) := by ring
      _ ≤ rho * 1 := mul_le_mul_of_nonneg_left hrhoK hrho.le
      _ ≤ 1 := by simpa only [mul_one] using hrhoone
  have hscaled : rho ^ 4 * K ^ 2 ≤ 1 := by
    calc
      rho ^ 4 * K ^ 2 = (rho ^ 2 * K) ^ 2 := by ring
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hrhoSq 2
      _ = 1 := by norm_num
  refine ⟨B, iota * rho, hB, mul_pos hiota hrho, ?_⟩
  intro X H x hQ
  obtain ⟨threshold, hthreshold⟩ := hsolutions' X H x hQ
  have hnc := (hncX eps heps (hepsStar'.trans (min_le_right _ _)) sigma
    X).eventually_metricNoncollapsed_scaleMetric
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 (H.strictMono.tendsto_atTop.eventually hnc)
  refine ⟨fun n => max (threshold n) j0, ?_⟩
  intro n j hj
  obtain ⟨S, hS, hmetric, hcomplete, hcenter, hcurv, hderiv⟩ :=
    hthreshold n j ((le_max_left _ _).trans hj)
  refine ⟨S, hS, hmetric, hcomplete, hcenter, hcurv, hderiv, ?_⟩
  dsimp only
  let P : PointedRiemannianManifold.{u, 0, 0} I3 :=
    { (X.term (H.subseq j)).atTime 0 with
      basepoint := H.maps j (x n)
      metric := S.base.metric 0 }
  have hmetric0 : S.base.metric 0 =
      scaleMetric (metricScalarAt H.metric (x n)) (zero_lt_one.trans_le (hQ n))
        ((X.term (H.subseq j)).S.base.metric 0) := by
    simpa only [zero_div] using hmetric 0
  have hnc : MetricNoncollapsed P kappa' (Ioc 0 (Real.sqrt (metricScalarAt H.metric (x n)))) := by
    dsimp only [P]
    rw [hmetric0]
    exact hj0 j ((le_max_right _ _).trans hj) _ (zero_lt_one.trans_le (hQ n)) (H.maps j (x n))
  intro y hy
  change HasInjRadiusAt P y (iota * rho)
  have hcontrol : ∀ z ∈ riemannianBallOf P.metric y rho,
      rho ^ 4 * Tensor0SBundle.normSq0S P.metric z 4 (metricRm04At P.metric z) ≤ 1 := by
    intro z hz
    have hhalf : c / (2 * Real.sqrt 3) = r / 2 := by dsimp only [r]; ring
    have hy' : riemannianEDistOf P.metric P.basepoint y ≤ ENNReal.ofReal (r / 2) := by
      rw [hhalf] at hy
      exact hy
    have hz' : z ∈ riemannianClosedBallOf P.metric P.basepoint r := by
      calc
        riemannianEDistOf P.metric P.basepoint z ≤
            riemannianEDistOf P.metric P.basepoint y + riemannianEDistOf P.metric y z :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
          add_le_add hy' (hz.le.trans (ENNReal.ofReal_le_ofReal hrhohalf))
        _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ r / 2) (by positivity : 0 ≤ r / 2)]
          congr 1
          ring
    have hbound := (hcurv z 0 ⟨by linarith, le_rfl⟩ hz').2
    have hnonneg : 0 ≤ FlowMetricBall.rmNormSq S 0 z :=
      Tensor0SBundle.normSq0S_nonneg _ _ _ _
    have hnorm := (sq_le_sq₀ (Real.sqrt_nonneg _) hK.le).2 hbound
    rw [Real.sq_sqrt hnonneg] at hnorm
    exact (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hrho.le 4)).trans hscaled
  have hscalej : rho ≤ Real.sqrt (metricScalarAt H.metric (x n)) := by
    have hsqrt : 1 ≤ Real.sqrt (metricScalarAt H.metric (x n)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hQ n)
    exact hrhoone.trans hsqrt
  have hvol := hnc y rho ⟨hrho, hscalej⟩ hrho hcontrol
  have hvol' : ENNReal.ofReal (kappa' * rho ^ Module.finrank ℝ ThreeSpace) ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I3 P.M P.metric
        (riemannianBallOf P.metric y rho) := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hvol
  have hcomplete0 : RiemannianMetricComplete P.metric :=
    hcomplete 0 ⟨by linarith, le_rfl⟩
  exact hasInjRadiusAt_of_expMap_injOn P y (mul_pos hiota hrho)
    (hinj P.M P.metric hcomplete0 y rho hrho hcontrol hvol')

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
