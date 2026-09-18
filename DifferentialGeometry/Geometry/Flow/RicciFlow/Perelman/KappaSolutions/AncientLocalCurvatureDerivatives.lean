import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance topology : TopologicalSpace F.M := F.topology
private local instance charted : ChartedSpace H F.M := F.charted
private local instance smooth : IsManifold I ∞ F.M := F.smooth
private local instance t2 : T2Space F.M := F.t2
private local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem curvDerivNorm_le_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) (m : ℕ) :
    let K := 1 + (Module.finrank ℝ E : ℝ) ^ 2 *
      (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2)
    curvDerivNorm (I := I) m
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) x ≤
      shiLocalUniformBound (Module.finrank ℝ E) m K (Real.sqrt K) * K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by decide : 0 < 4) (F.S.base.rm04 t z) hz⟩
  let K := 1 + (Module.finrank ℝ E : ℝ) ^ 2 *
    (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hstart : -2 * tau ∈ ancientTimeInterval.carrier := by
    change -2 * tau ≤ 0
    nlinarith
  let J := RealTimeInterval.closedOpen (-1) (3 / 2) (by norm_num : (-1 : ℝ) < 3 / 2)
  let S : SolutionOn (I := I) (M := F.M) J :=
    (parabolicSolution F.S (-2 * tau) tau⁻¹ (inv_pos.mpr htau) hstart).timeRestrict J
  have hS : IsSolutionOn S := by
    apply isSolutionOn_timeRestrict
      (parabolicSolution_isSolutionOn F.S F.isSolution (-2 * tau) tau⁻¹
        (inv_pos.mpr htau) hstart)
    · intro s hs
      change s ∈ Set.Ico (-1 : ℝ) (3 / 2) at hs
      change -2 * tau + s / tau⁻¹ ≤ 0
      rw [div_inv_eq_mul]
      nlinarith [hs.2]
    · intro s hs
      change s ∈ Set.Ioo (-1 : ℝ) (3 / 2) at hs
      change -2 * tau + s / tau⁻¹ < 0
      rw [div_inv_eq_mul]
      nlinarith [hs.2]
  have hmetric (s : ℝ) : S.base.metric s =
      scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (tau * (s - 2))) := by
    change scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-2 * tau + s / tau⁻¹)) = _
    congr 2
    rw [div_inv_eq_mul]
    ring
  have hmetricOne : S.base.metric 1 =
      scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau)) := by
    rw [hmetric]
    congr 2
    ring
  have hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0) := by
    rw [hmetric]
    apply RiemannianMetricComplete.of_lower
      (g := F.S.base.metric (tau * (0 - 2)))
      ⟨hF.complete _ (by change tau * (0 - 2) ≤ 0; nlinarith)⟩
      (inv_pos.mpr htau)
    intro y v
    exact le_rfl
  have hball : IsCompact {y : F.M | riemannianEDistOf (S.base.metric 0) x y ≤
      ENNReal.ofReal (Real.sqrt K / Real.sqrt K)} := by
    exact hcomplete.closedEBall_isCompact x _
  have hcurv : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y : F.M,
      riemannianEDistOf (S.base.metric 0) x y ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K) →
      nablaKRm04NormSqIntrinsic S 0 s y ≤ K ^ 2 := by
    intro s hs y hy
    have hxy : riemannianEDistOf
        (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) x y ≤
        ENNReal.ofReal 1 := by
      rw [div_self (ne_of_gt (Real.sqrt_pos.mpr hK))] at hy
      refine le_trans ?_ hy
      rw [hmetric, edistOf_scale, edistOf_scale]
      apply mul_le_mul' le_rfl
      apply edistOf_mono
      intro z v
      exact ancientModel_metric_inner_antitoneOn F hF z v
        (by change tau * (0 - 2) ≤ 0; nlinarith)
        (neg_nonpos.mpr htau.le) (by nlinarith)
    have hqy : riemannianEDistOf
        (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q y ≤
        ENNReal.ofReal (D + 1) := by
      calc
        _ ≤ riemannianEDistOf _ q x + riemannianEDistOf _ x y :=
          riemannianEDistOf_triangle _ q x y
        _ ≤ ENNReal.ofReal D + ENNReal.ofReal 1 := add_le_add hdist hxy
        _ = ENNReal.ofReal (D + 1) := (ENNReal.ofReal_add hD zero_le_one).symm
    have htime : tau * (s - 2) ≤ -tau := by nlinarith [hs.2]
    have hbound := rmNorm_le_on_past_of_rescaled_distance_le F hF p q y htau
      (by linarith : 0 ≤ D + 1) hbase hqy htime
    have hnorm : Real.sqrt (nablaKRm04NormSqIntrinsic S 0 s y) ≤ K := by
      apply le_trans ?_ (show (Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2) ≤ K by dsimp only [K]; linarith)
      rw [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero]
      change Real.sqrt (Tensor0SBundle.normSq0S (S.base.metric s) y 4
        (metricRm04At (S.base.metric s) y)) ≤ _
      rw [hmetric]
      exact hbound
    nlinarith [Real.sq_sqrt (nablaKRm04NormSqIntrinsic_nonneg S 0 s y),
      Real.sqrt_nonneg (nablaKRm04NormSqIntrinsic S 0 s y)]
  have hshi := shi_local_all_orders_curvature_scale_of_solution_uniform S hS x
    (by norm_num : (-1 : ℝ) < 0) hK (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 3 / 2) (Real.sqrt_pos.mpr hK)
    (by change (0 : ℝ) ∈ Set.Ico (-1) (3 / 2); norm_num) hball hcurv
    m 1 (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 1) x (by rw [riemannianEDistOf_self]; exact zero_le)
  change curvDerivNorm (I := I) m _ x ≤ shiLocalUniformBound _ m K (Real.sqrt K) * K
  rw [← hmetricOne, curvDerivNorm, curvNormSq_eq]
  simpa only [mul_one, Real.sqrt_one, one_pow, div_one] using hshi.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
