import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff

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

theorem volume_lower_bound_of_rescaled_distance_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q x : F.M) {tau A D r : ℝ} (htau : 0 < tau) (hD : 0 ≤ D)
    (hbase : redLength F.S 0 p q tau ≤ A)
    (hdist : riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))) q x ≤
      ENNReal.ofReal D) (hr : 0 < r) (hr1 : r ≤ 1)
    (hscale : r ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 *
      (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2)) ≤ 1) :
    let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := F.M) g
        {y : F.M | riemannianEDistOf g x y < ENNReal.ofReal r} := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  have ht : -tau ∈ ancientTimeInterval.carrier := neg_nonpos.mpr htau.le
  let S := curvatureNormalizedSolution F.S (-tau) tau⁻¹ (inv_pos.mpr htau) ht
  let time : ancientTimeInterval.FlowTime := ⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩
  let B : FlowMetricBall S time := ⟨x, r, hr⟩
  let g := scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau))
  have hmetric : S.base.metric 0 = g := by
    change scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (parabolicTime (-tau) tau⁻¹ 0)) = g
    rw [parabolicTime_zero]
  have hcontrolled : B.IsSpatiallyRmControlled := by
    intro y hy
    change riemannianEDistOf (S.base.metric 0) x y < ENNReal.ofReal r at hy
    rw [hmetric] at hy
    have hqy : riemannianEDistOf g q y ≤ ENNReal.ofReal (D + 1) := by
      calc
        _ ≤ riemannianEDistOf g q x + riemannianEDistOf g x y :=
          riemannianEDistOf_triangle g q x y
        _ ≤ ENNReal.ofReal D + ENNReal.ofReal 1 :=
          add_le_add hdist (hy.le.trans (ENNReal.ofReal_le_ofReal hr1))
        _ = ENNReal.ofReal (D + 1) := (ENNReal.ofReal_add hD zero_le_one).symm
    have hbound := rmNorm_le_of_rescaled_distance_le F hF p q y htau
      (by linarith : 0 ≤ D + 1) hbase hqy
    let v := Tensor0SBundle.normSq0S (I := I) g y 4 (metricRm04At g y)
    have hv : 0 ≤ v := Tensor0SBundle.normSq0S_nonneg g y 4 _
    have hsmall : r ^ 2 * Real.sqrt v ≤ 1 :=
      (mul_le_mul_of_nonneg_left hbound (sq_nonneg r)).trans hscale
    have hsquare : (r ^ 2 * Real.sqrt v) ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        (sq_le_sq₀ (mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg v)) zero_le_one).2 hsmall
    change r ^ 4 * Tensor0SBundle.normSq0S (S.base.metric 0) y 4 (S.base.rm04 0 y) ≤ 1
    change r ^ 4 * Tensor0SBundle.normSq0S (S.base.metric 0) y 4
      (metricRm04At (S.base.metric 0) y) ≤ 1
    rw [hmetric]
    change r ^ 4 * v ≤ 1
    simpa only [mul_pow, Real.sq_sqrt hv, ← pow_mul] using hsquare
  have hnc := curvatureNormalizedSolution_noncollapsed F.S hF.carrier_eq
    (-tau) tau⁻¹ (inv_pos.mpr htau) ht kappa hF.noncollapsed time B hcontrolled
  have hvol := hnc.2
  change ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := F.M) (S.base.metric 0)
      {y : F.M | riemannianEDistOf (S.base.metric 0) x y < ENNReal.ofReal r} at hvol
  rwa [hmetric] at hvol

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
