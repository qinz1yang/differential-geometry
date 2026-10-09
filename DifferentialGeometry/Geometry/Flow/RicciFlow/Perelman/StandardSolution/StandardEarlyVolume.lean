import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialVolumeLower
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem standard_uniform_early_ball_volume_lower :
    Nonempty StandardSolution ∧ ∃ delta kappa : ℝ, 0 < delta ∧ 0 < kappa ∧
      ENNReal.ofReal delta < uniformStandardLifetime ∧
      ∀ S : StandardSolution, ∀ t ∈ Icc (0 : ℝ) delta,
        t ∈ S.val.domain ∧ ∀ x : E3, ∀ r : ℝ, 0 < r → r ≤ 1 →
          ENNReal.ofReal (kappa * r ^ 3) ≤
            riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric t)
              {y | riemannianEDistOf (S.val.metric t) x y < ENNReal.ofReal r} := by
  obtain ⟨alpha, halpha⟩ := exists_uniform_standard_lifetime
  let delta := alpha / 2
  have hdelta : 0 < delta := half_pos halpha.1
  have hdeltaLife : ENNReal.ofReal delta < uniformStandardLifetime :=
    ((ENNReal.ofReal_lt_ofReal_iff halpha.1).mpr (half_lt_self halpha.1)).trans_le
      (le_uniformStandardLifetime alpha halpha)
  obtain ⟨Lambda, hLambda, hmetric⟩ :=
    uniformStandardLifetime_metricComparison delta hdelta.le hdeltaLife
  obtain ⟨r0, hr0, hball⟩ := standard_initial_ball_volume_lower
  have hLambdaPos : 0 < Lambda := lt_of_lt_of_le (by norm_num) hLambda
  have hsqrt : 0 < Real.sqrt Lambda := Real.sqrt_pos.mpr hLambdaPos
  let beta := min (1 : ℝ) (min r0 (1 / Real.sqrt Lambda))
  let c0 := intrinsicBallVolumeCoeff 3
  let v := Real.sqrt (Lambda ^ 3)
  let kappa := c0 * beta ^ 3 / v
  have hbeta : 0 < beta :=
    lt_min (by norm_num) (lt_min hr0 (one_div_pos.mpr hsqrt))
  have hbetaR : beta ≤ r0 := (min_le_right _ _).trans (min_le_left _ _)
  have hbetaSqrt : beta ≤ 1 / Real.sqrt Lambda :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbetaScale : Real.sqrt Lambda * beta ≤ 1 := by
    calc
      Real.sqrt Lambda * beta = beta * Real.sqrt Lambda := mul_comm _ _
      _ ≤ 1 := (le_div_iff₀ hsqrt).mp hbetaSqrt
  have hc0 : 0 < c0 := intrinsicBallVolumeCoeff_pos 3
  have hv : 0 < v := Real.sqrt_pos.mpr (pow_pos hLambdaPos 3)
  have hkappa : 0 < kappa := div_pos (mul_pos hc0 (pow_pos hbeta 3)) hv
  refine ⟨standard_solution_nonempty, delta, kappa, hdelta, hkappa, hdeltaLife, ?_⟩
  intro S t ht
  obtain ⟨hdom, hquadratic⟩ := hmetric S t ht
  refine ⟨hdom, ?_⟩
  intro x r hr hr1
  have hbetaRad : 0 < beta * r := mul_pos hbeta hr
  have hbetaRadR : beta * r ≤ r0 := by
    calc
      beta * r ≤ beta * 1 := mul_le_mul_of_nonneg_left hr1 hbeta.le
      _ = beta := mul_one _
      _ ≤ r0 := hbetaR
  have hpair (p : E3) (w : TangentSpace (𝓡 3) p) :
      Lambda⁻¹ * (S.val.metric 0).inner p w w ≤ (S.val.metric t).inner p w w ∧
        (S.val.metric t).inner p w w ≤ Lambda * (S.val.metric 0).inner p w w := by
    simpa only [S.val.initial] using hquadratic p w
  let U : Set E3 :=
    {y | riemannianEDistOf (S.val.metric 0) x y < ENNReal.ofReal (beta * r)}
  let V : Set E3 :=
    {y | riemannianEDistOf (S.val.metric t) x y < ENNReal.ofReal r}
  have hU : MeasurableSet U := by
    have hd : Continuous (fun y : E3 ↦ riemannianEDistOf (S.val.metric 0) x y) := by
      simpa only [riemannianEDistOf] using continuous_riemannianEDist (S.val.metric 0) x
    exact (isOpen_lt hd continuous_const).measurableSet
  have hUV : U ⊆ V := by
    intro y hy
    have hd := edistOf_le_of_quad (S.val.metric 0) (S.val.metric t) hLambdaPos
      (fun p w ↦ (hpair p w).2) x y
    change riemannianEDistOf (S.val.metric 0) x y < ENNReal.ofReal (beta * r) at hy
    change riemannianEDistOf (S.val.metric t) x y < ENNReal.ofReal r
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt Lambda) * riemannianEDistOf (S.val.metric 0) x y := hd
      _ < ENNReal.ofReal (Real.sqrt Lambda) * ENNReal.ofReal (beta * r) :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsqrt).ne' ENNReal.ofReal_ne_top hy
      _ = ENNReal.ofReal (Real.sqrt Lambda * (beta * r)) :=
        (ENNReal.ofReal_mul hsqrt.le).symm
      _ ≤ ENNReal.ofReal r := by
        apply ENNReal.ofReal_le_ofReal
        calc
          Real.sqrt Lambda * (beta * r) = (Real.sqrt Lambda * beta) * r := by ring
          _ ≤ 1 * r := mul_le_mul_of_nonneg_right hbetaScale hr.le
          _ = r := one_mul _
  have hreverse (p : E3) (w : TangentSpace (𝓡 3) p) :
      (S.val.metric 0).inner p w w ≤ Lambda * (S.val.metric t).inner p w w := by
    calc
      (S.val.metric 0).inner p w w =
          Lambda * (Lambda⁻¹ * (S.val.metric 0).inner p w w) := by
        rw [← mul_assoc, mul_inv_cancel₀ hLambdaPos.ne', one_mul]
      _ ≤ Lambda * (S.val.metric t).inner p w w :=
        mul_le_mul_of_nonneg_left (hpair p w).1 hLambdaPos.le
  have hmove : riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric 0) U ≤
      ENNReal.ofReal v * riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric t) U := by
    have h := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
      (S.val.metric t) (S.val.metric 0) hLambdaPos hU (fun p _hp w ↦ hreverse p w)
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using h
  have hinit : ENNReal.ofReal (c0 * (beta * r) ^ 3) ≤
      riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric 0) U :=
    hball S.val x (beta * r) hbetaRad hbetaRadR
  have htotal : ENNReal.ofReal (c0 * (beta * r) ^ 3) ≤
      ENNReal.ofReal v * riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric t) V :=
    (hinit.trans hmove).trans (mul_le_mul' le_rfl (measure_mono hUV))
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr hv).ne' ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal v * ENNReal.ofReal (kappa * r ^ 3) =
        ENNReal.ofReal (c0 * (beta * r) ^ 3) := by
      rw [← ENNReal.ofReal_mul hv.le]
      apply congrArg ENNReal.ofReal
      calc
        v * (kappa * r ^ 3) = (v * v⁻¹) * (c0 * beta ^ 3 * r ^ 3) := by
          dsimp only [kappa]
          ring
        _ = c0 * (beta * r) ^ 3 := by
          simp only [mul_inv_cancel₀ hv.ne', one_mul, mul_pow, mul_assoc]
    _ ≤ ENNReal.ofReal v * riemannianVolumeMeasure (I := 𝓡 3) (M := E3) (S.val.metric t) V :=
      htotal

end DifferentialGeometry.PDE.RicciFlow

end
