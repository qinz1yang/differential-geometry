import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterGap_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterDefect_O7
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

/-!
# CH12-O7 / C1, group L (1): the realisation inequality

`deficit_ge_of_pullback_O7`: if `f : W → X` is an injective local diffeomorphism into a compact
stage with `R ≥ -3/(2(T+c))`, and `h = t⁻¹ f^* m`, then a scalar lower bound
`κ ≤ R_h + 3t/(2(T+c))` on `B ⊆ W` gives `√t κ vol_h(B) ≤ 𝒟(m)` (the deficit at time `T`).
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section Realization

variable {W : Type*} [TopologicalSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold ThreeModel ∞ W] [T2Space W] [SigmaCompactSpace W]

private local instance measW_O7 : MeasurableSpace W := borel W
private local instance borelW_O7 : BorelSpace W := ⟨rfl⟩

/-- **Realisation inequality** (static). -/
theorem deficit_ge_of_pullback_O7 {X : OrientedThreeStage.{u}} (m : X.Metric) {c T t : ℝ}
    (hTc : 0 < T + c) (ht : 0 < t)
    (hRlow : ∀ x, -(3 / (2 * (T + c))) ≤ metricScalarAt m x)
    (f : W → X.Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hinj : Function.Injective f) {B : Set W} (hB : MeasurableSet B) {κ : ℝ} (hκ : 0 ≤ κ)
    (hκB : ∀ y ∈ B, κ ≤ metricScalarAt (scaleMetric t⁻¹ (inv_pos.mpr ht)
      (localPullMetric m f hf)) y + 3 * t / (2 * (T + c))) :
    Real.sqrt t * κ * (riemannianVolumeMeasure ThreeModel W (scaleMetric t⁻¹ (inv_pos.mpr ht)
      (localPullMetric m f hf)) B).toReal ≤ metricDeficit_O7 m c T := by
  let μ := riemannianVolumeMeasure ThreeModel X.Carrier m
  have : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel) (M := X.Carrier) _
  set k : ℝ := 3 / (2 * (T + c)) with hk
  have hcont : Continuous (metricScalarAt m) := (metricScalar_smooth m).continuous
  have hint : Integrable (metricScalarAt m) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdef : metricDeficit_O7 m c T = ∫ x, (metricScalarAt m x + k) ∂μ := by
    unfold metricDeficit_O7
    rw [integral_add hint (integrable_const _), integral_const, smul_eq_mul, Measure.real_def,
      mul_comm]
  -- the image region
  have hopen : Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have hfB : MeasurableSet (f '' B) := hopen.measurableEmbedding.measurableSet_image.mpr hB
  have hnonneg : ∀ x, 0 ≤ metricScalarAt m x + k := fun x => by linarith [hRlow x]
  have hint2 : Integrable (fun x => metricScalarAt m x + k) μ := hint.add (integrable_const _)
  have hsub : ∫ x in f '' B, (metricScalarAt m x + k) ∂μ ≤ ∫ x, (metricScalarAt m x + k) ∂μ :=
    setIntegral_le_integral hint2 (Eventually.of_forall hnonneg)
  -- pointwise lower bound on the image
  have hlow : ∀ x ∈ f '' B, κ / t ≤ metricScalarAt m x + k := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hκB y hy
    rw [metricScalarAt_scaleMetric, inv_inv, metricScalarAt_localPull] at h1
    rw [div_le_iff₀ ht]
    have : 3 * t / (2 * (T + c)) = k * t := by rw [hk]; ring
    rw [this] at h1
    linarith
  have hconst : (κ / t) * (μ (f '' B)).toReal ≤ ∫ x in f '' B, (metricScalarAt m x + k) ∂μ := by
    have hfin : μ (f '' B) ≠ ⊤ := measure_ne_top _ _
    have := setIntegral_ge_of_const_le_real hfB hfin hlow
      (hint2.integrableOn)
    simpa [Measure.real_def, mul_comm] using this
  -- volumes
  have hvol : μ (f '' B) = riemannianVolumeMeasure ThreeModel W (localPullMetric m f hf) B :=
    (Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      (localPullMetric m f hf) m f hf hinj (localPullMetric_inner m f hf) hB).symm
  have hscale := volume_scale_apply (I := ThreeModel) (M := W) t⁻¹ (inv_pos.mpr ht)
    (localPullMetric m f hf) B
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hscale
  have hsqrt : Real.sqrt t⁻¹ ^ 3 * t ^ (3 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_inv, inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
    rw [inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne']
  have hV : (riemannianVolumeMeasure ThreeModel W (scaleMetric t⁻¹ (inv_pos.mpr ht)
      (localPullMetric m f hf)) B).toReal = Real.sqrt t⁻¹ ^ 3 * (μ (f '' B)).toReal := by
    rw [hscale, hvol, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal
      (Real.sqrt_nonneg _)]
  rw [hdef, hV]
  have hmain : Real.sqrt t * κ * (Real.sqrt t⁻¹ ^ 3 * (μ (f '' B)).toReal) =
      (κ / t) * (μ (f '' B)).toReal := by
    have hst : Real.sqrt t * Real.sqrt t⁻¹ ^ 3 = 1 / t := by
      have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      rw [Real.sqrt_inv, inv_pow]
      conv_rhs => rw [← hs]
      field_simp
    calc Real.sqrt t * κ * (Real.sqrt t⁻¹ ^ 3 * (μ (f '' B)).toReal)
        = (Real.sqrt t * Real.sqrt t⁻¹ ^ 3) * κ * (μ (f '' B)).toReal := by ring
      _ = _ := by rw [hst]; ring
  rw [hmain]
  exact hconst.trans hsub

end Realization

end GC.LongTime.Ch12
