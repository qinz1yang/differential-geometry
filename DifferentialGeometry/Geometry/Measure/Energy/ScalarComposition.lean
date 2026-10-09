import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

section

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Pointwise

variable [T2Space (TangentBundle 𝓘(ℝ, E) M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem norm_fderiv_le_mul_sqrt_metric_of_edist_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ}
    {z : ℂ} {K : ℝ≥0}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hf : DifferentiableAt ℝ f z)
    (hbound : ∀ w, edist (f z) (f w) ≤ (K : ℝ≥0∞) * riemannianEDistOf g (U z) (U w))
    (v : ℂ) :
    ‖fderiv ℝ f z v‖ ≤ K * Real.sqrt (g.inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) := by
  let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
  have hmetric (x y : ℝ) : riemannianEDistOf (euclideanMetric (E := ℝ)) x y = edist x y := by
    exact (IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) x y).symm
  have h := metric_differential_le_of_edist_le g (euclideanMetric (E := ℝ))
    (L := K) hU hf.mdifferentiableAt (fun w => by
      rw [hmetric]
      exact hbound w) v
  rw [mfderiv_eq_fderiv] at h
  change Real.sqrt ((fderiv ℝ f z v) * (fderiv ℝ f z v)) ≤ _ at h
  simpa only [← sq, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, diskMapPartial] using h

theorem fderiv_partials_sq_le_mul_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ}
    {z : ℂ} {K : ℝ≥0}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hf : DifferentiableAt ℝ f z)
    (hbound : ∀ w, edist (f z) (f w) ≤ (K : ℝ≥0∞) * riemannianEDistOf g (U z) (U w)) :
    (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 ≤
      2 * (K : ℝ) ^ 2 * diskMapEnergyDensity g U z := by
  have hsq (v : ℂ) : (fderiv ℝ f z v) ^ 2 ≤
      (K : ℝ) ^ 2 * g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z v) := by
    have h := norm_fderiv_le_mul_sqrt_metric_of_edist_le g hU hf hbound v
    have hh := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _))).mpr h
    rw [mul_pow, Real.sq_sqrt (metric_inner_self_nonneg _ _ _)] at hh
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  calc
    _ ≤ (K : ℝ) ^ 2 * g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        (K : ℝ) ^ 2 * g.inner (U z)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) :=
      add_le_add (hsq 1) (hsq Complex.I)
    _ = _ := by unfold diskMapEnergyDensity; ring

end Pointwise

variable [T3Space M]

theorem ae_fderiv_partials_sq_le_mul_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ}
    {C K : ℝ≥0}
    (hU : ∀ z w, riemannianEDistOf g (U z) (U w) ≤ (C : ℝ≥0∞) * edist z w)
    (hbound : ∀ z w, edist (f z) (f w) ≤ (K : ℝ≥0∞) * riemannianEDistOf g (U z) (U w)) :
    ∀ᵐ z ∂volume, (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 ≤
      2 * (K : ℝ) ^ 2 * diskMapEnergyDensity g U z := by
  have hf : LipschitzWith (K * C) f := by
    intro z w
    calc
      edist (f z) (f w) ≤ (K : ℝ≥0∞) * riemannianEDistOf g (U z) (U w) := hbound z w
      _ ≤ (K : ℝ≥0∞) * ((C : ℝ≥0∞) * edist z w) := mul_le_mul_right (hU z w) _
      _ = ((K * C : ℝ≥0) : ℝ≥0∞) * edist z w := by
        rw [ENNReal.coe_mul, mul_assoc]
  have hmd : ∀ᵐ z ∂(volume : Measure ℂ), MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    ae_mdifferentiableAt_of_metric_lipschitz g hU
  filter_upwards [hmd, hf.ae_differentiableAt] with z hz hzf
  exact fderiv_partials_sq_le_mul_diskMapEnergyDensity g hz hzf (hbound z)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_norm_fderiv_sq_le_mul_disk_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {f : ℂ → ℝ} {L K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hbound : ∀ z w, edist (f z) (f w) ≤
      (K : ℝ≥0∞) * riemannianEDistOf g (diskExtension u z) (diskExtension u w)) :
    (∫ z in closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 *
        ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  have hU := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzWith (K * L) f := by
    intro z w
    calc
      edist (f z) (f w) ≤ (K : ℝ≥0∞) *
          riemannianEDistOf g (diskExtension u z) (diskExtension u w) := hbound z w
      _ ≤ (K : ℝ≥0∞) * ((L : ℝ≥0∞) * edist z w) := mul_le_mul_right (hU z w) _
      _ = ((K * L : ℝ≥0) : ℝ≥0∞) * edist z w := by
        rw [ENNReal.coe_mul, mul_assoc]
  have hae := ae_fderiv_partials_sq_le_mul_diskMapEnergyDensity g hU hbound
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hfm : MemLp (fderiv ℝ f) 2 (volume.restrict (closedBall (0 : ℂ) 1)) :=
    MemLp.of_bound
      ((measurable_fderiv ℝ f).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      (K * L : ℝ≥0) (Eventually.of_forall fun z => norm_fderiv_le_of_lipschitz ℝ hf)
  have he := integrable_diskMapEnergyDensity g hu
  rw [← integral_const_mul]
  apply integral_mono_ae hfm.norm.integrable_sq (he.const_mul (2 * (K : ℝ) ^ 2))
  filter_upwards [ae_restrict_of_ae (s := closedBall (0 : ℂ) 1) hae] with z hz
  have hnorm : ‖fderiv ℝ f z‖ ^ 2 =
      (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
    simpa [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two] using
      Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ f z)
  rwa [hnorm]

end DifferentialGeometry.Geometry

end

end
