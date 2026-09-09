import DifferentialGeometry.Analysis.Heat.Kernel.Conformal
import DifferentialGeometry.Analysis.Heat.Parametrix.WeightedDiagonalAsymptotics

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Integral

open DifferentialGeometry.Integral.Measure
open DivergenceTheorem
open Analysis.HeatEquation
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_inner_gradientFun_metricScalarAt_eq_zero_of_conformal_of_local_heatKernel_bound
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank ℝ E = 2)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) {T : ℝ} (hT : 0 < T)
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ x ∈ U,
        |heatKernel g t x x - 1 / (4 * Real.pi * t) -
          Geometry.Curvature.metricScalarAt g x / (24 * Real.pi)| ≤ t * C) :
    (∫ x, g.inner x (gradientFun g (Geometry.Curvature.metricScalarAt g) x) (X x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hdiv : Integrable (divergenceG g X) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      (divergence_g_contMDiff g X).continuous (HasCompactSupport.of_compactSpace _)
  have hzero {t : ℝ} (ht : 0 < t) :
      (∫ x, divergenceG g X x * (heatKernel g t x x - 1 / (4 * Real.pi * t)) ∂μ) = 0 := by
    have hkernel : Continuous (fun x => heatKernel g t x x) :=
      (continuousOn_heatKernel g).comp_continuous
        (continuous_const.prodMk (continuous_id.prodMk continuous_id))
        (fun _ => ⟨ht, mem_univ _⟩)
    have hprod : Integrable (fun x => divergenceG g X x * heatKernel g t x x) μ :=
      Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
        ((divergence_g_contMDiff g X).continuous.mul hkernel)
        (HasCompactSupport.of_compactSpace _)
    simp_rw [mul_sub]
    rw [integral_sub hprod (hdiv.mul_const _), integral_mul_const,
      integral_divergence_mul_heatKernel_diagonal_eq_zero_of_conformal hn g X hX ht,
      integral_divergence_eq_zero_of_compact g X, zero_mul, sub_zero]
  have hlim := tendsto_integral_mul_heatKernel_diagonal_sub_leading_of_local_bound
    (g := g) (T := T) hT hlocal hdiv
  have hzlim : Tendsto (fun t => ∫ x, divergenceG g X x *
      (heatKernel g t x x - 1 / (4 * Real.pi * t)) ∂μ) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hzero ht).symm
  have hpair : (∫ x, divergenceG g X x * Geometry.Curvature.metricScalarAt g x ∂μ) = 0 := by
    have h := tendsto_nhds_unique hlim hzlim
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  have hibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence g
    (Geometry.Curvature.metricScalar_smooth g) X (HasCompactSupport.of_compactSpace X)
  simp_rw [inner_gradientFun]
  change (∫ x, tangentSectionAction X (Geometry.Curvature.metricScalarAt g) x ∂μ) = 0
  rw [hibp]
  have hpair' : (∫ x, Geometry.Curvature.metricScalarAt g x * divergenceG g X x ∂μ) = 0 := by
    simpa only [mul_comm] using hpair
  rw [hpair', neg_zero]

end DifferentialGeometry.Integral
