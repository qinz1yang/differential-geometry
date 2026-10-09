import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Bundle.TangentOpenRestriction
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Analysis.InnerProductSpace.PiL2

/- Scratch only. This identifies the canonical volume of the actual induced
metric with the original complex-plane measure weighted by exactly one actual
disk density. The arbitrary chart-basis Haar normalization is canceled using
the Euclidean reference metric and Complex.orthonormalBasisOneI. -/

set_option autoImplicit false
noncomputable section

open Bundle Manifold MeasureTheory Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

private local instance (N : Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : Opens ℂ) : SigmaCompactSpace N := by
  let : LocallyCompactSpace N := N.isOpen.locallyCompactSpace
  infer_instance

private theorem symmL_open_complex (N : Opens ℂ) (z₀ z : N) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) z₀).symmL ℝ z =
      (1 : ℂ →L[ℝ] ℂ) := by
  have hz : z ∈ (chartAt ℂ z₀).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact mem_univ _
  rw [TangentBundle.symmL_trivializationAt_eq_core hz,
    tangentCoordChange_opens z₀ z z (mem_univ _), TangentBundle.coordChange_model_space]

private theorem normalized_chartDensity_eq_complex_jacobian
    (N : Opens ℂ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) (z : N) :
    (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := ℂ)) volume : ℝ) *
        chartDensity h z z = tangentTwoJacobian h (x := z) (1 : ℂ) Complex.I := by
  have heq := modelHaarScalarFactor_mul_chartDensity h z z Complex.orthonormalBasisOneI
  rw [symmL_open_complex] at heq
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := h.inner z
  change (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := ℂ)) volume : ℝ) *
      chartDensity h z z = Real.sqrt (Matrix.of (fun i j : Fin 2 =>
        B (Complex.orthonormalBasisOneI i) (Complex.orthonormalBasisOneI j))).det at heq
  have hsymm : B Complex.I (1 : ℂ) = B (1 : ℂ) Complex.I := h.symm z Complex.I (1 : ℂ)
  change (MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := ℂ)) volume : ℝ) *
      chartDensity h z z = Real.sqrt (B 1 1 * B Complex.I Complex.I - B 1 Complex.I ^ 2)
  simpa [Matrix.det_fin_two, Complex.coe_orthonormalBasisOneI, hsymm, pow_two] using heq

private theorem volumeDensity_eq_complex_jacobian
    (N : Opens ℂ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) (z : N) :
    riemannianVolumeDensity ((euclideanMetric (E := ℂ)).restrictOpen N) h z =
      tangentTwoJacobian h (x := z) (1 : ℂ) Complex.I := by
  let q := (euclideanMetric (E := ℂ)).restrictOpen N
  have hq : tangentTwoJacobian q (x := z) (1 : ℂ) Complex.I = 1 := by
    change Real.sqrt (inner ℝ (1 : ℂ) (1 : ℂ) * inner ℝ Complex.I Complex.I -
      inner ℝ (1 : ℂ) Complex.I ^ 2) = 1
    simp [real_inner_eq_re_inner]
  have hqnorm := normalized_chartDensity_eq_complex_jacobian N q z
  rw [hq] at hqnorm
  have hhnorm := normalized_chartDensity_eq_complex_jacobian N h z
  rw [riemannianVolumeDensity_apply_of_mem_chart_source q h z (mem_chart_source ℂ z)]
  apply (div_eq_iff (ne_of_gt (chartDensity_pos q z (mem_chart_source ℂ z)))).2
  calc
    chartDensity h z z = chartDensity h z z *
        ((MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := ℂ)) volume : ℝ) *
          chartDensity q z z) := by rw [hqnorm, mul_one]
    _ = ((MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := ℂ)) volume : ℝ) *
        chartDensity h z z) * chartDensity q z z := by ring
    _ = _ := by rw [hhnorm]

private theorem euclidean_open_volume_eq_comap (N : Opens ℂ) :
    riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N)
        ((euclideanMetric (E := ℂ)).restrictOpen N) =
      MeasureTheory.Measure.comap (Subtype.val : N → ℂ) (volume : MeasureTheory.Measure ℂ) := by
  have hval : MeasurableEmbedding (Subtype.val : N → ℂ) :=
    N.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel N)
  apply hval.map_injective
  rw [DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_restrictOpen,
    riemannianVolumeMeasure_euclideanMetric, hval.map_comap, Subtype.range_coe]

private theorem volume_eq_complex_jacobian_withDensity
    (N : Opens ℂ) (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) :
    riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) h =
      (MeasureTheory.Measure.comap (Subtype.val : N → ℂ) (volume : MeasureTheory.Measure ℂ)).withDensity
        (fun z => ENNReal.ofReal (tangentTwoJacobian h (x := z) (1 : ℂ) Complex.I)) := by
  rw [riemannianVolumeMeasure_eq_withDensity ((euclideanMetric (E := ℂ)).restrictOpen N) h,
    euclidean_open_volume_eq_comap]
  congr 1
  funext z
  rw [volumeDensity_eq_complex_jacobian]

/-- Canonical volume of the same actual induced metric on an open complex
domain. This theorem uses the original area density based on `1, I`; it has
no measure-normalization, conformality, stability, or Hessian premise. -/
theorem riemannianVolumeMeasure_induced_complex_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (N : Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun z : N => U z))
    (hi : ∀ z : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z)) :
    riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N)
        (g.pullback (fun z : N => U z) hU hi) =
      (MeasureTheory.Measure.comap (Subtype.val : N → ℂ) (volume : MeasureTheory.Measure ℂ)).withDensity
        (fun z => ENNReal.ofReal (riemannianAreaDensity g U z)) := by
  rw [volume_eq_complex_jacobian_withDensity]
  congr 1
  funext z
  congr 1
  let L : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
  let P : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z : ℂ)
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  have hLP : L = P := DifferentialGeometry.mfderiv_restrict_open
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z
  change Real.sqrt (B (L 1) (L 1) * B (L Complex.I) (L Complex.I) -
      B (L 1) (L Complex.I) ^ 2) =
    Real.sqrt (B (P 1) (P 1) * B (P Complex.I) (P Complex.I) -
      B (P 1) (P Complex.I) ^ 2)
  rw [hLP]

end DifferentialGeometry.Geometry
