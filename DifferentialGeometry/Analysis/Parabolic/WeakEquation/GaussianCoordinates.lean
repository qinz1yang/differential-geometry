import DifferentialGeometry.Geometry.Operator.Gradient.QuadraticForm
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "V" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem chartGradientBilin_fderiv_toEuclidean
    (g : SmoothRiemannianMetric I M) (α : M) (f : E → ℝ) (φ : V → ℝ) (y : E) :
    chartGradientBilin g α ((extChartAt I α).symm y)
      (fderiv ℝ f y) (fderiv ℝ (φ ∘ toEuclidean (E := E)) y) =
        ∑ i, ∑ j, invGramOnEuclid g α i j ((toEuclidean (E := E)) y) *
          fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
  have hf (j : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
          (EuclideanSpace.single j 1) = fderiv ℝ f y (chartModelBasis E j) := by
    rw [(toEuclidean (E := E)).symm.comp_right_fderiv]
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, chartModelBasis_apply]
  have hφ (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (φ ∘ toEuclidean (E := E)) y (chartModelBasis E i) =
        fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
    rw [(toEuclidean (E := E)).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      chartModelBasis_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [chartGradientBilin_apply]
  simp only [hf, hφ, invGramOnEuclid, ContinuousLinearEquiv.symm_apply_apply]

theorem integral_chartGaussianResidual_eq_toEuclidean
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    (f u : ℝ × E → ℝ) (Ω : Set V) (a b : ℝ) (φ : ℝ × V → ℝ) :
    let ψ : ℝ × E → ℝ := fun z => φ (z.1, (toEuclidean (E := E)) z.2)
    let fV : ℝ × V → ℝ := fun q => f (q.1, (toEuclidean (E := E)).symm q.2)
    let uV : ℝ × V → ℝ := fun q => u (q.1, (toEuclidean (E := E)).symm q.2)
    (∫ z, chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(volume.restrict (Ioc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) =
      ∫ q, densityOnEuclid (g q.1) α q.2 * uV q *
        (deriv (fun t => φ (t, q.2)) q.1 +
          ∑ i, ∑ j, invGramOnEuclid (g q.1) α i j q.2 *
            fderiv ℝ (fun y => fV (q.1, y)) q.2 (EuclideanSpace.single j 1) *
            fderiv ℝ (fun y => φ (q.1, y)) q.2 (EuclideanSpace.single i 1))
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω) := by
  intro ψ fV uV
  let T : (ℝ × E) ≃L[ℝ] (ℝ × V) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
  have hspace : MeasurePreserving (toEuclidean (E := E))
      (modelHaar (E := E)) volume :=
    ⟨(toEuclidean (E := E)).continuous.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have hspaceR := hspace.restrict_preimage_emb
    (toEuclidean (E := E)).toHomeomorph.measurableEmbedding Ω
  have hT : MeasurePreserving T
      ((volume.restrict (Icc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω)))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
    (MeasurePreserving.id (volume.restrict (Icc a b))).prod hspaceR
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [← hT.integral_comp T.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hgrad := chartGradientBilin_fderiv_toEuclidean (g z.1) α
    (fun y => f (z.1, y)) (fun y => φ (z.1, y)) z.2
  simpa only [T, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    densityOnEuclid, ContinuousLinearEquiv.symm_apply_apply,
    ψ, fV, uV, Function.comp_def] using
      congrArg (fun r => chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
        (deriv (fun t => φ (t, (toEuclidean (E := E)) z.2)) z.1 + r)) hgrad

end DifferentialGeometry.Analysis.Parabolic
