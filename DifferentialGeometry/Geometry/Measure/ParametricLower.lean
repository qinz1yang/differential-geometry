import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.PolarFramed
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped ContDiff Manifold Topology ENNReal Matrix

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem paramDensity_ge_of_inner_half
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (z : E)
    (hhalf : ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (Ψ z)
        (mfderiv 𝓘(ℝ, E) I Ψ z v) (mfderiv 𝓘(ℝ, E) I Ψ z v)) :
    Real.sqrt ((1 / 2 : ℝ) ^ Module.finrank ℝ E) *
        Real.sqrt (Matrix.of (fun i j : Fin (Module.finrank ℝ E) ↦
          inner ℝ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))).det ≤
      paramDensity (I := I) g Ψ z := by
  let D : E →L[ℝ] TangentSpace I (Ψ z) := mfderiv 𝓘(ℝ, E) I Ψ z
  let β : E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ D).comp ((g.inner (Ψ z)).comp D)
  obtain ⟨G, hG⟩ := DifferentialGeometry.Geometry.smoothMetric_of_localCoeff
    (I := 𝓘(ℝ, E)) (M := E) (fun _ ↦ β)
    (fun _ v w ↦ g.symm (Ψ z) (D v) (D w))
    (fun _ v hv ↦ by
      have hp : 0 < (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
        mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hv))
      exact hp.trans_le (hhalf v))
    (fun x₀ i j ↦ by
      refine (contMDiffOn_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (M := E) (M' := ℝ)
        (c := β (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))).congr ?_
      intro x _
      simp only [DifferentialGeometry.Geometry.frameVec, TangentBundle.symmL_model_space]
      rfl)
  have hcomp (v : TangentSpace 𝓘(ℝ, E) (0 : E)) :
      (flatModelMetric E).inner 0 v v ≤ 2 * G.inner 0 v v := by
    have hh : (1 / 2 : ℝ) * ‖(show E from v)‖ ^ 2 ≤
        β (show E from v) (show E from v) := hhalf (show E from v)
    calc
      (flatModelMetric E).inner 0 v v = ‖(show E from v)‖ ^ 2 :=
        real_inner_self_eq_norm_sq (show E from v)
      _ ≤ 2 * β (show E from v) (show E from v) := by linarith
      _ = 2 * G.inner 0 v v := congrArg (2 * ·) (hG 0 v v).symm
  have hcompare := chartDensity_le (I := 𝓘(ℝ, E)) G (flatModelMetric E)
    (by norm_num : (0 : ℝ) < 2) (0 : E)
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (0 : E)) hcomp
  have hGdensity : chartDensity (I := 𝓘(ℝ, E)) G 0 0 =
      paramDensity (I := I) g Ψ z := by
    unfold chartDensity paramDensity
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
      TangentBundle.symmL_model_space, hG, paramGramMatrix_apply]
    rfl
  have hflatDensity : chartDensity (I := 𝓘(ℝ, E)) (flatModelMetric E) 0 0 =
      Real.sqrt (Matrix.of (fun i j : Fin (Module.finrank ℝ E) ↦
        inner ℝ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))).det := by
    unfold chartDensity
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber,
      TangentBundle.symmL_model_space, Matrix.of_apply]
    rfl
  rw [hGdensity, hflatDensity] at hcompare
  have hroot : Real.sqrt ((1 / 2 : ℝ) ^ Module.finrank ℝ E) *
      Real.sqrt ((2 : ℝ) ^ Module.finrank ℝ E) = 1 := by
    rw [← Real.sqrt_mul (by positivity), ← mul_pow]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hcompare
    (Real.sqrt_nonneg ((1 / 2 : ℝ) ^ Module.finrank ℝ E))
  simpa only [← mul_assoc, hroot, one_mul] using hmul

private theorem euclidean_density_smul_modelHaar :
    ENNReal.ofReal
        (Real.sqrt (Matrix.of (fun i j : Fin (Module.finrank ℝ E) ↦
          inner ℝ (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))).det) •
        (modelHaar (E := E)) = (volume : Measure E) := by
  simpa only [framedDens_zero] using
    (framedDens_haar (I := 𝓘(ℝ, E)) (flatModelMetric E) (0 : E))

theorem riemannianVolumeMeasure_image_ge_of_inner_half
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB : MeasurableSet B) (hsource : B ⊆ Ψ.source)
    (hhalf : ∀ z ∈ B, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (Ψ z)
        (mfderiv 𝓘(ℝ, E) I Ψ z v) (mfderiv 𝓘(ℝ, E) I Ψ z v)) :
    ENNReal.ofReal (Real.sqrt ((1 / 2 : ℝ) ^ Module.finrank ℝ E)) *
        (volume : Measure E) B ≤
      riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) := by
  have hparam := param_vol_ge (I := I) g Ψ hB hsource
    (fun z hz ↦ paramDensity_ge_of_inner_half g Ψ z (hhalf z hz))
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc] at hparam
  have hhaar := congrArg (fun μ : Measure E ↦ μ B)
    (euclidean_density_smul_modelHaar (E := E))
  simp only [Measure.smul_apply, smul_eq_mul] at hhaar
  rw [hhaar] at hparam
  exact hparam

end DifferentialGeometry.Geometry.Measure

end
