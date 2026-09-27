import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Exponential
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.PolarFramed

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential NormalCoordinates Variation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem lintegral_paramDensity_expMap_le_of_ricci_nonneg
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E} (hK : MeasurableSet K)
    (hdom : K ⊆ expDomain (I := I) g p)
    (hinj : ∀ x ∈ K, ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)))
    (hRic : ∀ x ∈ K, ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    (∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x)
      ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal (paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0) *
          (modelHaar (E := E)) K := by
  calc
    _ ≤ ∫⁻ _x in K, ENNReal.ofReal (paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0)
        ∂(modelHaar (E := E)) :=
      setLIntegral_mono' hK (fun x hx => ENNReal.ofReal_le_ofReal
        (paramDensity_expMap_le_of_ricci_nonneg (I := I) g p x (hdom hx)
          (hinj x hx) (hRic x hx)))
    _ = _ := setLIntegral_const K _

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private theorem pole_density_bridge
    (g : SmoothRiemannianMetric I M) (p : M) :
    normalChartDensity (I := I) g p 0 =
      paramDensity (I := I) g
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0 := by
  have hD := expDiffeo_mfderiv (I := I) g p
    (zero_mem_expMapDiffeo_source (I := I) g p)
  have hbase : expMapDiffeo (I := I) g p (0 : E) =
      expMap (I := I) g p (show TangentSpace I p from (0 : E)) :=
    expMapDiffeo_apply_eq (I := I) g p (zero_mem_expMapDiffeo_source (I := I) g p)
  unfold normalChartDensity paramDensity
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  simp only [paramGramMatrix_apply]
  rw [hD, hbase]

theorem lintegral_paramDensity_expMap_le_volume_preimage_normalFrame
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E} (hK : MeasurableSet K)
    (hdom : K ⊆ expDomain (I := I) g p)
    (hinj : ∀ x ∈ K, ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)))
    (hRic : ∀ x ∈ K, ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    (∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x)
      ∂(modelHaar (E := E))) ≤
      (volume : Measure E) ((normalFrame (I := I) (E := E) g p) ⁻¹' K) := by
  have h := lintegral_paramDensity_expMap_le_of_ricci_nonneg (I := I) g p hK hdom hinj hRic
  have hmeasure :
      ENNReal.ofReal (paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0) *
          (modelHaar (E := E)) K =
        (volume : Measure E) ((normalFrame (I := I) (E := E) g p) ⁻¹' K) := by
    rw [← pole_density_bridge (I := I) g p]
    change (ENNReal.ofReal (normalChartDensity (I := I) g p 0) •
      modelHaar (E := E)) K = _
    rw [normalHaar_eq (I := I) g p]
    let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
    exact Measure.map_apply L.continuous.measurable hK
  exact h.trans_eq hmeasure

end InnerProduct

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
