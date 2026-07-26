import DifferentialGeometry.Analysis.Integration.Measure.PolarEvaluation
import DifferentialGeometry.Geometry.Comparison.Volume.BishopRadial
import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure

/-!
# Polar transfer for normal-coordinate volume

This file transfers the normal-coordinate volume formula to the generalized
polar decomposition of model Haar measure. It does not yet impose a cut-time
domain or identify the polar integrand with a transverse Jacobi density.
-/

noncomputable section

open Filter Metric Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [Nontrivial E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [Nontrivial E] in
private lemma smul_mem_ball
    {R : ℝ} (hR : 0 < R) (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)) :
    r.1 • u.1 ∈ ball (0 : E) R ↔ r ∈ Iio (⟨R, hR⟩ : Ioi (0 : ℝ)) := by
  have hu : ‖u.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using u.2
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg r.2.le, hu,
    mul_one]
  rfl

/-- The Riemannian volume of a measurable normal-coordinate image is the
iterated polar integral of the normal-coordinate density. -/
theorem normalImage_polar
    (g : SmoothRiemannianMetric I M) (p : M)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ (expMapDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (expMapDiffeo (I := I) g p '' B) =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ),
          B.indicator
            (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let Ψ := expMapDiffeo (I := I) g p
  let F : E → ℝ≥0∞ :=
    B.indicator (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
  have hcont : ContinuousOn (normalChartDensity (I := I) g p) Ψ.source := by
    simpa only [normalChartDensity, Ψ] using
      paramDensity_contOn (I := I) g Ψ
  have hF : AEMeasurable F (modelHaar (E := E)) := by
    apply (aemeasurable_indicator_iff hB_meas).mpr
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hcont.mono hB_source).aemeasurable hB_meas)
  calc
    riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) =
        ∫⁻ w in B, ENNReal.ofReal (normalChartDensity (I := I) g p w)
          ∂(modelHaar (E := E)) := by
      simpa only [Ψ, normalChartDensity] using
        riemannianVolumeMeasure_image_param_eq (I := I) (M := M) g Ψ
          hB_meas hB_source
    _ = ∫⁻ w, F w ∂(modelHaar (E := E)) := by
      rw [lintegral_indicator hB_meas]
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ), F (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(modelHaar (E := E)).toSphere :=
      lintegral_polar (modelHaar (E := E)) F hF
    _ = ∫⁻ u : sphere (0 : E) 1,
          ∫⁻ r : Ioi (0 : ℝ),
            B.indicator
              (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
              (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(modelHaar (E := E)).toSphere := by
      rfl

/-- Polar volume formula for a model ball contained in the selected normal
source. -/
theorem normalBall_polar
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    (hsource : ball (0 : E) R ⊆ (expMapDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (expMapDiffeo (I := I) g p '' ball (0 : E) R) =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ) in Iio (⟨R, hR⟩ : Ioi (0 : ℝ)),
          ENNReal.ofReal (normalChartDensity (I := I) g p (r.1 • u.1))
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  rw [normalImage_polar (I := I) g p measurableSet_ball hsource]
  apply lintegral_congr
  intro u
  rw [← lintegral_indicator measurableSet_Iio]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Iio (⟨R, hR⟩ : Ioi (0 : ℝ))
  · have hb : r.1 • u.1 ∈ ball (0 : E) R :=
      (smul_mem_ball (E := E) hR u r).2 hr
    simp only [Set.indicator_of_mem hr, Set.indicator_of_mem hb]
  · have hb : r.1 • u.1 ∉ ball (0 : E) R := fun h =>
      hr ((smul_mem_ball (E := E) hR u r).1 h)
    simp only [Set.indicator_of_notMem hr, Set.indicator_of_notMem hb]

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
