import DifferentialGeometry.Geometry.Boundary.SublevelMetric
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (SublevelSpace f a) :=
  borel (SublevelSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (SublevelSpace f a) := ⟨rfl⟩
private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (LevelSetSpace f a) :=
  borel (LevelSetSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (LevelSetSpace f a) := ⟨rfl⟩

theorem surfaceMeasure_sublevelMetric_eq_map (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    letI : SigmaCompactSpace (SublevelSpace f a) :=
      (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
    surfaceMeasure (sublevelMetric I g f a hf hreg) =
      Measure.map (manifoldSublevelBoundaryDiffeomorph I f a hf hreg).symm
        (Integral.Measure.riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a hf hreg)) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  let := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  let : SigmaCompactSpace (SublevelSpace f a) :=
    (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
  let Φ := manifoldSublevelBoundaryDiffeomorph I f a hf hreg
  have hg : inducedMetric (sublevelMetric I g f a hf hreg) =
      Diffeomorph.pullbackMetricCross (levelSetMetric I g f a hf hreg) Φ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact inducedMetric_sublevelMetric_inner I g f a hf hreg x v w
  exact (congrArg
    (fun k => Integral.Measure.riemannianVolumeMeasure
      (I := HasSmoothBoundary.boundaryModel (modelWithCornersEuclideanHalfSpace (m + 1)))
      (M := BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a)) k)
    hg).trans (Integral.Measure.riemannianVolumeMeasure_pullback_cross _ Φ)

theorem integral_surfaceMeasure_sublevelMetric_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclidean_isManifold I f a hf hreg
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    letI : SigmaCompactSpace (SublevelSpace f a) :=
      (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
    ∀ u : BoundaryManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a) → V,
      ∫ x, u x ∂(surfaceMeasure (sublevelMetric I g f a hf hreg)) =
        ∫ y, u ((manifoldSublevelBoundaryDiffeomorph I f a hf hreg).symm y)
          ∂(Integral.Measure.riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
            (M := LevelSetSpace f a) (levelSetMetric I g f a hf hreg)) := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let := manifoldSublevelEuclidean_isManifold I f a hf hreg
  let := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  let : SigmaCompactSpace (SublevelSpace f a) :=
    (isClosed_le hf.continuous continuous_const).sigmaCompactSpace
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
  intro u
  rw [surfaceMeasure_sublevelMetric_eq_map]
  exact (manifoldSublevelBoundaryDiffeomorph I f a hf hreg).symm.toHomeomorph.toMeasurableEquiv
    |>.measurableEmbedding.integral_map u

end

end DifferentialGeometry.Topology.Morse
