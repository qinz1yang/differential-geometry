import DifferentialGeometry.Analysis.Integration.Measure.SublevelSurface
import DifferentialGeometry.Geometry.Boundary.SublevelNormal
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.WeightedStokes

namespace DifferentialGeometry.Topology.Morse

open Integral.DivergenceTheorem.WithBoundary Geometry.Operator MeasureTheory Bundle
open Integral.DivergenceTheorem
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (SublevelSpace f a) :=
  borel (SublevelSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (SublevelSpace f a) := ⟨rfl⟩
private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (LevelSetSpace f a) :=
  borel (LevelSetSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (LevelSetSpace f a) := ⟨rfl⟩

theorem integral_mul_divergence_sublevelMetric_add_tangentSectionAction_eq_levelSet_flux
    (g : SmoothRiemannianMetric I M)
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
    ∀ (X : Cₛ^∞⟮modelWithCornersEuclideanHalfSpace (m + 1); EuclideanSpace ℝ (Fin (m + 1)),
        (TangentSpace (modelWithCornersEuclideanHalfSpace (m + 1)) : SublevelSpace f a → Type)⟯)
      (u : SublevelSpace f a → ℝ),
      ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) 𝓘(ℝ, ℝ) ∞ u → HasCompactSupport u →
      ∫ x, u x * divergenceGWithBoundary (sublevelMetric I g f a hf hreg) X x + tangentSectionAction X u x
        ∂(Integral.Measure.riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace (m + 1))
          (M := SublevelSpace f a) (sublevelMetric I g f a hf hreg)) =
      ∫ y : LevelSetSpace f a,
        u ⟨y.1, le_of_eq y.2⟩ * (Real.sqrt (normGradSqFun g f y.1))⁻¹ * mvfderiv I f y.1
          (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
            (fun x : SublevelSpace f a => x.1) ⟨y.1, le_of_eq y.2⟩ (X ⟨y.1, le_of_eq y.2⟩))
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
  intro X u hu huc
  have hs := integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux
    (sublevelMetric I g f a hf hreg) X hu huc
  have ht := integral_surfaceMeasure_sublevelMetric_eq I g f a hf hreg
    (fun x => u x.1 * (sublevelMetric I g f a hf hreg).inner x.1
      (outwardNormal (sublevelMetric I g f a hf hreg) x) (X x.1))
  refine (hs.trans ht).trans ?_
  apply integral_congr_ae
  filter_upwards with y
  rw [sublevelMetric_outwardNormal_inner]
  exact (mul_assoc _ _ _).symm

end

end DifferentialGeometry.Topology.Morse
