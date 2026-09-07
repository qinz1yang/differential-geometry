import DifferentialGeometry.Analysis.Integration.Measure.SublevelSurface
import DifferentialGeometry.Analysis.Integration.Measure.SublevelVolume
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.SublevelDivergence
import DifferentialGeometry.Geometry.Boundary.SublevelNormal
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.WeightedStokes
import DifferentialGeometry.Geometry.Operator.Laplacian

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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_sublevel_mul_divergence_add_tangentSectionAction_eq_levelSet_flux
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (huc : HasCompactSupport (fun x : SublevelSpace f a => u x.1)) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x ≤ a}, u x * divergenceG g X x + tangentSectionAction X u x
      ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y : LevelSetSpace f a, u y.1 * (Real.sqrt (normGradSqFun g f y.1))⁻¹ * mvfderiv I f y.1 (X y.1)
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
  let Xs := sublevelTangentSection I f a hf hreg X
  let us : SublevelSpace f a → ℝ := fun x => u x.1
  have hus : ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) 𝓘(ℝ, ℝ) ∞ us :=
    hu.comp (contMDiff_manifoldSublevelEuclideanInclusion I f a hf hreg)
  have hs := integral_mul_divergence_sublevelMetric_add_tangentSectionAction_eq_levelSet_flux
    I g f a hf hreg Xs us hus huc
  have hleft : (fun x : SublevelSpace f a =>
      us x * divergenceGWithBoundary (sublevelMetric I g f a hf hreg) Xs x + tangentSectionAction Xs us x) =
      (fun x : SublevelSpace f a => u x.1 * divergenceG g X x.1 + tangentSectionAction X u x.1) := by
    funext x
    rw [divergence_sublevelTangentSection I g f a hf hreg X,
      divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint g X BoundarylessManifold.isInteriorPoint]
    have ha := mvfderiv_sublevelTangentSection I f a hf hreg X u x
      (hu x.1 |>.mdifferentiableAt (by simp))
    exact congrArg (fun z => u x.1 * divergenceG g X x.1 + z) ha
  rw [hleft] at hs
  have hv := integral_sublevelMetric_eq_setIntegral I g f a hf hreg
    (fun x => u x * divergenceG g X x + tangentSectionAction X u x)
  refine (hv.symm.trans hs).trans ?_
  apply integral_congr_ae
  filter_upwards with y
  rw [mfderiv_sublevelTangentSection I f a hf hreg X]

theorem integral_sublevel_divergence_eq_levelSet_flux_of_isCompact
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcompact : IsCompact {x : M | f x ≤ a})
    (X : Cₛ^∞⟮I; MorseModel (m + 1), (TangentSpace I : M → Type)⟯) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    letI := manifoldLevelSetIsManifold I f a hf hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x ≤ a}, divergenceG g X x
      ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y : LevelSetSpace f a, (Real.sqrt (normGradSqFun g f y.1))⁻¹ * mvfderiv I f y.1 (X y.1)
        ∂(Integral.Measure.riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a hf hreg)) := by
  let := manifoldLevelSetChartedSpace I f a hf hreg
  let := manifoldLevelSetIsManifold I f a hf hreg
  let : CompactSpace (SublevelSpace f a) := isCompact_iff_compactSpace.mp hcompact
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq hf.continuous continuous_const).sigmaCompactSpace
  have hs := integral_sublevel_mul_divergence_add_tangentSectionAction_eq_levelSet_flux
    I g f a hf hreg X (fun _ => 1) contMDiff_const (HasCompactSupport.of_compactSpace _)
  simpa only [one_mul, tangentSectionAction_const, add_zero] using hs

theorem integral_sublevel_laplacian_eq_levelSet_normGrad_of_isCompact
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcompact : IsCompact {x : M | f x ≤ a}) :
    letI := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
    letI := manifoldLevelSetIsManifold I f a f.contMDiff hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x ≤ a}, ΔG g f x
      ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y : LevelSetSpace f a, Real.sqrt (normGradSqFun g f y.1)
        ∂(Integral.Measure.riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a f.contMDiff hreg)) := by
  let := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
  let := manifoldLevelSetIsManifold I f a f.contMDiff hreg
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
  have hs := integral_sublevel_divergence_eq_levelSet_flux_of_isCompact I g f a f.contMDiff hreg hcompact (gradG g f)
  refine hs.trans ?_
  apply integral_congr_ae
  filter_upwards with y
  have hgrad : mvfderiv I f y.1 (gradG g f y.1) = normGradSqFun g f y.1 := by
    change mvfderiv I f y.1 (gradientFun g f y.1) = _
    exact (inner_gradientFun g f y.1 (gradientFun g f y.1)).symm
  rw [hgrad]
  have hn := normGradSqFun_nonneg g f y.1
  calc
    _ = (Real.sqrt (normGradSqFun g f y.1))⁻¹ *
        (Real.sqrt (normGradSqFun g f y.1) * Real.sqrt (normGradSqFun g f y.1)) :=
      congrArg (fun z => (Real.sqrt (normGradSqFun g f y.1))⁻¹ * z)
        (Real.mul_self_sqrt hn).symm
    _ = _ := by
      by_cases hzero : Real.sqrt (normGradSqFun g f y.1) = 0
      · simp only [hzero, inv_zero, mul_zero]
      · rw [← mul_assoc, inv_mul_cancel₀ hzero, one_mul]


theorem integral_lt_sublevel_laplacian_eq_levelSet_normGrad_of_isCompact
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcompact : IsCompact {x : M | f x ≤ a}) :
    letI := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
    letI := manifoldLevelSetIsManifold I f a f.contMDiff hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x < a}, ΔG g f x
      ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ y : LevelSetSpace f a, Real.sqrt (normGradSqFun g f y.1)
        ∂(Integral.Measure.riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a f.contMDiff hreg)) := by
  let := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
  let := manifoldLevelSetIsManifold I f a f.contMDiff hreg
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
  have hμ : (Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g).restrict
      {x | f x < a} =
      (Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g).restrict {x | f x ≤ a} := by
    apply Measure.restrict_congr_set
    have hae := measure_eq_zero_iff_ae_notMem.mp
      (riemannianVolumeMeasure_levelSet_eq_zero I g f a f.contMDiff hreg)
    filter_upwards [hae] with x hx
    apply propext
    change (f x < a) ↔ f x ≤ a
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hx⟩
  rw [hμ]
  exact integral_sublevel_laplacian_eq_levelSet_normGrad_of_isCompact I g f a hreg hcompact


end

end DifferentialGeometry.Topology.Morse
