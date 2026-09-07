import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.RegularSublevel
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

namespace DifferentialGeometry.Geometry

open MeasureTheory Curvature Operator Topology.Morse
open Integral.Measure
open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (f : M → ℝ) (a : ℝ) : MeasurableSpace (LevelSetSpace f a) :=
  borel (LevelSetSpace f a)
private local instance (f : M → ℝ) (a : ℝ) : BorelSpace (LevelSetSpace f a) := ⟨rfl⟩

theorem gradientRicciSoliton_integral_scalar_eq_volume_sub_levelSet_flux_of_isCompact
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {σ : ℝ}
    (h : gradientRicciSoliton (I := I) g f σ) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcompact : IsCompact {x : M | f x ≤ a}) :
    letI := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
    letI := manifoldLevelSetIsManifold I f a f.contMDiff hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x < a}, metricScalarAt (I := I) g x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (Module.finrank ℝ (MorseModel (m + 1)) : ℝ) * σ / 2 *
        (riemannianVolumeMeasure (I := I) (M := M) g).real {x | f x < a} -
      ∫ y : LevelSetSpace f a, Real.sqrt (normGradSqFun g f y.1)
        ∂(riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a f.contMDiff hreg)) := by
  let := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
  let := manifoldLevelSetIsManifold I f a f.contMDiff hreg
  let : SigmaCompactSpace (LevelSetSpace f a) :=
    (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let U : Set M := {x | f x < a}
  let : IsFiniteMeasureOnCompacts μ :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hUK : U ⊆ {x : M | f x ≤ a} := by
    intro x hx
    change f x ≤ a
    exact le_of_lt hx
  have hscalar_int : IntegrableOn (metricScalarAt (I := I) g) U μ :=
    ((metricScalar_smooth (I := I) (M := M) g).continuous.continuousOn.integrableOn_compact
      hcompact).mono_set hUK
  have hlap_int : IntegrableOn (ΔG g f) U μ :=
    ((Δ_g_contMDiff g f).continuous.continuousOn.integrableOn_compact hcompact).mono_set hUK
  have htrace :
      (∫ x in U, metricScalarAt (I := I) g x ∂μ) + ∫ x in U, ΔG g f x ∂μ =
        (Module.finrank ℝ (MorseModel (m + 1)) : ℝ) * σ / 2 * μ.real U := by
    rw [← integral_add hscalar_int hlap_int]
    calc
      _ = ∫ _x in U, (Module.finrank ℝ (MorseModel (m + 1)) : ℝ) * σ / 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (gradientRicciSoliton_trace h))
      _ = _ := by
        rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
        ring
  have hflux := integral_lt_sublevel_laplacian_eq_levelSet_normGrad_of_isCompact
    I g f a hreg hcompact
  change (∫ x in U, ΔG g f x ∂μ) = _ at hflux
  rw [hflux] at htrace
  exact eq_sub_of_add_eq htrace

theorem normalizedGradientRicciSoliton_integral_scalar_eq_volume_sub_levelSet_flux_of_isCompact
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcompact : IsCompact {x : M | f x ≤ a}) :
    letI := manifoldLevelSetChartedSpace I f a f.contMDiff hreg
    letI := manifoldLevelSetIsManifold I f a f.contMDiff hreg
    letI : SigmaCompactSpace (LevelSetSpace f a) :=
      (isClosed_eq f.contMDiff.continuous continuous_const).sigmaCompactSpace
    (∫ x in {x | f x < a}, metricScalarAt (I := I) g x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (Module.finrank ℝ (MorseModel (m + 1)) : ℝ) / 2 *
        (riemannianVolumeMeasure (I := I) (M := M) g).real {x | f x < a} -
      ∫ y : LevelSetSpace f a, Real.sqrt (normGradSqFun g f y.1)
        ∂(riemannianVolumeMeasure (I := 𝓘(ℝ, MorseModel m))
          (M := LevelSetSpace f a) (levelSetMetric I g f a f.contMDiff hreg)) := by
  simpa only [mul_one] using
    gradientRicciSoliton_integral_scalar_eq_volume_sub_levelSet_flux_of_isCompact h.2.1 a hreg hcompact

end

end DifferentialGeometry.Geometry
