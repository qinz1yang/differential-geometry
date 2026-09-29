import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

noncomputable def reducedAction {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ) (τ : ℝ) (γ : ℝ → M) : ℝ :=
  ∫ s in (0 : ℝ)..τ,
    Real.sqrt s *
      (metricScalarAt (g (t₀ - s)) (γ s) +
        DifferentialGeometry.Geometry.riemannianCurveSpeed (g (t₀ - s)) γ s ^ 2)

noncomputable def reducedLength {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) : ℝ :=
  sInf {r : ℝ | ∃ γ : ℝ → M,
    admissible γ ∧ γ 0 = p ∧ γ τ = x ∧ reducedAction g t₀ τ γ = r}

noncomputable def reducedVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (V : Set M) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal
    ((4 * Real.pi * τ) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(reducedLength g t₀ admissible p τ x) / (2 * Real.sqrt τ)))
    ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M)
      (g (t₀ - τ)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
