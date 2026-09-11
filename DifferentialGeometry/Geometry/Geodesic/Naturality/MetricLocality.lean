import DifferentialGeometry.Geometry.Geodesic.Equation.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartChristoffel_eq_of_metric_eventuallyEq
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g₁.inner y v w = g₂.inner y v w)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel g₁ x i j k (extChartAt I x x) =
      chartChristoffel g₂ x i j k (extChartAt I x x) := by
  have hchart := continuousAt_extChartAt_symm (I := I) x
  unfold ContinuousAt at hchart
  rw [extChartAt_to_inv] at hchart
  have hGram (a b : Fin (Module.finrank ℝ E)) :
      chartGramOnE g₁ x a b =ᶠ[𝓝 (extChartAt I x x)] chartGramOnE g₂ x a b := by
    filter_upwards [hchart hmetric] with y hy
    exact hy _ _
  have hGramPoint : chartGramMatrix g₁ x x = chartGramMatrix g₂ x x := by
    ext a b
    exact hmetric.self_of_nhds _ _
  have hInv : chartInvGramMatrix g₁ x x = chartInvGramMatrix g₂ x x :=
    congrArg (fun A => A⁻¹) hGramPoint
  have hpartial (a b c : Fin (Module.finrank ℝ E)) :
      partialDeriv a (chartGramOnE g₁ x b c) (extChartAt I x x) =
        partialDeriv a (chartGramOnE g₂ x b c) (extChartAt I x x) := by
    exact congrArg (fun D : E →L[ℝ] ℝ => D (chartModelBasis E a)) (hGram b c).fderiv_eq
  simp only [chartChristoffel_def, extChartAt_to_inv, hInv, hpartial]

theorem hasGeodesicEquationAt_iff_of_metric_eventuallyEq
    (g₁ g₂ : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hmetric : ∀ᶠ x in 𝓝 (γ t), ∀ v w : TangentSpace I x,
      g₁.inner x v w = g₂.inner x v w) :
    HasGeodesicEquationAt g₁ γ t ↔ HasGeodesicEquationAt g₂ γ t := by
  have hcontraction (v : E) :
      chartChristoffelContraction g₁ (γ t) v v (extChartAt I (γ t) (γ t)) =
        chartChristoffelContraction g₂ (γ t) v v (extChartAt I (γ t) (γ t)) := by
    simp only [chartChristoffelContraction_def,
      chartChristoffel_eq_of_metric_eventuallyEq g₁ g₂ (γ t) hmetric]
  simp only [HasGeodesicEquationAt, hcontraction]

theorem isGeodesicOn_iff_of_metric_eventuallyEq
    (g₁ g₂ : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hmetric : ∀ t ∈ s, ∀ᶠ x in 𝓝 (γ t), ∀ v w : TangentSpace I x,
      g₁.inner x v w = g₂.inner x v w) :
    IsGeodesicOn g₁ γ s ↔ IsGeodesicOn g₂ γ s := by
  apply forall₂_congr
  intro t ht
  exact hasGeodesicEquationAt_iff_of_metric_eventuallyEq g₁ g₂ (hmetric t ht)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
