import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality

set_option autoImplicit false

/-!
# 盘的共形 / 调和条件对度量的 locality（车道 S-A10-GAUSS，G4，后缀 `_GB`）

`IsMorreyDisk G γU q` 是在 open target `Ω` 上对 canonical positive-domain metric `G` 陈述的；
`_HC` 的 local metric clause 给出 `G.inner = (g.restrictOpen Ω).inner` 在 `q z` 的邻域上。
这里证明：两个度量在 `γ t` 的邻域上相等 ⇒ `covDerivAlong` 在 `t` 相等（Christoffel 的 locality，
`Geodesic/Naturality/MetricLocality.lean` 里的同名 private 引理的公开版），进而
`diskMapTension` 与 `DiskMapConformalAt` 只依赖 `U z` 附近的度量。
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry

section Christoffel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartChristoffel_eq_of_metric_eventuallyEq_GB
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

theorem covDerivAlong_eq_of_metric_eventuallyEq_GB
    (g₁ g₂ : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hmetric : ∀ᶠ y in 𝓝 (γ t), ∀ v w : TangentSpace I y,
      g₁.inner y v w = g₂.inner y v w) :
    covDerivAlong g₁ γ V t = covDerivAlong g₂ γ V t := by
  have hcontraction (v w : E) :
      chartChristoffelContraction g₁ (γ t) v w (extChartAt I (γ t) (γ t)) =
        chartChristoffelContraction g₂ (γ t) v w (extChartAt I (γ t) (γ t)) := by
    simp only [chartChristoffelContraction_def,
      chartChristoffel_eq_of_metric_eventuallyEq_GB g₁ g₂ (γ t) hmetric]
  simp only [covDerivAlong_def, chartCovDerivAlong_def, chartCurve_def, hcontraction]

end Christoffel

section Disk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {U : ℂ → M} {z : ℂ}

omit [FiniteDimensional ℝ E] in
/-- `DiskMapConformalAt` 只用 `U z` 处的度量。 -/
theorem diskMapConformalAt_congr_of_metric_GB
    (g₁ g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (h : ∀ v w : TangentSpace 𝓘(ℝ, E) (U z), g₁.inner (U z) v w = g₂.inner (U z) v w) :
    DiskMapConformalAt g₁ U z ↔ DiskMapConformalAt g₂ U z := by
  unfold DiskMapConformalAt
  simp only [h]

/-- `diskMapTension` 只用 `U z` 邻域上的度量（Christoffel 的 locality）。 -/
theorem diskMapTension_congr_of_metric_eventuallyEq_GB
    (g₁ g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (h : ∀ᶠ y in 𝓝 (U z), ∀ v w : TangentSpace 𝓘(ℝ, E) y,
      g₁.inner y v w = g₂.inner y v w) :
    diskMapTension g₁ U z = diskMapTension g₂ U z := by
  have hcov (v w : ℂ) :
      diskMapCovariantPartial g₁ U z v w = diskMapCovariantPartial g₂ U z v w := by
    unfold diskMapCovariantPartial
    have h' : ∀ᶠ y in 𝓝 ((fun t : ℝ => U (z + t • v)) 0), ∀ a b : TangentSpace 𝓘(ℝ, E) y,
        g₁.inner y a b = g₂.inner y a b := by
      simpa only [zero_smul, add_zero] using h
    exact covDerivAlong_eq_of_metric_eventuallyEq_GB g₁ g₂ _ _ 0 h'
  unfold diskMapTension
  rw [hcov 1 1, hcov Complex.I Complex.I]

omit [FiniteDimensional ℝ E] in
/-- `riemannianAreaDensity` 只用 `U z` 处的度量。 -/
theorem riemannianAreaDensity_congr_of_metric_GB
    (g₁ g₂ : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (h : ∀ v w : TangentSpace 𝓘(ℝ, E) (U z), g₁.inner (U z) v w = g₂.inner (U z) v w) :
    riemannianAreaDensity g₁ U z = riemannianAreaDensity g₂ U z := by
  unfold riemannianAreaDensity tangentTwoJacobian
  simp only [h]

end Disk

end DifferentialGeometry.Geometry
