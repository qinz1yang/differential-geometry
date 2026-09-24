import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared


noncomputable section

open Bundle Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tendsto_normGradSqFun_of_chart
    {A : Type*} {l : Filter A}
    (g : A → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (f : A → M → ℝ) (f₀ : M → ℝ) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hf : ∀ᶠ a in l, MDifferentiableAt I 𝓘(ℝ, ℝ) (f a) x)
    (hf₀ : MDifferentiableAt I 𝓘(ℝ, ℝ) f₀ x)
    (hG : ∀ i j : Fin (Module.finrank ℝ E),
      Tendsto (fun a => chartInvGramMatrix (I := I) (g a) α x i j) l
        (𝓝 (chartInvGramMatrix (I := I) g₀ α x i j)))
    (hD : ∀ i : Fin (Module.finrank ℝ E),
      Tendsto
        (fun a => fderiv ℝ (fun y : E => f a ((extChartAt I α).symm y))
          (extChartAt I α x) (chartModelBasis E i)) l
        (𝓝 (fderiv ℝ (fun y : E => f₀ ((extChartAt I α).symm y))
          (extChartAt I α x) (chartModelBasis E i)))) :
    Tendsto (fun a => normGradSqFun (g a) (f a) x) l
      (𝓝 (normGradSqFun g₀ f₀ x)) := by
  have hsum : Tendsto
      (fun a => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (g a) α x i j *
          fderiv ℝ (fun y : E => f a ((extChartAt I α).symm y))
            (extChartAt I α x) (chartModelBasis E j) *
          fderiv ℝ (fun y : E => f a ((extChartAt I α).symm y))
            (extChartAt I α x) (chartModelBasis E i)) l
      (𝓝 (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₀ α x i j *
          fderiv ℝ (fun y : E => f₀ ((extChartAt I α).symm y))
            (extChartAt I α x) (chartModelBasis E j) *
          fderiv ℝ (fun y : E => f₀ ((extChartAt I α).symm y))
            (extChartAt I α x) (chartModelBasis E i))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact ((hG i j).mul (hD j)).mul (hD i)
  have hzero := grad_norm_sq_chart g₀ α hf₀ hx
  change normGradSqFun g₀ f₀ x =
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₀ α x i j *
        fderiv ℝ (fun y : E => f₀ ((extChartAt I α).symm y))
          (extChartAt I α x) (chartModelBasis E j) *
        fderiv ℝ (fun y : E => f₀ ((extChartAt I α).symm y))
          (extChartAt I α x) (chartModelBasis E i)) at hzero
  rw [hzero]
  apply hsum.congr'
  filter_upwards [hf] with a ha
  exact (grad_norm_sq_chart (g a) α ha hx).symm

theorem hamiltonNormalized_of_tendsto_chart
    {A : Type*} {l : Filter A} [NeBot l]
    (g : A → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (f : A → C^∞⟮I, M; ℝ⟯) (f₀ : C^∞⟮I, M; ℝ⟯)
    (σ : A → ℝ) (σ₀ : ℝ)
    (hR : ∀ x : M, Tendsto (fun a => metricScalarAt (g a) x) l
      (𝓝 (metricScalarAt g₀ x)))
    (hG : ∀ x : M, ∀ i j : Fin (Module.finrank ℝ E),
      Tendsto (fun a => chartInvGramMatrix (I := I) (g a) x x i j) l
        (𝓝 (chartInvGramMatrix (I := I) g₀ x x i j)))
    (hD : ∀ x : M, ∀ i : Fin (Module.finrank ℝ E),
      Tendsto
        (fun a => fderiv ℝ (fun y : E => f a ((extChartAt I x).symm y))
          (extChartAt I x x) (chartModelBasis E i)) l
        (𝓝 (fderiv ℝ (fun y : E => f₀ ((extChartAt I x).symm y))
          (extChartAt I x x) (chartModelBasis E i))))
    (hf : ∀ x : M, Tendsto (fun a => f a x) l (𝓝 (f₀ x)))
    (hσ : Tendsto σ l (𝓝 σ₀))
    (hnormal : ∀ᶠ a in l, hamiltonNormalized (g a) (f a) (σ a)) :
    hamiltonNormalized g₀ f₀ σ₀ := by
  intro x
  have hgrad := tendsto_normGradSqFun_of_chart g g₀
    (fun a => (f a : M → ℝ)) f₀ x (mem_chart_source H x)
    (Filter.Eventually.of_forall fun a =>
      (f a).contMDiff.mdifferentiableAt (by simp))
    (f₀.contMDiff.mdifferentiableAt (by simp)) (hG x) (hD x)
  have hleft := (hR x).add hgrad
  have hright := hσ.mul (hf x)
  change metricScalarAt g₀ x + normGradSqFun g₀ f₀ x = σ₀ * f₀ x
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hnormal] with a ha
  exact ha x

end DifferentialGeometry.Geometry
