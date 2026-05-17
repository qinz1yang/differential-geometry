import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlongMetric

set_option linter.unusedSectionVars false

/-!
# Parallel vector fields along a curve

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M` and a
`C¹` curve `γ : ℝ → M`, a `C¹` vector field `V` along `γ` is **parallel** if its
covariant derivative along `γ` vanishes identically:
`covDerivAlong g γ V _ _ t = 0` for every `t`.

The main result of this file is the **inner-product preservation** property:
if `V` and `W` are both parallel along `γ`, then `g.inner (γ s) (V s) (W s)` is
constant in `s`. As a special case, the `g`-norm of a parallel field is
constant. Both statements are unconditional consequences of the metric
compatibility identity `covDerivAlong_metric_compatibility`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry DifferentialGeometry.Integral.Measure
  DifferentialGeometry.Geometry.Riemannian.Curve

namespace Geometry
namespace Riemannian
namespace ParallelTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Parallel vector field along a curve -/

/-- A vector field `V` along a `C¹` curve `γ` is **parallel** if its covariant
derivative along `γ` vanishes at every time. -/
def IsParallelAlong (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))) : Prop :=
  ∀ t, covDerivAlong (I := I) g γ V hγ hV t = 0

/-! ## Differentiability of the inner product along the curve

The function `s ↦ g.inner (γ s) (V s) (W s)` is differentiable at every time
`t`. Locally near `t`, it coincides with the chart-sum representation, whose
differentiability is established in `Curve.CovDerivAlongMetric`. -/

/-- Differentiability of the inner product along the curve at a single time. -/
private lemma g_inner_along_differentiableAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (V W : ∀ t, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (t : ℝ) :
    DifferentiableAt ℝ (fun s => g.inner (γ s) (V s) (W s)) t := by
  classical
  -- (1) Eventual equality with the chart-sum at base time `t`.
  have hev := g_inner_eq_chart_sum_along_eventually (I := I) g γ hγ V W t
  -- (2) Differentiability of each chart-sum factor at `t`.
  have hvi : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ V t i) t := fun i =>
    chartFiberCoordAlong_differentiableAt (I := I) γ V hV t i
  have hwj : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartFiberCoordAlong (I := I) γ W t j) t := fun j =>
    chartFiberCoordAlong_differentiableAt (I := I) γ W hW t j
  have hGij : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartGramAlong (I := I) g γ t i j) t := fun i j =>
    chartGramAlong_differentiableAt (I := I) g γ hγ t i j
  -- (3) Differentiability of each triple-product summand.
  have hijsum : ∀ i j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => chartFiberCoordAlong (I := I) γ V t i s *
          chartFiberCoordAlong (I := I) γ W t j s *
          chartGramAlong (I := I) g γ t i j s) t := fun i j =>
    ((hvi i).mul (hwj j)).mul (hGij i j)
  -- (4) Differentiability of the inner sum over j.
  have hjsum : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun s => ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t := fun i =>
    DifferentiableAt.fun_sum (fun j _ => hijsum i j)
  -- (5) Differentiability of the outer sum over i.
  have hsum : DifferentiableAt ℝ
      (fun s => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ V t i s *
            chartFiberCoordAlong (I := I) γ W t j s *
            chartGramAlong (I := I) g γ t i j s) t :=
    DifferentiableAt.fun_sum (fun i _ => hjsum i)
  -- (6) Transfer differentiability across the eventual equality.
  exact (hev.differentiableAt_iff).mpr hsum

/-! ## Inner-product preservation along a parallel pair -/

/-- **Inner-product preservation.** If `V` and `W` are parallel along `γ`, then
`g.inner (γ s) (V s) (W s)` is independent of `s`. -/
theorem isParallelAlong_inner_const
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW) (t₀ t₁ : ℝ) :
    g.inner (γ t₀) (V t₀) (W t₀) = g.inner (γ t₁) (V t₁) (W t₁) := by
  classical
  -- (1) Globally differentiable inner-product function.
  have hdiff : Differentiable ℝ (fun s => g.inner (γ s) (V s) (W s)) := by
    intro t
    exact g_inner_along_differentiableAt (I := I) g V W hγ hV hW t
  -- (2) Derivative vanishes pointwise via metric compatibility.
  have hderiv_zero : ∀ t, deriv (fun s => g.inner (γ s) (V s) (W s)) t = 0 := by
    intro t
    have hmc := covDerivAlong_metric_compatibility (I := I) g hγ hV hW t
    rw [hmc, hVp t, hWp t]
    -- Goal: `g.inner (γ t) 0 (W t) + g.inner (γ t) (V t) 0 = 0`.
    simp
  -- (3) Apply Mathlib's constancy theorem on ℝ.
  exact is_const_of_deriv_eq_zero hdiff hderiv_zero t₀ t₁

/-- **Norm preservation.** If `V` is parallel along `γ`, then
`g.inner (γ s) (V s) (V s)` is independent of `s`. -/
theorem IsParallelAlong.norm_const
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV) (t₀ t₁ : ℝ) :
    g.inner (γ t₀) (V t₀) (V t₀) = g.inner (γ t₁) (V t₁) (V t₁) :=
  isParallelAlong_inner_const (I := I) hVp hVp t₀ t₁

end ParallelTransport
end Riemannian
end Geometry

end
