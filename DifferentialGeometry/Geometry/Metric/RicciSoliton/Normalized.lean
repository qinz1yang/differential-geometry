import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialCompleteness

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

def normalizedGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) : Prop :=
  RiemannianMetricComplete (I := I) g ∧
    gradientRicciSoliton (I := I) g f 1 ∧
      ∀ x : M, metricScalarAt (I := I) g x +
        normGradSqFun (I := I) g f x = f x

theorem normalizedGradientRicciSoliton_complete
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    RiemannianMetricComplete (I := I) g :=
  h.1

theorem normalizedGradientRicciSoliton_equation
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    gradientRicciSoliton (I := I) g f 1 :=
  h.2.1

theorem normalizedGradientRicciSoliton_potential_equation
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    metricScalarAt (I := I) g x +
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = f x := by
  simpa only [normGradSqFun_def] using h.2.2 x

theorem normalizedGradientRicciSoliton_scalar_nonneg
    [NeZero (Module.finrank Real E)] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    0 ≤ metricScalarAt (I := I) g x := by
  have hR := gradientRicciSoliton_scalar_lower_bound
    (I := I) g f 1 h.1 h.2.1 x
  have hhalf : 0 ≤ (Module.finrank Real E : Real) * 1 / 2 := by positivity
  rw [min_eq_left hhalf] at hR
  exact hR

theorem normalizedGradientRicciSoliton_potential_nonneg
    [NeZero (Module.finrank Real E)] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    0 ≤ f x := by
  have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h x
  have hgrad := normGradSqFun_nonneg (I := I) g (f : M → Real) x
  linarith [h.2.2 x]

theorem normalizedGradientRicciSoliton_hamilton_normalized
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    hamiltonNormalized (I := I) g f 1 := by
  intro x
  simpa only [one_mul] using
    normalizedGradientRicciSoliton_potential_equation (I := I) h x

theorem normalizedGradientRicciSoliton_weightedLaplacian_potential
    [NeZero (Module.finrank Real E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (x : M) :
    weightedLaplacian (I := I) g f f x =
      (Module.finrank Real E : Real) / 2 - f x := by
  have hC : ∀ y : M,
      metricScalarAt (I := I) g y +
          g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) - 1 * f y = 0 := by
    intro y
    rw [normalizedGradientRicciSoliton_potential_equation (I := I) h y]
    ring
  have hw := gradientRicciSoliton_weightedLaplacian_potential
    (I := I) h.2.1 hC x
  rw [one_mul, sub_zero] at hw
  simpa only [mul_one] using hw

theorem normalizedGradientRicciSoliton_add_const_unique
    [Nonempty M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {c : Real}
    (hf : normalizedGradientRicciSoliton (I := I) g f)
    (hc : normalizedGradientRicciSoliton (I := I) g
      (f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf Real Real) (M := M) (n := ∞) c)) :
    c = 0 := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  have hgrad :
      gradFun (I := I) g ((f : M → Real) + (fun _ : M => c)) x =
        gradFun (I := I) g f x := by
    rw [Operator.gradFun_add (I := I) g
      ((f.contMDiff x).mdifferentiableAt (by simp))
      (mdifferentiableAt_const (c := c)), Operator.gradFun_const]
    simp
  have hf' := normalizedGradientRicciSoliton_potential_equation (I := I) hf x
  have hc' := normalizedGradientRicciSoliton_potential_equation (I := I) hc x
  change metricScalarAt (I := I) g x +
      g.inner x (gradFun (I := I) g
        ((f : M → Real) + (fun _ : M => c)) x)
        (gradFun (I := I) g ((f : M → Real) + (fun _ : M => c)) x) =
    f x + c at hc'
  rw [hgrad] at hc'
  linarith

end DifferentialGeometry.Geometry
