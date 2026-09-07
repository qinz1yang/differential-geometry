import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientGlobalSection
import DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.WeightedStokes


noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open DifferentialGeometry.Geometry.Operator.WithBoundary

open DifferentialGeometry.Integral.Measure

private local instance instMeasurableSpaceM
    {M : Type*} [TopologicalSpace M] : MeasurableSpace M := borel M

private local instance instBorelSpaceM
    {M : Type*} [TopologicalSpace M] :
    @BorelSpace M _ (borel M) := letI : MeasurableSpace M := borel M; ⟨rfl⟩

section ClassicalLaplacian

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

noncomputable def ΔGClassical
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {h : M → ℝ} (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    M → ℝ :=
  divergenceGWithBoundary
    (I := modelWithCornersEuclideanHalfSpace n) g
    (gradGFullSection (M := M) (n := n) g hh)

@[simp] lemma Δ_g_classical_def
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {h : M → ℝ} (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    ΔGClassical (M := M) (n := n) g hh x =
      divergenceGWithBoundary
        (I := modelWithCornersEuclideanHalfSpace n) g
        (gradGFullSection (M := M) (n := n) g hh) x := rfl

end ClassicalLaplacian

section GreenFull

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem green_first_eq_boundary_surface_integral
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    ∫ x, g.inner x
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)
        ∂(riemannianVolumeMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) +
      ∫ x, f x * ΔGClassical (M := M) (n := n) g hh x
        ∂(riemannianVolumeMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) =
      ∫ x : (modelWithCornersEuclideanHalfSpace n).boundary M,
        f x.val *
          g.inner x.val
            (outwardNormal
                (I := modelWithCornersEuclideanHalfSpace n) (M := M) g x :
              TangentSpace _ x.val)
            (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x.val)
        ∂(surfaceMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  let X := gradGFullSection (M := M) (n := n) g hh
  have haction : tangentSectionAction X f =
      fun x => g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x) := by
    funext x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner g X x]
    exact g.symm x _ _
  have hdiv : Integrable (fun x => f x * divergenceGWithBoundary g X x)
      (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      (hf.continuous.mul (divergence_g_with_boundary_contMDiff g X).continuous)
      (HasCompactSupport.of_compactSpace _)
  have hact : Integrable (tangentSectionAction X f)
      (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      (tangentSectionAction_contMDiff X hf).continuous (HasCompactSupport.of_compactSpace _)
  have hStokes :=
    integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux
      g X hf (HasCompactSupport.of_compactSpace _)
  rw [integral_add hdiv hact, haction] at hStokes
  exact (add_comm _ _).trans hStokes

end GreenFull

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
