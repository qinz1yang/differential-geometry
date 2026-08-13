import DifferentialGeometry.Geometry.Boundary.Orientation
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum

set_option autoImplicit false

noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

section OutwardNormalDerivative

variable [FiniteDimensional ℝ E]

def outwardNormalDerivative
    (g : Measure.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) : ℝ :=
  g.inner (x : M) (gradientFun (I := I) g f (x : M))
    (outwardNormal (M := M) g x)

@[simp] theorem outwardNormalDerivative_apply
    (g : Measure.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) :
    outwardNormalDerivative (M := M) g f x =
      g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (outwardNormal (M := M) g x) := rfl

theorem outwardNormalDerivative_eq_mfderiv
    (g : Measure.SmoothRiemannianMetric I M) (f : M → ℝ)
    (x : BoundaryManifold I M) :
    outwardNormalDerivative (M := M) g f x =
      mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
        (outwardNormal (M := M) g x) := by
  exact inner_gradientFun (I := I) g f (x : M)
    (outwardNormal (M := M) g x)

end OutwardNormalDerivative

theorem mfderiv_boundary_tangent_eq_zero_at_local_min
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (w : hI.boundaryE) :
    mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
        (boundaryInclusionMfderiv (M := M) x w) = 0 := by
  have hinclusion : MDifferentiableAt hI.boundaryI I
      (boundaryInclusion I M) x :=
    (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
      (by simp)
  have hcomp : MDifferentiableAt hI.boundaryI
      (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x := by
    exact hf.comp x hinclusion
  have hmin' : IsLocalMin (f ∘ boundaryInclusion I M) x := by
    simpa [Function.comp_def] using hmin
  have hzero : mfderiv hI.boundaryI (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x = 0 :=
    mfderiv_eq_zero_at_spatial_min (I := hI.boundaryI) hmin' hcomp
  have hchain := mfderiv_comp x hf hinclusion
  have happ := congrArg (fun L => L w) hchain
  change mfderiv hI.boundaryI (modelWithCornersSelf ℝ ℝ)
      (f ∘ boundaryInclusion I M) x w =
        mfderiv I (modelWithCornersSelf ℝ ℝ) f (x : M)
          (boundaryInclusionMfderiv (M := M) x w) at happ
  rw [hzero] at happ
  simpa [boundaryInclusionMfderiv] using happ.symm

section GradientBoundaryTangent

variable [FiniteDimensional ℝ E]

theorem inner_gradient_boundary_tangent_eq_zero_at_local_min
    (g : Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (w : hI.boundaryE) :
    g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (boundaryInclusionMfderiv (M := M) x w) = 0 := by
  rw [inner_gradientFun]
  exact mfderiv_boundary_tangent_eq_zero_at_local_min
    (M := M) hmin hf w

end GradientBoundaryTangent

section OutwardNormalSign

variable [FiniteDimensional ℝ E]

theorem outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min
    (g : Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : BoundaryManifold I M}
    (hmin : IsLocalMin (fun y : BoundaryManifold I M ↦ f (y : M)) x)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (x : M))
    (hinward : 0 < g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (inwardCoord (M := M) x)) :
    outwardNormalDerivative (M := M) g f x < 0 := by
  have htangent : g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (inwardTangentialPart (M := M) g x) = 0 := by
    rw [inwardTangentialPart_def]
    exact inner_gradient_boundary_tangent_eq_zero_at_local_min
      (M := M) g hmin hf (boundaryComponentOfInward (M := M) g x)
  have houtwardDir : g.inner (x : M) (gradientFun (I := I) g f (x : M))
      (outwardDir (M := M) g x) =
        -g.inner (x : M) (gradientFun (I := I) g f (x : M))
          (inwardCoord (M := M) x) := by
    rw [outwardDir_def, map_sub, htangent, zero_sub]
  rw [outwardNormalDerivative_apply, outwardNormal_eq, map_smul,
    houtwardDir]
  change (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ *
      (-g.inner (x : M) (gradientFun (I := I) g f (x : M))
        (inwardCoord (M := M) x)) < 0
  have hscale : 0 < (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ := by
    exact inv_pos.mpr (Real.sqrt_pos.mpr (g_inner_outwardDir_pos (M := M) g x))
  exact mul_neg_of_pos_of_neg hscale (neg_neg_of_pos hinward)

end OutwardNormalSign

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
