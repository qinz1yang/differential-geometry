import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem hessFun_apply_self_nonneg_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (v : TangentSpace I x) :
    0 <= hessFun (I := I) g f x v v := by
  rw [Connection.hessFun_eq_cov_grad (I := I) g hf x v v]
  exact cov_gradientFun_inner_self_nonneg_at_spatial_min_of_isInteriorPoint
    (I := I) (Connection.LeviCivita (I := I) g) g
      (by
        simpa [Connection.LeviCivita] using
          (Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) g))
      hmin BoundarylessManifold.isInteriorPoint
      (hf.mdifferentiable (by simp) x)
      (Filter.Eventually.of_forall fun y => hf.mdifferentiable (by simp) y)
      (gradientFun_mdiffAt (I := I) g hf x) v

theorem hessFun_apply_self_nonpos_at_spatial_max
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (v : TangentSpace I x) :
    hessFun (I := I) g f x v v <= 0 := by
  have hnonneg := hessFun_apply_self_nonneg_at_spatial_min
    (I := I) g hmax.neg hf.neg v
  have hneg : hessFun (I := I) g (fun y : M => -f y) x v v =
      -hessFun (I := I) g f x v v := by
    rw [show (fun y : M => -f y) = (-1 : Real) • f by
      funext y
      simp]
    rw [hessFun_smul]
    simp
  rw [hneg] at hnonneg
  linarith

end DifferentialGeometry.Geometry.Operator
