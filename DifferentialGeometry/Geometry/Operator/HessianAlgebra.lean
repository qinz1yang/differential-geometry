import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hessFun_add_const
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (c : Real)
    (x : M) (v w : TangentSpace I x) :
    hessFun (I := I) g (fun y => f y + c) x v w =
      hessFun (I := I) g f x v w := by
  rw [Connection.hessFun_eq_abstract (I := I) (f := fun y => f y + c)
    g (f.contMDiff.add contMDiff_const) x v w]
  rw [Connection.hessFun_eq_abstract (I := I) (f := f) g f.contMDiff x v w]
  simp only [Connection.abstractHessian_apply]
  have hderiv :
      mvfderiv (I := I) (fun y : M => f y + c) = mvfderiv (I := I) f := by
    funext y
    rw [show (fun z : M => f z + c) =
      (fun z : M => f z) + (fun _ : M => c) by rfl]
    rw [mvfderiv_add
      (f.contMDiff.mdifferentiable (by simp) y)
      (mdifferentiableAt_const (c := c))]
    rw [mvfderiv_const]
    simp
  rw [hderiv]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hessFun_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; Real⟯) (x : M) (v w : TangentSpace I x) :
    hessFun (I := I) (scaleMetric (I := I) c hc g) f x v w =
      hessFun (I := I) g f x v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  rw [Connection.hessFun_eq_abstract (I := I) (scaleMetric (I := I) c hc g)
    f.contMDiff x v w]
  rw [Connection.hessFun_eq_abstract (I := I) g f.contMDiff x v w]
  simp only [Connection.abstractHessian_apply]
  rw [show Connection.LeviCivita (I := I) (scaleMetric (I := I) c hc g) =
      Connection.LeviCivita (I := I) g by
    simpa [Connection.LeviCivita] using
      (Connection.lcConn_scaleMetric (I := I) c hc g)]

end DifferentialGeometry.Geometry.Operator
