import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Operator.HessianAlgebra

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

def gradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (σ : Real) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x,
    ricciTensor (I := I) g x v w + hessFun (I := I) g f x v w =
      (σ / 2) * g.inner x v w

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_add_const
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ) (c : Real) :
    gradientRicciSoliton (I := I) g (f + ContMDiffMap.const c) σ := by
  intro x v w
  change ricciTensor (I := I) g x v w +
      hessFun (I := I) g (fun y => f y + c) x v w =
    (σ / 2) * g.inner x v w
  rw [hessFun_add_const (I := I) g f c x v w]
  exact h x v w

end DifferentialGeometry.Geometry
