import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BoundedGeometry

import DifferentialGeometry.Geometry.Metric.Convergence.ProductDerivativeNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.RicciTowerTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.HeatEquation
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem curvStep_eq_covStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    curvCovDerivStep (I := I) g a A =
      covStep (I := I) g (a + 4) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply]
  rfl

private def curvEquiv : (m : Nat) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (curvEquiv m)

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curv_apply_iterCov
    (g : SmoothRiemannianMetric I M) :
    ∀ (m : Nat) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (curvEquiv m)
              (iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I) g m
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I) (M := M) g m)
        _ = covStep (I := I) g (m + 4)
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvStep_eq_covStep (I := I) (M := M) g m _)
        _ = covStep (I := I) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
                (∞ : WithTop ℕ∞) (curvEquiv m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (frontExtendEquiv (curvEquiv m))
              (covStep (I := I) g (4 + m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I) g (curvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (curvEquiv (m + 1))
              ((iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) (m + 1)) x)) v := by
          rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem curvCovDeriv_normSq_eq
    (g : SmoothRiemannianMetric I M) (m : Nat) (x : M) :
    normSq0S (I := I) g x (m + 4) (curvCovDeriv (I := I) (M := M) g m x) =
      normSq0S (I := I) g x (4 + m)
        ((iterCov (I := I) g 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04
            (I := I) (M := M) g) m) x) := by
  classical
  have hfiber :
      curvCovDeriv (I := I) (M := M) g m x =
        ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact curv_apply_iterCov (I := I) (M := M) g m x v
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv :
      MetricInverseInBasis_gen (I := I) g x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  rw [hfiber]
  exact normSq0S_domDomCongr (I := I) g x basis hinv (curvEquiv m)
    ((iterCov (I := I) g 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04
        (I := I) (M := M) g) m) x)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem curvNormSq_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    curvDerivNormSq (I := I) (M := M) k (S.base.metric t) x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  classical
  unfold curvDerivNormSq nablaKRm04NormSqIntrinsic
  rw [curvCovDeriv_normSq_eq (I := I) (M := M) (S.base.metric t) k x]
  exact congrArg
    (fun A => normSq0S (I := I) (S.base.metric t) x (4 + k) (A x))
    (nablaKRm_eq_iterCov (I := I) S t k).symm

end HCGCompactness
end DifferentialGeometry
