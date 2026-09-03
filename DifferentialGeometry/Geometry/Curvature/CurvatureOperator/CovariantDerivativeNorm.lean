import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Comparison

open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

noncomputable def curvCovDerivStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 5) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov := DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  let hcov := DifferentialGeometry.Geometry.Curvature.metricCov_smooth (I := I) (M := M) g
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 4) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 4) cov A hreg

noncomputable def curvCovDeriv
    (g : SmoothRiemannianMetric I M) :
    (k : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4) :=
  Nat.rec
    (motive := fun k : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g)
    (fun k A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          curvCovDerivStep (I := I) g k A)

omit [SigmaCompactSpace M] in
theorem curvCovDeriv_succ
    (g : SmoothRiemannianMetric I M) (k : Nat) :
    curvCovDeriv (I := I) (M := M) g (k + 1) =
      curvCovDerivStep (I := I) g k
        (curvCovDeriv (I := I) (M := M) g k) :=
  rfl

section PointwiseCurvature

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem curvZero_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    curvCovDeriv (I := I) (M := M) g 0 x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      g.inner x W
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          x X Y Z) := by
  rw [show curvCovDeriv (I := I) (M := M) g 0 =
      DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g from rfl]
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04_apply]
  change
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        g
        (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
        (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
          (I := I) (M := M) g) x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      _
  rw [DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const]
  let :
      CovariantDerivative.ContMDiffCovariantDerivative
        (DifferentialGeometry.Geometry.Curvature.metricCov
          (I := I) (M := M) g) ∞ :=
    DifferentialGeometry.Geometry.Connection.LeviCivita_isContMDiff
      (I := I) (M := M) g
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
    (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
      (I := I) (M := M) g) x X Y Z]
  rfl

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem curvOne_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    curvCovDeriv (I := I) (M := M) g 1 x
        (DifferentialGeometry.Geometry.Curvature.vec5 (I := I) D X Y Z W) =
      g.inner x W
        (DifferentialGeometry.Integral.Connection.nablaRiemannOp
          (I := I) g x D X Y Z) := by
  simpa [curvCovDeriv, curvCovDerivStep,
    DifferentialGeometry.Geometry.Curvature.metricCov,
    DifferentialGeometry.Geometry.Curvature.metricRm04] using
    (DifferentialGeometry.Integral.Connection.nablaRm04_apply
      (I := I) g x D X Y Z W)

end PointwiseCurvature

noncomputable def curvDerivNormSq
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) g x (k + 4)
    (curvCovDeriv (I := I) (M := M) g k x)

noncomputable def curvDerivNorm
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt (curvDerivNormSq (I := I) (M := M) k g x)

omit [SigmaCompactSpace M] in
theorem curv_apply_le
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 4) -> TangentSpace I x) :
    |curvCovDeriv (I := I) (M := M) g k x v| <=
      curvDerivNorm (I := I) (M := M) k g x *
        ∏ a : Fin (k + 4), Real.sqrt (g.inner x (v a) (v a)) := by
  simpa [curvDerivNorm, curvDerivNormSq] using
    (Tensor0SBundle.abs_apply_le_norm0S (I := I) g x (k + 4)
      (curvCovDeriv (I := I) (M := M) g k x) v)

end HCGCompactness
end DifferentialGeometry
