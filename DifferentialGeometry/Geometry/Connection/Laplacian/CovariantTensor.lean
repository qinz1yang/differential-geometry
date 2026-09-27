import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalHessian
import DifferentialGeometry.Geometry.Operator.MetricTraceOrthonormalFrame
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Geometry.Operator.CovariantTensor

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem rawBundleConnLap_multilinear_eq_roughLap0STensor
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (hreg : TotalNabla0SRegular s (LeviCivita g) A) (x : M) :
    rawBundleConnLap g ((LeviCivita g).multilinear s) (fun y => A y) x =
      roughLap0STensor g (totalNabla0SFun (s + 1) (LeviCivita g)
        (totalNabla0S s (LeviCivita g) A hreg) x) := by
  let B := totalNabla0S s (LeviCivita g) A hreg
  have hDB := funext (totalNabla0S_curryLeft_eq_multilinear s (LeviCivita g) A hreg)
  have hD : MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ))
      (fun y => TotalSpace.mk'
        (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) y
        ((LeviCivita g).multilinear s (fun z => A z) y)) x := by
    change MDifferentiableAt I _ (fun y => TotalSpace.mk' _ y
      ((fun z => (LeviCivita g).multilinear s (fun w => A w) z) y)) x
    rw [← hDB]
    exact B.mdifferentiableAt.multilinear_bundle_curry_left
  unfold rawBundleConnLap
  apply tensor0SSpace_ext s x
  intro tail
  simp only [roughLap0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_smoothOrthoFrame]
  erw [Tensor0SSpace.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  have hH := CovariantDerivative.hessian_apply ((LeviCivita g).multilinear s)
    (LeviCivita g) hD ((smoothOrthoFrame_smooth g x i).mdifferentiableAt (by simp))
    (smoothOrthoFrame g x i x)
  have hTotal := totalNabla0SFun_totalNabla0S_apply_eq_hessian s (LeviCivita g) A hreg x
    (smoothOrthoFrame g x i x) (smoothOrthoFrame g x i x) tail
  exact (congrArg (fun T => T tail) hH).symm.trans hTotal.symm

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem rawBundleConnLap_multilinear_eq_roughLap0SField
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s) (x : M) :
    rawBundleConnLap g ((LeviCivita g).multilinear s) (fun y => A y) x =
      roughLap0SField g A x := by
  exact rawBundleConnLap_multilinear_eq_roughLap0STensor g A
    (totalNabla0S_regularity s (metricCov g) (metricCov_smooth g) A) x

end DifferentialGeometry.PDE.RicciFlow
