import DifferentialGeometry.Geometry.Connection.Hessian.Restriction
import DifferentialGeometry.Geometry.Connection.Laplacian.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
variable [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
variable [IsContMDiffRiemannianBundle I ∞ F V]

namespace CovariantDerivative

theorem selfAdjoint_hessian_subtypeVal
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (X Y : TangentSpace I x),
      ((cov.selfAdjoint hcov).hessian base A x X Y : V x →L[ℝ] V x) =
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov).hessian base (fun y => (A y : V y →L[ℝ] V y)) x X Y := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict_hessian_subtypeVal S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov) base

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

theorem rawBundleConnLap_selfAdjoint_subtypeVal
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M),
      (rawBundleConnLap g (cov.selfAdjoint hcov) A x : V x →L[ℝ] V x) =
        rawBundleEndomorphismConnLap g cov (fun y => (A y : V y →L[ℝ] V y)) x := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact rawBundleConnLap_restrict_subtypeVal g
    (HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov) S
    (HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint cov hcov)

end DifferentialGeometry.Geometry.Connection
