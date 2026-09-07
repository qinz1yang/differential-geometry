import DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla

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

def selfAdjoint
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  letI := S.totalSpaceTopology
  letI := S.fiberBundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov)

theorem selfAdjoint_subtypeVal
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (v : TangentSpace I x),
      (cov.selfAdjoint hcov A x v : V x →L[ℝ] V x) =
        DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
          (fun y => (A y : V y →L[ℝ] V y)) x v := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict_subtypeVal S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov)

theorem contMDiff_selfAdjoint
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [ContMDiffCovariantDerivative cov ∞] :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffCovariantDerivative (cov.selfAdjoint hcov) ∞ := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.contMDiff_restrict S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov) inferInstance

end CovariantDerivative
