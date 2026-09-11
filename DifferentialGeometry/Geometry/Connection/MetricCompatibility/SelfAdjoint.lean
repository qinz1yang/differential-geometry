import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Subbundle
import DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Hom

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

namespace CovariantDerivative

theorem IsMetricCompatible.selfAdjoint
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    let g := homContMDiffRiemannianMetric (IB := I) (n := 1) (FU := F) (FV := F) V V
    letI : RiemannianBundle (fun y => V y →L[ℝ] V y) := ⟨g.toRiemannianMetric⟩
    let homNorm : ∀ y, NormedAddCommGroup (V y →L[ℝ] V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y => V y →L[ℝ] V y) y
    letI : ∀ y, SeminormedAddCommGroup (V y →L[ℝ] V y) :=
      fun y => (homNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y →L[ℝ] V y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := fun y => V y →L[ℝ] V y) y
    let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    letI := S.contMDiffVectorBundle
    letI := S.isContMDiffRiemannianBundle (by simp : (1 : WithTop ℕ∞) ≤ ∞)
    (cov.selfAdjoint hcov).IsMetricCompatible := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let g := homContMDiffRiemannianMetric (IB := I) (n := 1) (FU := F) (FV := F) V V
  let _ : RiemannianBundle (fun y => V y →L[ℝ] V y) := ⟨g.toRiemannianMetric⟩
  let homNorm : ∀ y, NormedAddCommGroup (V y →L[ℝ] V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun y => V y →L[ℝ] V y) y
  let _ : ∀ y, SeminormedAddCommGroup (V y →L[ℝ] V y) :=
    fun y => (homNorm y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (V y →L[ℝ] V y) := fun y =>
    Bundle.instInnerProductSpaceReal (E := fun y => V y →L[ℝ] V y) y
  let S := selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  let _ := S.isContMDiffRiemannianBundle (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isMetricCompatible
    cov hcov cov hcov).restrict S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov)

end CovariantDerivative
