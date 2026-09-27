import DifferentialGeometry.Geometry.Exponential.Defs
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

def minimizingDomain (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
    riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v))}

def extendibleMinimizingDomain (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ∃ c : ℝ, 1 < c ∧ c • v ∈ minimizingDomain (I := I) g p}

end DifferentialGeometry.Geometry.Riemannian.Exponential
