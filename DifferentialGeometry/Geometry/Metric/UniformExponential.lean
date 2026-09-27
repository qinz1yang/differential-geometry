import DifferentialGeometry.Geometry.Metric.UniformFiberInjectivity
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



theorem exists_uniform_diagExp_injective (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (diagExp (I := I) g hg)
      {u : TangentBundle I M | Real.sqrt (g.inner u.proj u.2 u.2) ≤ ε} := by
  apply exists_uniform_fiber_injectivity g (diagExp (I := I) g hg)
  · intro u v huv
    exact congrArg Prod.fst huv
  · intro x
    let B := standardDiagonalInverseBranch (I := I) g hg x
    refine ⟨B.hom.source, B.hom.open_source, B.zero_mem, ?_⟩
    intro u hu v hv huv
    apply B.hom.injOn hu hv
    exact (B.hom_eq hu).trans (huv.trans (B.hom_eq hv).symm)

end DifferentialGeometry.Geometry
