import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundleCompactness
import DifferentialGeometry.Geometry.Metric.BundleInnerSelf

/-!
# The soul's normal bundle is a smooth Riemannian bundle

The fibre `normalBundleFiber g S q = normalSpace g S q` is a submodule of `TangentSpace I q`, so it
carries the restricted inner product of the ambient Riemannian bundle structure. When the ambient
norm is the norm of `g` (`IsMetricNorm`), this fibre inner product is `g` itself, and the squared
fibre norm on the total space of the normal bundle is the composite of the smooth squared length
on `TangentBundle I M` with the smooth inclusion `normalBundleInclusion`. The criterion
`isContMDiffRiemannianBundle_of_contMDiff_inner_self` then gives the smooth Riemannian structure.
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
/-- The fibre inner product of the soul's normal bundle is the metric `g`. -/
theorem normalBundleFiber_inner_eq {g : SmoothRiemannianMetric I M}
    (hEnorm : IsMetricNorm (I := I) g) {S : Set M} (q : S) (v w : normalBundleFiber g S q) :
    inner ℝ v w = g.inner q.1 v.1 w.1 := by
  rw [Submodule.coe_inner]
  exact hEnorm.inner_eq q.1 v.1 w.1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] in
/-- The fibre norm of the soul's normal bundle is the `g`-length. -/
theorem normalBundleFiber_norm_eq {g : SmoothRiemannianMetric I M}
    (hEnorm : IsMetricNorm (I := I) g) {S : Set M} (q : S) (v : normalBundleFiber g S q) :
    ‖v‖ = Real.sqrt (g.inner q.1 v.1 v.1) := by
  rw [← normalBundleFiber_inner_eq hEnorm q v v, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]

variable [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **The soul's normal bundle is a smooth Riemannian bundle** (fibre inner product `g`). -/
theorem normalBundle_isContMDiffRiemannianBundle (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {S : Set M} (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    IsContMDiffRiemannianBundle 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞
      (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) (normalBundleFiber g S) := by
  intro hS _ a _ _ _
  apply DifferentialGeometry.Geometry.Metric.isContMDiffRiemannianBundle_of_contMDiff_inner_self
  have hinc := normalBundleInclusion_contMDiff g hEnorm hconv hB
  refine ((tangentSquaredLength_contMDiff g).comp hinc).congr fun z => ?_
  exact normalBundleFiber_inner_eq hEnorm z.proj z.2 z.2

end DifferentialGeometry.Geometry.Topology
