import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle

noncomputable def hessTensorAt
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    Tensor0SSpace (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ).symm.toContinuousLinearMap).comp
    (hessFun (I := I) g f x).toContinuousBilinearMap).uncurryLeft

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem hessTensorAt_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessTensorAt (I := I) g f x (vec2 (I := I) v w) =
      hessFun (I := I) g f x v w := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lap_eq_hess_on [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hx : x ∈ U) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g f x) := by
  classical
  let basis :
      Module.Basis (CoordinateIdx (𝕜 := ℝ) E) ℝ (TangentSpace I x) :=
    coordinateFrameAt_toBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := ℝ) E → CoordinateIdx (𝕜 := ℝ) E → ℝ :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j
        (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  unfold laplacian divergence
  rw [linearMap_trace_eq_sum_inv_inner_apply
    (I := I) g x basis gInv hinv
    ((LeviCivita (I := I) g).toFun
      (fun y => gradientFun (I := I) g f y) x).toLinearMap]
  rw [metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv (hessTensorAt (I := I) g f x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hessTensorAt_apply]
  rw [hessFun_eq_cov_local (I := I) g hU hf hx]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem laplacian_eq_chart_hessian_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          chartHessianTensor (I := I) g α f i j x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hbase
  let gInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g α x i j
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv := by
    intro i j
    constructor
    · have hmatrix := congrArg (fun A => A i j)
        (chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv,
        chartBasisFamily_apply] using hmatrix
    · have hmatrix := congrArg (fun A => A i j)
        (chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase)
      simpa [Matrix.mul_apply, Matrix.one_apply, basis, gInv,
        chartBasisFamily_apply] using hmatrix
  rw [lap_eq_hess_on (I := I) g isOpen_univ hf.contMDiffOn (Set.mem_univ x)]
  rw [metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv (hessTensorAt (I := I) g f x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change gInv i j * hessFun (I := I) g f x (basis i) (basis j) = _
  rw [hessFun_eq_cov_local (I := I) g isOpen_univ hf.contMDiffOn
    (Set.mem_univ x)]
  rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf]
  change chartInvGramMatrix (I := I) g α x i j *
      abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) = _
  rw [chartAlphaMatrixIdentity_holds (I := I) g α hf hx i j]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem connLaplacian_function_eq_chartLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g ⟨_, hf⟩ x := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_abstractHessian_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      Δ_g (I := I) g ⟨_, hf⟩ x := by
  classical
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  have h2 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h3 : chartHessTrace (I := I) g f x = Δ_g (I := I) g ⟨_, hf⟩ x :=
    chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x
  rw [← h1, h2, h3]

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_abstractHessian_eq_connLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      connLaplacian_function (I := I) g hf x := by
  rw [connLaplacian_function_eq_chartLaplacian (I := I) g hf x]
  exact traceFun_abstractHessian_eq_laplacian (I := I) g hf x h_orth

end Connection
end Geometry
end DifferentialGeometry
