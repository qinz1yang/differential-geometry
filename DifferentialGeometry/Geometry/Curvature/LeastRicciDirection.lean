import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.EigenvectorAxisEstimate
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData

noncomputable section
open scoped Manifold ContDiff InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_least_ricci_direction_of_axis_error
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (hv : g.inner x v v = 1)
    (κ ε : ℝ) (hκ : 0 < κ) (hε : ε < κ / 2)
    (herror : ∀ z : TangentSpace I x,
      let d := ricciSharp g x z - κ • (z - (g.inner x v z) • v)
      Real.sqrt (g.inner x d d) ≤ ε * Real.sqrt (g.inner x z z)) :
    ∃ (μ : ℝ) (w : TangentSpace I x), g.inner x w w = 1 ∧
      ricciSharp g x w = μ • w ∧
      (∀ z : TangentSpace I x, g.inner x z z = 1 → μ ≤ ricciTensor g x z z) ∧
      |μ| ≤ ε ∧ 0 < g.inner x v w ∧
      Real.sqrt (g.inner x (w - v) (w - v)) ≤ 4 * ε / κ ∧
      Module.End.eigenspace (ricciSharp g x).toLinearMap μ = Submodule.span ℝ {w} := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hi (a b : TangentSpace I x) : ⟪a, b⟫_ℝ = g.inner x a b := by
    exact (MetricFiberData.toCore_inner D a b).trans
      (TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen g x) a b)
  have hn (a : TangentSpace I x) : ‖a‖ = Real.sqrt (g.inner x a a) := by
    rw [← hi, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  let : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ (TangentSpace I x)
  let A := Module.End.toContinuousLinearMap (TangentSpace I x) (ricciSharp g x).toLinearMap
  have hA : IsSelfAdjoint A := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro a b
    change ⟪A a, b⟫_ℝ = ⟪a, A b⟫_ℝ
    rw [hi, hi]
    change g.inner x (ricciSharp g x a) b = g.inner x a (ricciSharp g x b)
    rw [inner_ricciSharp, inner_ricciSharp_right, ricciTensor_symm g x a b]
  have hvn : ‖v‖ = 1 := by rw [hn, hv, Real.sqrt_one]
  have he (z : TangentSpace I x) :
      ‖A z - κ • (z - ⟪v, z⟫_ℝ • v)‖ ≤ ε * ‖z‖ := by
    rw [hn, hn, hi]
    exact herror z
  obtain ⟨μ, w, hw, heig, hmin, hμ, hpos, hdist, hspace⟩ :=
    DifferentialGeometry.Analysis.exists_least_eigenvector_close_to_axis A hA v hvn hκ hε he
  have hwg : g.inner x w w = 1 := by
    rw [← hi, real_inner_self_eq_norm_sq, hw]
    norm_num
  refine ⟨μ, w, hwg, heig, ?_, hμ, ?_, ?_, hspace⟩
  · intro z hz
    have hzn : ‖z‖ = 1 := by rw [hn, hz, Real.sqrt_one]
    have h := hmin z hzn
    rw [hi] at h
    exact h.trans_eq (inner_ricciSharp g x z z)
  · rwa [hi] at hpos
  · rwa [hn] at hdist

end DifferentialGeometry.Geometry.Curvature
