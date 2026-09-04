import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Generic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sqrt_inner_add_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) <=
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have hnorm : ∀ z : TangentSpace I x,
      Real.sqrt (g.inner x z z) = ‖z‖ := by
    intro z
    rw [← TangentMetricDataGen.inner_eq_gen
      (tangentMetricDataGen (I := I) g x) z z]
    change Real.sqrt (D.inner z z) = ‖z‖
    rw [← MetricFiberData.toCore_inner D z z,
      real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]
  rw [hnorm, hnorm, hnorm]
  exact norm_add_le v w

theorem sqrt_inner_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (c : Real) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  have hnorm : ∀ z : TangentSpace I x,
      Real.sqrt (g.inner x z z) = ‖z‖ := by
    intro z
    rw [← TangentMetricDataGen.inner_eq_gen
      (tangentMetricDataGen (I := I) g x) z z]
    change Real.sqrt (D.inner z z) = ‖z‖
    rw [← MetricFiberData.toCore_inner D z z,
      real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]
  rw [hnorm, hnorm, norm_smul, Real.norm_eq_abs]

omit [FiniteDimensional ℝ E] in
theorem inner_sum_orthonormal (g : SmoothRiemannianMetric I M) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → TangentSpace I x)
    (hON : ∀ i j, g.inner x (v i) (v j) = if i = j then (1 : ℝ) else 0)
    (c : ι → ℝ) :
    g.inner x (∑ i, c i • v i) (∑ j, c j • v j) = ∑ i, c i ^ 2 := by
  have hexp : ∀ i, (g.inner x (v i)) (∑ j, c j • v j) = c i := by
    intro i
    rw [map_sum]
    have hterm : ∀ j, (g.inner x (v i)) (c j • v j) = if i = j then c j else 0 := by
      intro j
      rw [map_smul, smul_eq_mul, hON i j]
      by_cases h : i = j <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp
  have houter : (g.inner x) (∑ i, c i • v i) = ∑ i, c i • (g.inner x (v i)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [houter, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, smul_eq_mul, hexp i, sq]

theorem expand_orthonormal (g : SmoothRiemannianMetric I M) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I x))
    (v : ι → TangentSpace I x)
    (hON : ∀ i j, g.inner x (v i) (v j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ i, g.inner x (v i) u • v i := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hg : ∀ a b : TangentSpace I x, g.inner x a b = Inner.inner ℝ a b := by
    intro a b
    rw [← TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen (I := I) g x) a b]
    change D.inner a b = Inner.inner ℝ a b
    exact (MetricFiberData.toCore_inner D a b).symm
  have hONi : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← hg]
    exact hON i j
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) :=
    ge_of_eq (hONi.linearIndependent.span_eq_top_of_card_eq_finrank hcard)
  let b : OrthonormalBasis ι ℝ (TangentSpace I x) := OrthonormalBasis.mk hONi hspan
  have hb : ∀ i, b i = v i := by
    intro i
    change (OrthonormalBasis.mk hONi hspan) i = v i
    rw [OrthonormalBasis.coe_mk]
  calc u = ∑ i, (Inner.inner ℝ (b i) u : ℝ) • b i := (b.sum_repr' u).symm
    _ = ∑ i, g.inner x (v i) u • v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hb i, hg]

theorem inner_self_eq_sum_sq (g : SmoothRiemannianMetric I M) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I x))
    (v : ι → TangentSpace I x)
    (hON : ∀ i j, g.inner x (v i) (v j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    g.inner x u u = ∑ i, (g.inner x (v i) u) ^ 2 := by
  conv_lhs => rw [expand_orthonormal g x hcard v hON u]
  exact inner_sum_orthonormal g x v hON _

end Riemannian
end Geometry
end DifferentialGeometry
