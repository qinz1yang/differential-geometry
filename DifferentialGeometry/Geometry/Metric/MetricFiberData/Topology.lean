import DifferentialGeometry.Geometry.Metric.MetricFiberData.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Topology.VectorBundle.Riemannian

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Tensor0SBundle.MetricFiberData

section Topological

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

def innerCLM (D : MetricFiberData V) : V →L[ℝ] V →L[ℝ] ℝ :=
  D.flat.toLinearMap.toContinuousBilinearMap

@[simp] theorem innerCLM_apply (D : MetricFiberData V) (v w : V) :
    D.innerCLM v w = D.inner v w := rfl

theorem continuous_inner (D : MetricFiberData V) :
    Continuous (fun p : V × V => D.inner p.1 p.2) := by
  let _ : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  exact IsModuleTopology.continuous_bilinear_of_finite_left D.flat.toLinearMap

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]

theorem exists_metric_continuousLinearEquiv
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (hfin : Module.finrank ℝ V = Module.finrank ℝ W) :
    ∃ e : V ≃L[ℝ] W, ∀ v w, DW.inner (e v) (e w) = DV.inner v w := by
  obtain ⟨e, he⟩ := exists_metric_linearEquiv DV DW hfin
  exact ⟨e.toContinuousLinearEquiv, he⟩

theorem isCompact_inner_self_le (D : MetricFiberData V) (R : ℝ) :
    IsCompact {v : V | D.inner v v ≤ R} := by
  let W := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  obtain ⟨e, he⟩ := D.exists_metric_continuousLinearEquiv (ofInnerProductSpace (F := W)) (by simp [W])
  have hnorm (v : V) : D.inner v v = ‖e v‖ ^ 2 := by
    rw [← he, ofInnerProductSpace_inner, real_inner_self_eq_norm_sq]
  by_cases hR : 0 ≤ R
  · have hset : {v : V | D.inner v v ≤ R} = e ⁻¹' Metric.closedBall 0 (Real.sqrt R) := by
      ext v
      rw [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hnorm]
      exact (Real.le_sqrt (norm_nonneg _) hR).symm
    rw [hset]
    exact e.toHomeomorph.isCompact_preimage.mpr (ProperSpace.isCompact_closedBall 0 (Real.sqrt R))
  · have hset : {v : V | D.inner v v ≤ R} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hR ((D.inner_nonneg v).trans hv)
    rw [hset]
    exact isCompact_empty

theorem isVonNBounded_inner_self_lt (D : MetricFiberData V) (R : ℝ) :
    Bornology.IsVonNBounded ℝ {v : V | D.inner v v < R} := by
  apply Bornology.IsVonNBounded.subset (s₂ := {v : V | D.inner v v ≤ R})
    ?_ ((D.isCompact_inner_self_le R).isVonNBounded ℝ)
  intro v hv
  change D.inner v v < R at hv
  change D.inner v v ≤ R
  exact hv.le

end Topological

section Families

variable {B : Type*} {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [∀ b, T2Space (V b)] [∀ b, FiniteDimensional ℝ (V b)]

def riemannianMetric (D : ∀ b, MetricFiberData (V b)) : Bundle.RiemannianMetric V where
  inner b := (D b).innerCLM
  symm b := (D b).inner_comm
  pos b v hv := (D b).inner_pos_of_ne_zero (v := v) hv
  continuousAt b := ((D b).continuous_inner.comp (continuous_id.prodMk continuous_id)).continuousAt
  isVonNBounded b := (D b).isVonNBounded_inner_self_lt 1

@[simp] theorem riemannianMetric_inner (D : ∀ b, MetricFiberData (V b))
    (b : B) (v w : V b) :
    (riemannianMetric D).inner b v w = (D b).inner v w := rfl

end Families

end DifferentialGeometry.Tensor0SBundle.MetricFiberData
