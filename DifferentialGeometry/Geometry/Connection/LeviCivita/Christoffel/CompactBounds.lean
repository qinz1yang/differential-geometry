import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Bounds
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity
import Mathlib.Topology.Order.Compact


noncomputable section

open Manifold Set
open scoped ContDiff Manifold BigOperators

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_norm_chartChristoffel_le_of_isCompact
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ interior (extChartAt I p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ i j k,
      ‖chartChristoffel g p i j k x‖ ≤ C := by
  classical
  let F : E → ℝ := fun x => ∑ i, ∑ j, ∑ k, ‖chartChristoffel g p i j k x‖
  have hF : ContinuousOn F K := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply continuousOn_finsetSum
    intro k _
    exact ((chartChristoffel_contDiffOn_interior g p i j k).continuousOn.mono hKt).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hF
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx i j k
  have hk : ‖chartChristoffel g p i j k x‖ ≤
      ∑ c, ‖chartChristoffel g p i j c x‖ :=
    Finset.single_le_sum (f := fun c => ‖chartChristoffel g p i j c x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have hj : (∑ c, ‖chartChristoffel g p i j c x‖) ≤
      ∑ b, ∑ c, ‖chartChristoffel g p i b c x‖ :=
    Finset.single_le_sum (f := fun b => ∑ c, ‖chartChristoffel g p i b c x‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  have hi : (∑ b, ∑ c, ‖chartChristoffel g p i b c x‖) ≤ F x :=
    Finset.single_le_sum (f := fun a => ∑ b, ∑ c, ‖chartChristoffel g p a b c x‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  exact (hk.trans (hj.trans hi)).trans ((hB (mem_image_of_mem F hx)).trans (le_max_left _ _))

end DifferentialGeometry.Geometry.Connection
