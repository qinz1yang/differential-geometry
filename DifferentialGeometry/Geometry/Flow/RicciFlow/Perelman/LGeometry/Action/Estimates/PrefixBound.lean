import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedAction_prefix_le_of_action_le
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a d b v A B : ℝ} (ha : 0 ≤ a) (had : a ≤ d) (hdb : d ≤ b) (hbv : b ≤ v)
    (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ Ioo d b, -B ≤ S.scalar (T - t ^ 2) (α t))
    (hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hact : lRegularizedAction S T α a b ≤ A) :
    lRegularizedAction S T α a d ≤ A + 2 * B * v ^ 2 * (b - d) := by
  have hab := had.trans hdb
  have hleft := hint.mono_set (by
    rw [uIcc_of_le had, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hdb)
  have hright := hint.mono_set (by
    rw [uIcc_of_le hdb, uIcc_of_le hab]
    exact Icc_subset_Icc had le_rfl)
  have htail := lRegularizedAction_ge_of_scalar_lower_on_interior S T α
    (ha.trans had) hdb hbv hB hscalar hright
  have hadd := lRegularizedAction_add S T α a d b hleft hright
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
