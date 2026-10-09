import DifferentialGeometry.Analysis.ODE.QuadraticBackwardBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

/-!
# Scalar comparison on a genuine closed flow interval

The actual solution supplies scalar time regularity. A quadratic derivative
bound above a threshold controls the clipped reciprocal and therefore transfers
an upper bound from the terminal time to earlier points of the same interval.
Only interior derivatives are used; endpoints use the actual scalar continuity.
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I) (M := M) D}

/-- The reciprocal clipped at a positive scalar threshold is Lipschitz on the
actual closed interval, from a quadratic bound only above that threshold. -/
theorem IsSolutionOn.lipschitzOnWith_inv_max_scalar_Icc
    (hS : IsSolutionOn S) {a b q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hsub : Icc a b ⊆ D.carrier) (x : M)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2) :
    LipschitzOnWith C (fun v => (max q (S.scalar v x))⁻¹) (Icc a b) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    (r' := fun v => derivWithin (fun w => S.scalar w x) (Iic v) v) hq
  · intro v hv
    exact (hS.scalarTime hv hsub x).continuousWithinAt
  · intro v hv _
    have hd : DifferentiableAt ℝ (fun w => S.scalar w x) v :=
      (hS.scalarTime (K := Ioo a b) hv (Ioo_subset_Icc_self.trans hsub) x).differentiableAt
        (Ioo_mem_nhds hv.1 hv.2)
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic v)]
    exact hd.hasDerivAt
  · exact hbound

/-- A terminal scalar ceiling propagates backward by the actual quadratic
scalar-time bound, with its exact reciprocal time budget. -/
theorem IsSolutionOn.scalar_le_of_quadratic_time_bound
    (hS : IsSolutionOn S) {a b q A B t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hB : 0 < B) (hqA : q ≤ A)
    (hsub : Icc a b ⊆ D.carrier) (x : M)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2)
    (hend : S.scalar b x ≤ A) (ht : t ∈ Icc a b)
    (htime : C * (b - t) ≤ A⁻¹ - B⁻¹) : S.scalar t x ≤ B := by
  apply DifferentialGeometry.Analysis.ODE.le_of_quadratic_deriv_bound
    (r' := fun v => derivWithin (fun w => S.scalar w x) (Iic v) v)
    hA hB hqA ?_ ?_ hbound hend ht htime
  · intro v hv
    exact (hS.scalarTime hv hsub x).continuousWithinAt
  · intro v hv _
    have hd : DifferentiableAt ℝ (fun w => S.scalar w x) v :=
      (hS.scalarTime (K := Ioo a b) hv (Ioo_subset_Icc_self.trans hsub) x).differentiableAt
        (Ioo_mem_nhds hv.1 hv.2)
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic v)]
    exact hd.hasDerivAt

/-- A closed-interval two-multiple bound with the original same-point scalar
and derivative threshold. It assumes neither earlier curvature nor survival. -/
theorem IsSolutionOn.scalar_le_two_mul_of_quadratic_time_bound
    (hS : IsSolutionOn S) {a b q A t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hqA : q ≤ A) (hsub : Icc a b ⊆ D.carrier) (x : M)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2)
    (hend : S.scalar b x ≤ A) (ht : t ∈ Icc a b)
    (htime : C * A * (b - t) ≤ 1 / 2) : S.scalar t x ≤ 2 * A := by
  apply hS.scalar_le_of_quadratic_time_bound hA (by positivity) hqA hsub x hbound hend ht
  have hhalf : C * (b - t) ≤ (2 * A)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * A)]
    nlinarith only [htime]
  have htwo : A⁻¹ = 2 * (2 * A)⁻¹ := by field_simp
  linarith only [hhalf, htwo]

end DifferentialGeometry.PDE.RicciFlow
