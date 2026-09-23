import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem scalar_le_two_mul_of_time_distance_le
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {t u : ℝ} (ht : t ∈ Ioo a s) (hu : u ∈ Ioo a s)
    (hqQ : q ≤ Q) (hscalar : G.flow.scalar t x ≤ Q)
    (htime : 2 * C * |u - t| * Q ≤ 1) : G.flow.scalar u x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hlipschitz : LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Ioo a s) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
      (r' := fun t => derivWithin (fun v => G.flow.scalar v x) (Iic t) t) hq ordConnected_Ioo
    · intro v hv
      exact (G.equation.scalarTime (K := Ioo a s) hv Ioo_subset_Ico_self x).continuousWithinAt
    · intro v hv _
      exact hasDerivWithinAt_left_of_mem_nhdsLE
        (G.equation.scalarTime (K := Ioo a s) hv Ioo_subset_Ico_self x)
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hv.1 hv.2))
    · exact hbound
  have hlip := hlipschitz.dist_le_mul u hu t ht
  rw [Real.dist_eq, Real.dist_eq] at hlip
  have htpos : 0 < max q (G.flow.scalar t x) := hq.trans_le (le_max_left _ _)
  have hup : 0 < max q (G.flow.scalar u x) := hq.trans_le (le_max_left _ _)
  have hinv : Q⁻¹ ≤ (max q (G.flow.scalar t x))⁻¹ :=
    inv_anti₀ htpos (max_le hqQ hscalar)
  have hhalf : C * |u - t| ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlow : (2 * Q)⁻¹ ≤ (max q (G.flow.scalar u x))⁻¹ := by
    have hab := (abs_le.mp hlip).1
    rw [htwo] at hinv
    linarith
  have hupper : max q (G.flow.scalar u x) ≤ 2 * Q :=
    (inv_le_inv₀ (by positivity : 0 < 2 * Q) hup).mp hlow
  exact (le_max_right _ _).trans hupper

theorem TerminalLimitMetric.scalar_le_two_mul_of_time_sub_le
    (L : G.TerminalLimitMetric) {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ Ioo a s)
    (hqQ : q ≤ Q) (hscalar : G.flow.scalar t x.val ≤ Q)
    (htime : 2 * C * (s - t) * Q ≤ 1) : metricScalarAt L.metric x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  apply le_of_tendsto (L.tendsto_metricScalarAt x)
  filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
  have hsmall : 2 * C * |u - t| * Q ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2.le t) (by positivity)) hQ.le
  exact G.scalar_le_two_mul_of_time_distance_le hq x.val hbound ht
    ⟨ht.1.trans hu.1, hu.2⟩ hqQ hscalar hsmall

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
