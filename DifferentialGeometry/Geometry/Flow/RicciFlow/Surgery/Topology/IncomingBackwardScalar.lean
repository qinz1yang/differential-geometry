import DifferentialGeometry.Analysis.Calculus.Derivative.SuperlevelMonotonicity
import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem lipschitzOnWith_inv_max_scalar_at
    (G : P.IncomingSlab a s) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤
        C * G.flow.scalar t x ^ 2) :
    LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Ico a s) := by
  have hlip : LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Ioo a s) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
      (r' := fun t => derivWithin (fun v => G.flow.scalar v x) (Iic t) t)
      hq ordConnected_Ioo
    · intro t ht
      exact (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x).continuousWithinAt
    · intro t ht _
      exact DifferentialGeometry.Analysis.hasDerivWithinAt_left_of_mem_nhdsLE
        (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x)
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
    · exact hbound
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht v hv
  let b := (max t v + s) / 2
  have hmb : max t v < b := by dsimp [b]; linarith [max_lt ht.2 hv.2]
  have hbs : b < s := by dsimp [b]; linarith [max_lt ht.2 hv.2]
  have hab : a < b := (ht.1.trans (le_max_left _ _)).trans_lt hmb
  have hsub : Icc a b ⊆ Ico a s := fun z hz => ⟨hz.1, hz.2.trans_lt hbs⟩
  have hc : ContinuousOn (fun t => (max q (G.flow.scalar t x))⁻¹) (Icc a b) := by
    apply (continuous_max.comp_continuousOn (continuousOn_const.prodMk ?_)).inv₀
      (fun t _ => ne_of_gt (hq.trans_le (le_max_left _ _)))
    intro t ht
    exact (G.equation.scalarTime (hsub ht) Subset.rfl x).continuousWithinAt.mono hsub
  have hext : LipschitzOnWith C (fun t => (max q (G.flow.scalar t x))⁻¹) (Icc a b) := by
    rw [← closure_Ioo hab.ne]
    apply LipschitzOnWith.closure
    · simpa only [closure_Ioo hab.ne] using hc
    · exact hlip.mono (fun z hz => ⟨hz.1, hz.2.trans hbs⟩)
  exact hext.dist_le_mul t ⟨ht.1, (le_max_left _ _).trans hmb.le⟩
    v ⟨hv.1, (le_max_right _ _).trans hmb.le⟩


theorem scalar_le_two_mul_of_time_distance_le
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : P.Carrier)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {t u : ℝ} (ht : t ∈ Ioo a s) (hu : u ∈ Ioo a s)
    (hqQ : q ≤ Q) (hscalar : G.flow.scalar t x ≤ Q)
    (htime : 2 * C * |u - t| * Q ≤ 1) : G.flow.scalar u x ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hlipschitz := (G.lipschitzOnWith_inv_max_scalar_at hq x hbound).mono Ioo_subset_Ico_self
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

theorem monotoneOn_max_scalar_of_deriv_nonneg
    (G : P.IncomingSlab a s) {q : ℝ} (x : P.Carrier)
    (hderiv : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      0 ≤ derivWithin (fun v => G.flow.scalar v x) (Iic t) t) :
    MonotoneOn (fun t => max q (G.flow.scalar t x)) (Ico a s) := by
  apply DifferentialGeometry.Analysis.monotoneOn_max_of_deriv_nonneg_above ordConnected_Ico
  · intro t ht
    exact (G.equation.scalarTime ht Subset.rfl x).continuousWithinAt
  · intro t ht hq
    rw [interior_Ico] at ht
    have hd : DifferentiableAt ℝ (fun v => G.flow.scalar v x) t :=
      (G.equation.scalarTime (K := Ioo a s) ht Ioo_subset_Ico_self x).differentiableAt
        (Ioo_mem_nhds ht.1 ht.2)
    exact ⟨hd, by simpa only [hd.derivWithin (uniqueDiffWithinAt_Iic t)] using hderiv t ht hq⟩

theorem TerminalLimitMetric.max_scalar_le_terminal_of_deriv_nonneg
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) {q : ℝ} (x : G.terminalRegularOpen)
    (hderiv : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      0 ≤ derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t)
    {t : ℝ} (ht : t ∈ Ico a s) :
    max q (G.flow.scalar t x.val) ≤ max q (metricScalarAt L.metric x) := by
  apply ge_of_tendsto (tendsto_const_nhds.max (L.tendsto_metricScalarAt x))
  filter_upwards [Ioo_mem_nhdsLT ht.2] with v hv
  exact G.monotoneOn_max_scalar_of_deriv_nonneg x.val hderiv ht
    ⟨ht.1.trans hv.1.le, hv.2⟩ hv.1.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
