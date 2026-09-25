import DifferentialGeometry.Analysis.Calculus.Derivative.Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureConvergence
import DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem TerminalLimitMetric.extendedScalar_continuousOn
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcs : c < s)
    (x : G.terminalRegularOpen) :
    ContinuousOn (fun t => metricScalarAt (L.extendedMetric t) x) (Icc c s) := by
  have hgram := chartGramMatrix_joint_contMDiffOn L.extendedMetric (Icc c s)
    (L.extendedMetric_jointContMDiffOn hac hcs)
  intro t ht
  exact (scalarTime_of_joint L.extendedMetric (Icc c s) (uniqueDiffOn_Icc hcs) hgram
    t ht x).continuousWithinAt

private theorem TerminalLimitMetric.extendedScalar_differentiableAt
    (L : G.TerminalLimitMetric) {c t : ℝ} (hac : a ≤ c) (hcs : c < s)
    (ht : t ∈ Ioo c s) (x : G.terminalRegularOpen) :
    DifferentiableAt ℝ (fun t => metricScalarAt (L.extendedMetric t) x) t := by
  have hgram := chartGramMatrix_joint_contMDiffOn L.extendedMetric (Icc c s)
    (L.extendedMetric_jointContMDiffOn hac hcs)
  exact (scalarTime_of_joint L.extendedMetric (Icc c s) (uniqueDiffOn_Icc hcs) hgram
    t ⟨ht.1.le, ht.2.le⟩ x).differentiableAt (Icc_mem_nhds ht.1 ht.2)

private theorem TerminalLimitMetric.extendedScalar_deriv_eq_incoming
    (L : G.TerminalLimitMetric) {c t : ℝ} (hac : a ≤ c)
    (ht : t ∈ Ioo c s) (x : G.terminalRegularOpen) :
    deriv (fun t => metricScalarAt (L.extendedMetric t) x) t =
      derivWithin (fun t => G.flow.scalar t x.val) (Iic t) t := by
  have heq : (fun t => metricScalarAt (L.extendedMetric t) x) =ᶠ[𝓝 t]
      (fun t => G.flow.scalar t x.val) := by
    filter_upwards [Iio_mem_nhds ht.2] with t hts
    rw [L.extendedMetric_before hts, metricScalarAt_restrictOpen]
    rfl
  have hd : DifferentiableAt ℝ (fun t => G.flow.scalar t x.val) t :=
    (G.equation.scalarTime (K := Ioo a s) ⟨hac.trans_lt ht.1, ht.2⟩
      Ioo_subset_Ico_self x.val).differentiableAt (Ioo_mem_nhds (hac.trans_lt ht.1) ht.2)
  exact heq.deriv_eq.trans (hd.derivWithin (uniqueDiffWithinAt_Iic t)).symm


theorem TerminalLimitMetric.abs_scalar_time_derivWithin_le_of_incoming_bound
    (L : G.TerminalLimitMetric) {c C q : ℝ} (hac : a ≤ c) (hcs : c < s)
    (x : G.terminalRegularOpen) (hq : q < metricScalarAt L.metric x)
    (hbound : ∀ t ∈ Ioo c s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) :
    |derivWithin (fun t => metricScalarAt (L.extendedMetric t) x) (Iic s) s| ≤
      C * metricScalarAt L.metric x ^ 2 := by
  have hsq := DifferentialGeometry.Analysis.abs_derivWithin_Iic_le_mul_sq_of_interior_bound
    (fun t => metricScalarAt (L.extendedMetric t) x) hcs
    (L.extendedScalar_continuousOn hac hcs x)
    (fun t ht => L.extendedScalar_differentiableAt hac hcs ht x)
    (by simpa only [L.extendedMetric_terminal] using hq) (C := C)
  rw [L.extendedMetric_terminal] at hsq
  apply hsq
  intro t ht hqt
  rw [L.extendedScalar_deriv_eq_incoming hac ht x]
  have heq : metricScalarAt (L.extendedMetric t) x = G.flow.scalar t x.val := by
    rw [L.extendedMetric_before ht.2, metricScalarAt_restrictOpen]
    rfl
  rw [heq] at hqt ⊢
  exact hbound t ht hqt

private theorem scalar_differential_eq_chart
    (g : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen)
    (x : G.terminalRegularOpen) (v : TangentSpace ThreeModel x) :
    (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt g) x v) =
      fderiv ℝ (scalarOnE (I := ThreeModel) x (metricScalarAt g)) (extChartAt ThreeModel x x)
        ((trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x v) := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.mfderiv_eq_fderivWithin_scalarOnE
    x (mem_chart_source _ _) ((metricScalar_smooth g).mdifferentiableAt (by simp)) v]
  rw [fderivWithin_of_mem_nhds ((isOpen_extChartAt_target (I := ThreeModel) x).mem_nhds (mem_extChartAt_target (I := ThreeModel) x))]

private theorem extended_scalar_chart_fderiv_continuousOn
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) :
    ContinuousOn (fun z : ℝ × ThreeSpace =>
      fderiv ℝ (scalarOnE (I := ThreeModel) x (metricScalarAt (L.extendedMetric z.1))) z.2)
      (Icc a s ×ˢ interior (extChartAt ThreeModel x).target) := by
  let S : SolutionOn (I := ThreeModel) (M := G.terminalRegularOpen)
      (RealTimeInterval.closed a s G.lt.le) := { base := { metric := L.extendedMetric } }
  exact S.scalarOnE_spatial_fderiv_continuousOn_of_joint_metric (I := ThreeModel)
    (Icc a s) (L.extendedMetric_jointContMDiffOn le_rfl G.lt) x

private theorem chart_self_mem_interior_target (x : G.terminalRegularOpen) :
    extChartAt ThreeModel x x ∈ interior (extChartAt ThreeModel x).target := by
  rw [(isOpen_extChartAt_target (I := ThreeModel) x).interior_eq]
  exact mem_extChartAt_target (I := ThreeModel) x

private theorem continuousOn_fixed_snd {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X × Y → Z} {J : Set X} {K : Set Y} (hf : ContinuousOn f (J ×ˢ K))
    {y : Y} (hy : y ∈ K) : ContinuousOn (fun t => f (t, y)) J :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, hy⟩)

private theorem extended_scalar_chart_fderiv_at_continuousOn
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) :
    ContinuousOn
      (fun t => fderiv ℝ (scalarOnE (I := ThreeModel) x (metricScalarAt (L.extendedMetric t)))
        (extChartAt ThreeModel x x)) (Icc a s) :=
  continuousOn_fixed_snd (extended_scalar_chart_fderiv_continuousOn L x)
    (chart_self_mem_interior_target x)

private theorem extended_scalar_differential_continuousOn
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) (v : TangentSpace ThreeModel x) :
    ContinuousOn
      (fun t => (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (L.extendedMetric t)) x v))
      (Icc a s) := by
  have hcomp := extended_scalar_chart_fderiv_at_continuousOn L x
  let w : ThreeSpace :=
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x v
  have heval : ContinuousOn (fun t =>
      fderiv ℝ (scalarOnE (I := ThreeModel) x (metricScalarAt (L.extendedMetric t)))
        (extChartAt ThreeModel x x) w) (Icc a s) :=
    hcomp.clm_apply continuousOn_const
  have heq : (fun t => (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (metricScalarAt (L.extendedMetric t)) x v)) =
      (fun t => fderiv ℝ (scalarOnE (I := ThreeModel) x (metricScalarAt (L.extendedMetric t)))
        (extChartAt ThreeModel x x) w) := by
    funext t
    exact scalar_differential_eq_chart (L.extendedMetric t) x v
  rw [heq]
  exact heval

theorem TerminalLimitMetric.tendsto_scalar_differential
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) (v : TangentSpace ThreeModel x) :
    Tendsto (fun t => (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (metricScalarAt ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)) x v))
      (𝓝[<] s) (𝓝 (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt L.metric) x v)) := by
  have hd := extended_scalar_differential_continuousOn L x v
  have hlim := (hd s ⟨G.lt.le, le_rfl⟩).mono Ioc_subset_Icc_self
  change Tendsto _ (𝓝[Ioc a s] s) _ at hlim
  rw [nhdsWithin_Ioc_eq_nhdsLE G.lt] at hlim
  have hlim' := hlim.mono_left (nhdsWithin_mono s Iio_subset_Iic_self)
  change Tendsto _ _ (𝓝 (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
    (metricScalarAt (L.extendedMetric s)) x v)) at hlim'
  rw [L.extendedMetric_terminal] at hlim'
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [L.extendedMetric_before ht]

private theorem scalar_differential_restrictOpen
    (g : P.Metric) (x : G.terminalRegularOpen) (v : TangentSpace ThreeModel x) :
    (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (metricScalarAt (g.restrictOpen G.terminalRegularOpen)) x v) =
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt g) x.val v) := by
  have heq : metricScalarAt (g.restrictOpen G.terminalRegularOpen) =
      (metricScalarAt g) ∘ (Subtype.val : G.terminalRegularOpen → P.Carrier) := by
    funext y
    exact metricScalarAt_restrictOpen g G.terminalRegularOpen y
  rw [heq, mfderiv_comp x ((metricScalar_smooth g).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val : ContMDiff ThreeModel ThreeModel ∞
      (Subtype.val : G.terminalRegularOpen → P.Carrier)).mdifferentiableAt (by simp)),
    ContinuousLinearMap.comp_apply,
    DifferentialGeometry.mfderiv_subtype_val_apply]

theorem TerminalLimitMetric.scalar_differential_le_of_incoming_bound
    (L : G.TerminalLimitMetric) {c C q : ℝ} (hcs : c < s)
    (x : G.terminalRegularOpen) (hq : q < metricScalarAt L.metric x)
    (hbound : ∀ t ∈ Ioo a s, c ≤ t → q < G.flow.scalar t x.val →
      ∀ v : TangentSpace ThreeModel x.val,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (G.flow.scalar t) x.val v)| ≤
          C * G.flow.scalar t x.val * Real.sqrt (G.flow.scalar t x.val) *
            Real.sqrt ((G.flow.base.metric t).inner x.val v v))
    (v : TangentSpace ThreeModel x) :
    |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt L.metric) x v)| ≤
      C * metricScalarAt L.metric x * Real.sqrt (metricScalarAt L.metric x) *
        Real.sqrt (L.metric.inner x v v) := by
  have hscalar := L.tendsto_metricScalarAt x
  have hinner := L.tendsto_inner x v v
  have hright := (((tendsto_const_nhds (x := C)).mul hscalar).mul hscalar.sqrt).mul hinner.sqrt
  apply le_of_tendsto_of_tendsto (L.tendsto_scalar_differential x v).abs hright
  filter_upwards [Ioo_mem_nhdsLT G.lt, Ioo_mem_nhdsLT hcs,
    hscalar.eventually_const_lt hq] with t ht hct hqt
  rw [scalar_differential_restrictOpen, SmoothRiemannianMetric.restrictOpen_inner]
  exact hbound t ht hct.1.le hqt v

theorem TerminalLimitMetric.scalar_derivative_bounds_of_canonical_on_time_window
    (L : G.TerminalLimitMetric) {c eps C1 C2 q : ℝ} (hac : a ≤ c) (hcs : c < s)
    (hcanonical : ∀ y : P.Carrier, ∀ t ∈ Ioo c s, q < G.flow.scalar t y →
      Nonempty (Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness G.flow eps C1 C2 y t))
    (x : G.terminalRegularOpen) (hq : q < metricScalarAt L.metric x) :
    (∀ v : TangentSpace ThreeModel x,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt L.metric) x v)| ≤
        C2 * metricScalarAt L.metric x * Real.sqrt (metricScalarAt L.metric x) *
          Real.sqrt (L.metric.inner x v v)) ∧
    |derivWithin (fun t => metricScalarAt (L.extendedMetric t) x) (Iic s) s| ≤
      C2 * metricScalarAt L.metric x ^ 2 := by
  obtain ⟨d, hcd, hds⟩ := exists_between hcs
  constructor
  · apply L.scalar_differential_le_of_incoming_bound hds x hq
    intro t ht hdt hqt v
    exact (hcanonical x.val t ⟨hcd.trans_le hdt, ht.2⟩ hqt).some.gradient v
  · exact L.abs_scalar_time_derivWithin_le_of_incoming_bound hac hcs x hq
      (fun t ht hqt => (hcanonical x.val t ht hqt).some.time_derivative)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end
