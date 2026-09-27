import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman (FlowMetricBall)
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

theorem exists_incomingSlab_metric_eq (P : OrientedThreeStage.{u}) (g : P.Metric) (a : ℝ) :
    ∃ s : ℝ, a < s ∧ ∃ G : P.IncomingSlab a s, G.flow.base.metric a = g := by
  obtain ⟨d, had, Q, hinit, -, hjoint, -⟩ :=
    exists_completeBoundedCurvatureSolutionOn_from_time_of_compact (I := ThreeModel)
      (M := P.Carrier) g a
  obtain ⟨s, has, hsd⟩ := exists_between had
  exact ⟨s, has, IncomingSlab.ofClosedOpen P had Q.solution Q.isSolution hjoint has hsd, hinit⟩

namespace IncomingSlab

variable {P : OrientedThreeStage.{u}} {a : ℝ}

theorem hasDerivWithinAt_inner_Ici {s : ℝ} (G : P.IncomingSlab a s) {t : ℝ} (ht : t ∈ Ico a s)
    (x : P.Carrier) (v w : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun r => (G.flow.base.metric r).inner x v w)
      (-2 * ricciTensor (G.flow.base.metric t) x v w) (Ici a) t := by
  obtain ⟨c, htc, hcs⟩ := exists_between ht.2
  have hac : a < c := ht.1.trans_lt htc
  have h := metric_inner_hasDerivWithinAt_on_closed_interval G.flow G.equation hac
    (fun r hr => ⟨hr.1, hr.2.trans_lt hcs⟩) (fun r hr => ⟨hr.1, hr.2.trans hcs⟩)
    ⟨ht.1, htc.le⟩ x v w
  have hmem : Icc a c ∈ 𝓝[Ici a] t :=
    mem_of_superset (inter_mem_nhdsWithin (Ici a) (Iio_mem_nhds htc))
      (fun r hr => ⟨hr.1, le_of_lt hr.2⟩)
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor] using h.mono_of_mem_nhdsWithin hmem

theorem metric_eq_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a) :
    ∀ t ∈ Ico a (min s₁ s₂), G₁.flow.base.metric t = G₂.flow.base.metric t :=
  ricci_flow_forward_unique_of_joint_contMDiffOn G₁.flow.base.metric G₂.flow.base.metric
    (lt_min G₁.lt G₂.lt)
    (G₁.smoothUpTo.jointContMDiffOn.mono
      (prod_mono (Ico_subset_Ico_right (min_le_left _ _)) subset_rfl))
    (G₂.smoothUpTo.jointContMDiffOn.mono
      (prod_mono (Ico_subset_Ico_right (min_le_right _ _)) subset_rfl))
    (fun _ ht => G₁.hasDerivWithinAt_inner_Ici ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
    (fun _ ht => G₂.hasDerivWithinAt_inner_Ici ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
    h

theorem scalar_eq_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a)
    {t : ℝ} (ht : t ∈ Ico a (min s₁ s₂)) :
    G₁.flow.scalar t = G₂.flow.scalar t := by
  rw [SolutionOn.scalar_eq, SolutionOn.scalar_eq]
  unfold SolutionFamily.scalar
  rw [metric_eq_of_initial_eq G₁ G₂ h t ht]

theorem riemannNorm_eq_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a)
    {t : ℝ} (ht : t ∈ Ico a (min s₁ s₂)) :
    G₁.riemannNorm t = G₂.riemannNorm t := by
  funext x
  unfold riemannNorm SolutionFamily.rm04
  rw [metric_eq_of_initial_eq G₁ G₂ h t ht]

theorem rmNormSq_eq_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a)
    {t : ℝ} (ht : t ∈ Ico a (min s₁ s₂)) :
    FlowMetricBall.rmNormSq G₁.flow t = FlowMetricBall.rmNormSq G₂.flow t := by
  funext x
  unfold FlowMetricBall.rmNormSq SolutionFamily.rm04
  rw [metric_eq_of_initial_eq G₁ G₂ h t ht]

theorem isRmControlled_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a)
    {τ₁ : (RealTimeInterval.closedOpen a s₁ G₁.lt).FlowTime}
    {τ₂ : (RealTimeInterval.closedOpen a s₂ G₂.lt).FlowTime} (hτ : (τ₁ : ℝ) = τ₂)
    (B₁ : FlowMetricBall G₁.flow τ₁) (B₂ : FlowMetricBall G₂.flow τ₂)
    (hc : B₂.center = B₁.center) (hr : B₂.radius = B₁.radius) (hB : B₁.IsRmControlled) :
    B₂.IsRmControlled := by
  obtain ⟨hsub, hbound⟩ := hB
  have hτ₂ : (τ₂ : ℝ) < s₂ := (show (τ₂ : ℝ) ∈ Ico a s₂ from τ₂.2).2
  have hmem : ∀ t ∈ Icc ((τ₂ : ℝ) - B₂.radius ^ 2) τ₂, t ∈ Ico a (min s₁ s₂) := by
    intro t ht
    rw [hr, ← hτ] at ht
    have h1 : t ∈ Ico a s₁ := hsub ht
    exact ⟨h1.1, lt_min h1.2 (ht.2.trans_lt (hτ ▸ hτ₂))⟩
  refine ⟨fun t ht => ?_, fun t ht x hx => ?_⟩
  · have ht' := hmem t ht
    exact ⟨ht'.1, ht'.2.trans_le (min_le_right _ _)⟩
  · have hm := metric_eq_of_initial_eq G₁ G₂ h t (hmem t ht)
    have ht' : t ∈ Icc ((τ₁ : ℝ) - B₁.radius ^ 2) τ₁ := by rwa [hr, ← hτ] at ht
    have hx' : x ∈ B₁.setAt t := by
      simpa only [FlowMetricBall.setAt, mem_ofPred_eq, hc, hr, hm] using hx
    have hk := hbound t ht' x hx'
    simpa only [hr, FlowMetricBall.rmNormSq, SolutionFamily.rm04, hm] using hk

theorem isKappaNoncollapsed_of_initial_eq {s₁ s₂ : ℝ} (G₁ : P.IncomingSlab a s₁)
    (G₂ : P.IncomingSlab a s₂) (h : G₁.flow.base.metric a = G₂.flow.base.metric a)
    {τ₁ : (RealTimeInterval.closedOpen a s₁ G₁.lt).FlowTime}
    {τ₂ : (RealTimeInterval.closedOpen a s₂ G₂.lt).FlowTime} (hτ : (τ₁ : ℝ) = τ₂)
    (B₁ : FlowMetricBall G₁.flow τ₁) (B₂ : FlowMetricBall G₂.flow τ₂)
    (hc : B₂.center = B₁.center) (hr : B₂.radius = B₁.radius) {κ : ℝ}
    (hB : B₁.IsKappaNoncollapsed κ) : B₂.IsKappaNoncollapsed κ := by
  have hτ₁ : (τ₁ : ℝ) ∈ Ico a s₁ := τ₁.2
  have hτ₂ : (τ₂ : ℝ) ∈ Ico a s₂ := τ₂.2
  have hm := metric_eq_of_initial_eq G₁ G₂ h τ₁ ⟨hτ₁.1, lt_min hτ₁.2 (hτ ▸ hτ₂.2)⟩
  have hvol : B₂.volume = B₁.volume := by
    simp only [FlowMetricBall.volume, FlowMetricBall.set,
      FlowMetricBall.setAt, Integral.Measure.volumeMeasureOn_eq_metric,
      SolutionOn.family_metric, hc, hr, ← hτ, hm]
  simp only [FlowMetricBall.IsKappaNoncollapsed, hr, hvol]
  exact hB

end IncomingSlab

theorem exists_uniform_kappaNoncollapsed_initial (P : OrientedThreeStage.{u}) (g : P.Metric)
    {ρ : ℝ} (hnc : ∀ (s : ℝ) (G : P.IncomingSlab 0 s), G.flow.base.metric 0 = g →
      Perelman.NoLocalCollapsing G.flow ρ) :
    ∃ κ > 0, ∃ η > 0, ∀ (s : ℝ) (G : P.IncomingSlab 0 s), G.flow.base.metric 0 = g →
      ∀ (τ : (RealTimeInterval.closedOpen 0 s G.lt).FlowTime)
        (B : FlowMetricBall G.flow τ), (τ : ℝ) ≤ η → B.radius ≤ ρ →
          B.IsRmControlled → B.IsKappaNoncollapsed κ := by
  obtain ⟨s₀, hs₀, G₀, hG₀⟩ := P.exists_incomingSlab_metric_eq g 0
  obtain ⟨κ, hκ, -, hK⟩ := hnc s₀ G₀ hG₀
  refine ⟨κ, hκ, s₀ / 2, half_pos hs₀, ?_⟩
  intro s G hG τ B hτη hBρ hB
  have hinit : G.flow.base.metric 0 = G₀.flow.base.metric 0 := hG.trans hG₀.symm
  have hτ : (τ : ℝ) ∈ Ico 0 s := τ.2
  have hτ₀ : (τ : ℝ) ∈ (RealTimeInterval.closedOpen 0 s₀ G₀.lt).carrier :=
    ⟨hτ.1, by linarith⟩
  let τ₀ : (RealTimeInterval.closedOpen 0 s₀ G₀.lt).FlowTime := ⟨τ, hτ₀⟩
  let B₀ : FlowMetricBall G₀.flow τ₀ := ⟨B.center, B.radius, B.radius_pos⟩
  have hB₀ := hK τ₀ B₀ hBρ
    (IncomingSlab.isRmControlled_of_initial_eq G G₀ hinit rfl B B₀ rfl rfl hB)
  exact IncomingSlab.isKappaNoncollapsed_of_initial_eq G₀ G hinit.symm rfl B₀ B rfl rfl hB₀

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
