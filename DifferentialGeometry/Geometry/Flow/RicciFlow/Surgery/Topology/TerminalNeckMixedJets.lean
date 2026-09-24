import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTensorPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Parameter
import DifferentialGeometry.Analysis.Calculus.AffineTimeReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckTimeWindow
import Mathlib.Geometry.Manifold.Metrizable

noncomputable section
open Bundle Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance terminalSigmaCompact : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)
private local instance terminalC1 : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

section TimeJetContinuity

private theorem time_derivative_field_chart_component
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcs : c < s)
    (B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2)
    (hB : ∀ q t, t ∈ Icc c s → ∀ x,
      B q t x = iteratedDerivWithin q (fun u => metricTensorField (L.extendedMetric u) x)
        (Icc c s) t)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c s) (p : G.terminalRegularOpen)
    (slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace))
    (y : ThreeSpace) :
    B q t ((extChartAt ThreeModel p).symm y)
        (fun j => chartBasisVecFiber (I := ThreeModel) p (slots j)
          ((extChartAt ThreeModel p).symm y)) =
      iteratedDerivWithin q (fun u => chartGramOnE (L.extendedMetric u) p
        (slots 0) (slots 1) y) (Icc c s) t := by
  let x := (extChartAt ThreeModel p).symm y
  let v := fun j => chartBasisVecFiber (I := ThreeModel) p (slots j) x
  have hh := (tensor0SEvalCLM (I := ThreeModel) v).iteratedFDerivWithin_comp_left
    (L.metricTensor_contDiffOn_time hac hcs x t ht)
    (uniqueDiffOn_Icc hcs) ht (show (q : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin q => ℝ) ℝ =>
    A (fun _ => 1)) hh
  rw [hB q t ht]
  exact he.symm

theorem TerminalLimitMetric.exists_time_derivative_fields_norm_continuous
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c) (hcs : c < s) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc c s → ∀ x,
        B q t x = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) x) (Icc c s) t ∧
        HasDerivWithinAt (fun u => B q u x) (B (q + 1) t x) (Icc c s) t) ∧
      ∀ q r : ℕ, ContinuousOn (fun z : (ℝ × ℝ) × G.terminalRegularOpen =>
        tensor02CovDerivNormWith r (B q z.1.1 - B q z.1.2) L.metric L.metric z.2)
        ((Icc c s ×ˢ Icc c s) ×ˢ univ) := by
  obtain ⟨B, hzero, hB⟩ := L.exists_time_derivative_fields hac hcs
  refine ⟨B, hzero, hB, ?_⟩
  intro q r
  refine tensor02CovDerivNormWith_joint_continuousOn (I := ThreeModel) L.metric
    (fun z : ℝ × ℝ => B q z.1 - B q z.2)
    (S := Icc c s ×ˢ Icc c s) (U := univ) ?_ r
  intro x _
  refine ⟨(extChartAt ThreeModel x).target, isOpen_extChartAt_target x,
    (extChartAt ThreeModel x).map_source (mem_extChartAt_source x), Subset.rfl, ?_⟩
  intro slots
  let f := fun z : ℝ × ThreeSpace => iteratedDerivWithin q
    (fun t => chartGramOnE (I := ThreeModel) (L.extendedMetric t) x (slots 0) (slots 1) z.2)
    (Icc c s) z.1
  have hf := L.chartGram_timeJets_contDiffOn_closed hac hcs x (slots 0) (slots 1) q
  have hfst : ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × ThreeSpace => f (z.1.1, z.2))
      ((Icc c s ×ˢ Icc c s) ×ˢ (extChartAt ThreeModel x).target) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hz.1.1, hz.2⟩)
  have hsnd : ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × ThreeSpace => f (z.1.2, z.2))
      ((Icc c s ×ˢ Icc c s) ×ˢ (extChartAt ThreeModel x).target) :=
    hf.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hz.1.2, hz.2⟩)
  apply (hfst.sub hsnd).congr
  intro z hz
  change B q z.1.1 ((extChartAt ThreeModel x).symm z.2)
      (fun j => chartBasisVecFiber (I := ThreeModel) x (slots j)
        ((extChartAt ThreeModel x).symm z.2)) -
    B q z.1.2 ((extChartAt ThreeModel x).symm z.2)
      (fun j => chartBasisVecFiber (I := ThreeModel) x (slots j)
        ((extChartAt ThreeModel x).symm z.2)) = _
  rw [time_derivative_field_chart_component L hac hcs B (fun q t ht x => (hB q t ht x).1)
      q hz.1.1 x slots z.2,
    time_derivative_field_chart_component L hac hcs B (fun q t ht x => (hB q t ht x).1)
      q hz.1.2 x slots z.2]

private theorem tensor02CovDerivNormWith_zero
    (g : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen) (r : ℕ)
    (x : G.terminalRegularOpen) : tensor02CovDerivNormWith r 0 g g x = 0 := by
  rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_zero_tensor]
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
    MetricFiberData.inner, map_zero, Real.sqrt_zero]

theorem TerminalLimitMetric.exists_time_derivative_fields_clipped_convergence
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c)
    {τ Q : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (hQpos : ∀ n, 0 < Q n) {Qlim : ℝ} (hQlim : 0 < Qlim)
    (hQ : Tendsto Q atTop (𝓝 Qlim)) (hmargin : c < s - Qlim⁻¹) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc c s → ∀ x,
        B q t x = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) x) (Icc c s) t ∧
        HasDerivWithinAt (fun u => B q u x) (B (q + 1) t x) (Icc c s) t) ∧
      ∀ q r : ℕ, ∀ K : Set G.terminalRegularOpen, IsCompact K →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v ∈ Icc (-1 : ℝ) 0, ∀ x ∈ K,
          tensor02CovDerivNormWith r
            (B q (Real.clippedAffineTime s (τ n) (Q n) Qlim v) -
              B q (s + v / Qlim)) L.metric L.metric x < ε := by
  have hcs : c < s := hmargin.trans (sub_lt_self s (inv_pos.mpr hQlim))
  obtain ⟨B, hzero, hB, hcont⟩ := L.exists_time_derivative_fields_norm_continuous hac hcs
  refine ⟨B, hzero, hB, ?_⟩
  let _ : TopologicalSpace.MetrizableSpace G.terminalRegularOpen :=
    Manifold.metrizableSpace ThreeModel G.terminalRegularOpen
  let _ : MetricSpace G.terminalRegularOpen :=
    TopologicalSpace.metrizableSpaceMetric G.terminalRegularOpen
  have hτ' := hτ.mono_right nhdsWithin_le_nhds
  have hleft := hτ'.sub (hQ.inv₀ hQlim.ne')
  have hsource : ∀ᶠ n in atTop,
      Icc (τ n - (Q n)⁻¹) (τ n) ⊆ Icc c s := by
    filter_upwards [hleft.eventually (Ioi_mem_nhds hmargin),
      hτ.eventually self_mem_nhdsWithin] with n hn hns
    exact fun t ht => ⟨hn.le.trans ht.1, ht.2.trans hns.le⟩
  have htarget : MapsTo (fun v => s + v / Qlim) (Icc (-1 : ℝ) 0) (Icc c s) := by
    intro v hv
    have hlo := div_le_div_of_nonneg_right hv.1 hQlim.le
    simp only [neg_div, one_div] at hlo
    have hhi := div_nonpos_of_nonpos_of_nonneg hv.2 hQlim.le
    constructor <;> linarith
  have htime := Real.tendstoUniformlyOn_clippedAffineTime hQ hτ' hQlim hQpos
  intro q r K hK ε hε
  let F := fun z : (ℝ × ℝ) × G.terminalRegularOpen =>
    tensor02CovDerivNormWith r (B q z.1.1 - B q z.1.2) L.metric L.metric z.2
  have hF : ContinuousOn F ((Icc c s ×ˢ Icc c s) ×ˢ K) :=
    (hcont q r).mono (prod_mono_right (subset_univ K))
  have hUC := ((isCompact_Icc.prod isCompact_Icc).prod hK).uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  have hnear := Metric.tendstoUniformlyOn_iff.mp htime δ hδ
  filter_upwards [hsource, hnear] with n hn ht
  intro v hv x hx
  have h1 : Real.clippedAffineTime s (τ n) (Q n) Qlim v ∈ Icc c s :=
    hn (Real.clippedAffineTime_mem_source (hQpos n))
  have h2 := htarget hv
  have hdist : dist ((Real.clippedAffineTime s (τ n) (Q n) Qlim v, s + v / Qlim), x)
      ((s + v / Qlim, s + v / Qlim), x) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm] using ht v hv
  have hh := hc _ ⟨⟨h1, h2⟩, hx⟩ _ ⟨⟨h2, h2⟩, hx⟩ hdist
  have hz : F ((s + v / Qlim, s + v / Qlim), x) = 0 := by
    dsimp [F]
    rw [sub_self, tensor02CovDerivNormWith_zero]
  rw [hz, Real.dist_eq, sub_zero] at hh
  exact lt_of_le_of_lt (le_abs_self _) hh


theorem TerminalLimitMetric.exists_time_derivative_fields_clipped_convergence_of_strongNecks
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps : ℝ} (neck : ∀ n, Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck
      G.flow eps x.1 (τ n)) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc a s → ∀ y,
        B q t y = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) y) (Icc a s) t ∧
        HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t) ∧
      ∀ q r : ℕ, ∀ K : Set G.terminalRegularOpen, IsCompact K →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v ∈ Icc (-1 : ℝ) 0, ∀ y ∈ K,
          tensor02CovDerivNormWith r
            (B q (Real.clippedAffineTime s (τ n) (G.flow.scalar (τ n) x.1)
              (metricScalarAt L.metric x) v) -
              B q (s + v / metricScalarAt L.metric x)) L.metric L.metric y < ε := by
  let Q := fun n => G.flow.scalar (τ n) x.1
  let Qlim := metricScalarAt L.metric x
  have hQpos : ∀ n, 0 < Q n := fun n => (neck n).Q_pos
  have hQ : Tendsto Q atTop (𝓝 Qlim) := (L.tendsto_metricScalarAt x).comp hτ
  obtain ⟨B, hzero, hB, hcont⟩ := L.exists_time_derivative_fields_norm_continuous le_rfl G.lt
  refine ⟨B, hzero, hB, ?_⟩
  let _ : TopologicalSpace.MetrizableSpace G.terminalRegularOpen :=
    Manifold.metrizableSpace ThreeModel G.terminalRegularOpen
  let _ : MetricSpace G.terminalRegularOpen :=
    TopologicalSpace.metrizableSpaceMetric G.terminalRegularOpen
  have hτ' := hτ.mono_right nhdsWithin_le_nhds
  have hsource : ∀ᶠ n in atTop,
      Icc (τ n - (Q n)⁻¹) (τ n) ⊆ Icc a s :=
    Eventually.of_forall fun n t ht =>
      ⟨((neck n).time_domain ht).1, ((neck n).time_domain ht).2.le⟩
  have hleft := L.inv_scalar_le_time_length_of_strongNecks hτ x hx neck
  have htarget : MapsTo (fun v => s + v / Qlim) (Icc (-1 : ℝ) 0) (Icc a s) := by
    intro v hv
    have hlo := div_le_div_of_nonneg_right hv.1 hx.le
    simp only [neg_div, one_div] at hlo
    have hhi := div_nonpos_of_nonpos_of_nonneg hv.2 hx.le
    constructor <;> linarith
  have htime := Real.tendstoUniformlyOn_clippedAffineTime hQ hτ' hx hQpos
  intro q r K hK ε hε
  let F := fun z : (ℝ × ℝ) × G.terminalRegularOpen =>
    tensor02CovDerivNormWith r (B q z.1.1 - B q z.1.2) L.metric L.metric z.2
  have hF : ContinuousOn F ((Icc a s ×ˢ Icc a s) ×ˢ K) :=
    (hcont q r).mono (prod_mono_right (subset_univ K))
  have hUC := ((isCompact_Icc.prod isCompact_Icc).prod hK).uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  have hnear := Metric.tendstoUniformlyOn_iff.mp htime δ hδ
  filter_upwards [hsource, hnear] with n hn ht
  intro v hv x hx
  have h1 : Real.clippedAffineTime s (τ n) (Q n) Qlim v ∈ Icc a s :=
    hn (Real.clippedAffineTime_mem_source (hQpos n))
  have h2 := htarget hv
  have hdist : dist ((Real.clippedAffineTime s (τ n) (Q n) Qlim v, s + v / Qlim), x)
      ((s + v / Qlim, s + v / Qlim), x) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm] using ht v hv
  have hh := hc _ ⟨⟨h1, h2⟩, hx⟩ _ ⟨⟨h2, h2⟩, hx⟩ hdist
  have hz : F ((s + v / Qlim, s + v / Qlim), x) = 0 := by
    dsimp [F]
    rw [sub_self, tensor02CovDerivNormWith_zero]
  rw [hz, Real.dist_eq, sub_zero] at hh
  exact lt_of_le_of_lt (le_abs_self _) hh

end TimeJetContinuity

section NeckPullback

theorem TerminalLimitMetric.exists_time_fields_clipped_neck_pullback_convergence
    (L : G.TerminalLimitMetric) {c : ℝ} (hac : a ≤ c)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    (hQ : ∀ n, 0 < G.flow.scalar (τ n) x.1)
    (hmargin : c < s - (metricScalarAt L.metric x)⁻¹)
    {δ : ℝ} (hδ : δ < 1 / 4) (k : ℕ)
    (N : ℕ → NormalizedNeck L.metric δ k) (hcenter : ∀ n, (N n).center = x)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ, (N n).chart z ∈ K) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc c s → ∀ y,
        B q t y = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) y) (Icc c s) t ∧
        HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc c s) t) ∧
      ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ v ∈ Icc (-1 : ℝ) 0, ∀ r ≤ k, ∀ z ∈ neckClosedTest δ,
          tensor02CovDerivNormWith r
            (pullbackTensor02FieldCross (N n).cylindricalChart.chart
              (restrictOpen0S 2 (V := (N n).cylindricalChart.target)
                (B q (Real.clippedAffineTime s (τ n) (G.flow.scalar (τ n) x.1)
                    (metricScalarAt L.metric x) v) -
                  B q (s + v / metricScalarAt L.metric x))))
            (roundCylinderMetric.restrictOpen (neckBuffer δ))
            (roundCylinderMetric.restrictOpen (neckBuffer δ)) z < ε := by
  let Q := fun n => G.flow.scalar (τ n) x.1
  let Qlim := metricScalarAt L.metric x
  have hscale : Tendsto Q atTop (𝓝 Qlim) := (L.tendsto_metricScalarAt x).comp hτ
  obtain ⟨B, hzero, hB, hconv⟩ :=
    L.exists_time_derivative_fields_clipped_convergence hac hτ hQ hx hscale hmargin
  refine ⟨B, hzero, hB, ?_⟩
  obtain ⟨D, hD, hbound⟩ := exists_normalizedNeck_tensor_pullback_bound
    (M := G.terminalRegularOpen) (qmax := Qlim) hδ k hx
  have hsc (n : ℕ) : (N n).scale = Qlim := by rw [(N n).scale_scalar, hcenter n]
  intro q ε hε
  let η := ε / (2 * (D + 1) * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have herr (j : Fin (k + 1)) := hconv q j K hK η hη
  have hall := eventually_all.mpr herr
  filter_upwards [hall, hcapture] with n hn hc
  intro v hv r hr z hz
  let A := B q (Real.clippedAffineTime s (τ n) (Q n) Qlim v) - B q (s + v / Qlim)
  have hsum : (∑ j ∈ Finset.range (k + 1),
      tensor02CovDerivNormWith j A L.metric L.metric ((N n).chart z)) ≤
      ((k : ℝ) + 1) * η := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k + 1), η := Finset.sum_le_sum fun j hj =>
        (hn ⟨j, Finset.mem_range.mp hj⟩ v hv ((N n).chart z) (hc z hz)).le
      _ = _ := by simp
  have hpull := hbound L.metric (N n) (hsc n).symm.le (hsc n).le A r hr z hz
  have hsmall : D * (((k : ℝ) + 1) * η) < ε := by
    have hden : 0 < 2 * (D + 1) * ((k : ℝ) + 1) := by positivity
    have hhalf : D * (((k : ℝ) + 1) * η) ≤ ε / 2 := by
      dsimp [η]
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hε.le]
    linarith
  exact hpull.trans_lt ((mul_le_mul_of_nonneg_left hsum hD).trans_lt hsmall)


theorem TerminalLimitMetric.exists_time_fields_clipped_neck_pullback_convergence_of_strongNecks
    (L : G.TerminalLimitMetric)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {eps : ℝ} (neck : ∀ n, Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck
      G.flow eps x.1 (τ n))
    {δ : ℝ} (hδ : δ < 1 / 4) (k : ℕ)
    (N : ℕ → NormalizedNeck L.metric δ k) (hcenter : ∀ n, (N n).center = x)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (hcapture : ∀ᶠ n in atTop, ∀ z ∈ neckClosedTest δ, (N n).chart z ∈ K) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := ThreeModel) (M := G.terminalRegularOpen) ∞ 2,
      (∀ t, B 0 t = metricTensorField (L.extendedMetric t)) ∧
      (∀ q t, t ∈ Icc a s → ∀ y,
        B q t y = iteratedDerivWithin q
          (fun u => metricTensorField (L.extendedMetric u) y) (Icc a s) t ∧
        HasDerivWithinAt (fun u => B q u y) (B (q + 1) t y) (Icc a s) t) ∧
      ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ v ∈ Icc (-1 : ℝ) 0, ∀ r ≤ k, ∀ z ∈ neckClosedTest δ,
          tensor02CovDerivNormWith r
            (pullbackTensor02FieldCross (N n).cylindricalChart.chart
              (restrictOpen0S 2 (V := (N n).cylindricalChart.target)
                (B q (Real.clippedAffineTime s (τ n) (G.flow.scalar (τ n) x.1)
                    (metricScalarAt L.metric x) v) -
                  B q (s + v / metricScalarAt L.metric x))))
            (roundCylinderMetric.restrictOpen (neckBuffer δ))
            (roundCylinderMetric.restrictOpen (neckBuffer δ)) z < ε := by
  let Q := fun n => G.flow.scalar (τ n) x.1
  let Qlim := metricScalarAt L.metric x
  obtain ⟨B, hzero, hB, hconv⟩ :=
    L.exists_time_derivative_fields_clipped_convergence_of_strongNecks hτ x hx neck
  refine ⟨B, hzero, hB, ?_⟩
  obtain ⟨D, hD, hbound⟩ := exists_normalizedNeck_tensor_pullback_bound
    (M := G.terminalRegularOpen) (qmax := Qlim) hδ k hx
  have hsc (n : ℕ) : (N n).scale = Qlim := by rw [(N n).scale_scalar, hcenter n]
  intro q ε hε
  let η := ε / (2 * (D + 1) * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have herr (j : Fin (k + 1)) := hconv q j K hK η hη
  have hall := eventually_all.mpr herr
  filter_upwards [hall, hcapture] with n hn hc
  intro v hv r hr z hz
  let A := B q (Real.clippedAffineTime s (τ n) (Q n) Qlim v) - B q (s + v / Qlim)
  have hsum : (∑ j ∈ Finset.range (k + 1),
      tensor02CovDerivNormWith j A L.metric L.metric ((N n).chart z)) ≤
      ((k : ℝ) + 1) * η := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k + 1), η := Finset.sum_le_sum fun j hj =>
        (hn ⟨j, Finset.mem_range.mp hj⟩ v hv ((N n).chart z) (hc z hz)).le
      _ = _ := by simp
  have hpull := hbound L.metric (N n) (hsc n).symm.le (hsc n).le A r hr z hz
  have hsmall : D * (((k : ℝ) + 1) * η) < ε := by
    have hden : 0 < 2 * (D + 1) * ((k : ℝ) + 1) := by positivity
    have hhalf : D * (((k : ℝ) + 1) * η) ≤ ε / 2 := by
      dsimp [η]
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hε.le]
    linarith
  exact hpull.trans_lt ((mul_le_mul_of_nonneg_left hsum hD).trans_lt hsmall)

end NeckPullback

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
