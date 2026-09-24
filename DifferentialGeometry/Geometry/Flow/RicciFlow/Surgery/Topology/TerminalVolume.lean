import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtype

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance : BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem TerminalLimitMetric.tendsto_riemannianVolumeMeasure_compact
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K) :
    Tendsto (fun t => riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen)
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) K)
      (𝓝[<] s) (𝓝 (riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric K)) := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  let : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts L.metric
  have hmetric : TendstoUniformlyOn
      (fun t x => metricDerivNorm 0
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x)
      (fun _ => 0) (𝓝[<] s) K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨d, hd, hbound⟩ := L.converges K hK 0 ε hε
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    intro x hx
    have hn : 0 ≤ metricDerivNorm 0
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x :=
      Real.sqrt_nonneg _
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using hbound t ht x hx
  have hconv := tendsto_setLIntegral_of_dominated_convergence_of_metricDerivNorm
    (fun t => (G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric
    hK.measurableSet hmetric (fs := fun _ _ => (1 : ℝ≥0∞)) (f := fun _ => 1)
    (fun _ => 1)
    (Eventually.of_forall fun _ => aemeasurable_const)
    (Eventually.of_forall fun _ => Eventually.of_forall fun _ => le_rfl)
    (by simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using
      hK.measure_lt_top.ne)
    (Eventually.of_forall fun _ => tendsto_const_nhds)
  simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using hconv

theorem TerminalLimitMetric.volume_compact_le_of_eventually_volume_le
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    {V : ℝ≥0∞}
    (hV : ∀ᶠ t in 𝓝[<] s,
      riemannianVolumeMeasure (I := ThreeModel) (M := P.Carrier) (G.flow.base.metric t) univ ≤ V) :
    riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric K ≤ V := by
  apply le_of_tendsto (L.tendsto_riemannianVolumeMeasure_compact hK)
  filter_upwards [hV] with t ht
  have hmap := congrArg (fun μ : Measure P.Carrier => μ univ)
    (map_riemannianVolumeMeasure_restrictOpen (G.flow.base.metric t) G.terminalRegularOpen)
  rw [Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] at hmap
  exact ((measure_mono (subset_univ K)).trans hmap.le).trans
    ((measure_mono (subset_univ _)).trans ht)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance : BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball
    (L : G.TerminalLimitMetric) (p : G.terminalRegularOpen) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p R)) :
    ∀ᶠ t in 𝓝[<] s,
      riemannianBallOf (G.flow.base.metric t) p.val ρ ⊆
        Subtype.val '' riemannianClosedBallOf L.metric p R := by
  let B : ℝ := R / ρ
  have hB : 1 < B := (lt_div_iff₀ hρ).mpr (by simpa only [one_mul] using hρR)
  have heps : 0 < B ^ 2 - 1 := by nlinarith
  obtain ⟨d, hd, hbound⟩ := L.exists_compact_quad_bound hcompact heps
  let F := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel
    G.terminalRegularOpen ⟨p⟩
  have hsource : riemannianClosedBallOf L.metric p R ⊆ F.source := subset_univ _
  filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
  have hlow : ∀ y ∈ riemannianClosedBallOf L.metric p R,
      ∀ v : TangentSpace ThreeModel y, L.metric.inner y v v ≤
        B ^ 2 * (G.flow.base.metric t).inner (F y)
          (mfderiv ThreeModel ThreeModel F y v) (mfderiv ThreeModel ThreeModel F y v) := by
    intro y hy v
    have hb := hbound t ht y hy v
    change L.metric.inner y v v ≤ (1 + (B ^ 2 - 1)) *
      (G.flow.base.metric t).inner y.val v v at hb
    have hdf : mfderiv ThreeModel ThreeModel F y v = v :=
      DifferentialGeometry.mfderiv_subtype_val_apply G.terminalRegularOpen y v
    rw [hdf]
    change L.metric.inner y v v ≤ B ^ 2 * (G.flow.base.metric t).inner y.val v v
    convert hb using 1
    ring
  have hcapture := DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    L.metric (G.flow.base.metric t) F p (hρ.trans hρR) (zero_lt_one.trans hB) hcompact hsource hlow
  have hradius : R / B = ρ := by
    dsimp only [B]
    field_simp [ne_of_gt (hρ.trans hρR)]
  rw [hradius] at hcapture
  exact hcapture

private theorem TerminalLimitMetric.le_volume_compact_of_eventually_ball_volume_ge
    (L : G.TerminalLimitMetric) (p : G.terminalRegularOpen) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p R))
    {V : ℝ≥0∞}
    (hV : ∀ᶠ t in 𝓝[<] s, V ≤
      riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t)
        (riemannianBallOf (G.flow.base.metric t) p.val ρ)) :
    V ≤ riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (riemannianClosedBallOf L.metric p R) := by
  apply ge_of_tendsto (L.tendsto_riemannianVolumeMeasure_compact hcompact)
  filter_upwards [hV, L.eventually_ball_subset_compact_terminal_ball p hρ hρR hcompact] with t hvt hcapture
  refine hvt.trans ((measure_mono hcapture).trans_eq ?_)
  let K := riemannianClosedBallOf L.metric p R
  have hKimage : MeasurableSet ((Subtype.val : G.terminalRegularOpen → P.Carrier) '' K) :=
    (hcompact.image continuous_subtype_val).measurableSet
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (G.flow.base.metric t) G.terminalRegularOpen hKimage (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  have hpre : (Subtype.val : G.terminalRegularOpen → P.Carrier) ⁻¹'
      (Subtype.val '' K) = K := Subtype.val_injective.preimage_image K
  rw [hpre] at heq
  exact heq.symm

theorem TerminalLimitMetric.volume_ball_ge_of_eventually_volume_ball_ge
    (L : G.TerminalLimitMetric) (p : G.terminalRegularOpen) {r κ : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p r))
    (hvolume : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∀ᶠ t in 𝓝[<] s,
      ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t)
          (riemannianBallOf (G.flow.base.metric t) p.val ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric p r) := by
  have hsmall (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
      ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
        riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric p r) := by
    obtain ⟨R, hρR, hRr⟩ := exists_between hρr
    have hclosed : IsClosed (riemannianClosedBallOf L.metric p R) :=
      isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist L.metric p)
        continuous_const
    have hcpt : IsCompact (riemannianClosedBallOf L.metric p R) :=
      hcompact.of_isClosed_subset hclosed (riemannianClosedBallOf_mono L.metric p hRr.le)
    have hbound := L.le_volume_compact_of_eventually_ball_volume_ge p hρ hρR hcpt
      (hvolume ρ hρ hρr)
    refine hbound.trans (measure_mono ?_)
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)
  have hlimit : Tendsto (fun ρ : ℝ => ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3)
      (𝓝[<] r) (𝓝 (ENNReal.ofReal κ * ENNReal.ofReal r ^ 3)) := by
    have hp := ((ENNReal.continuous_pow 3).comp ENNReal.continuous_ofReal).continuousAt.tendsto.mono_left
      (show 𝓝[<] r ≤ 𝓝 r from nhdsWithin_le_nhds)
    exact ENNReal.Tendsto.const_mul hp (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto hlimit
  filter_upwards [Ioo_mem_nhdsLT hr] with ρ hρ
  exact hsmall ρ hρ.1 hρ.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
