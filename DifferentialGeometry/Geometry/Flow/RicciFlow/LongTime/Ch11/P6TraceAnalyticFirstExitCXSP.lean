import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodFirstExitCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceBallRicciCXSP

set_option autoImplicit false

/-!
# CX-SPINE G20：局部 analytic 数据实际消费整史 first-exit

保留同一 pair 的后缀 Good，以两倍端点球梯度和局部 HI 生产 Ricci 输入。
所有数值预算明确量化；不预设整窗不出界，不借全空间曲率界或新的顶层 supply。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

/-- 局部 Good、梯度、HI 与同一 records 数据生产整史 first-exit，不再索取 hRic。 -/
theorem exists_pair_firstExit_of_local_analytic_CXSP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p q : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
        (_hOld : ∀ e : Fin H.eventCount,
          (H.event e).old = (H.event e).transition.trace.retainedCore)
        (_hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
        (_hacc : params.modelAccuracy ≤ ε₀) (_hm : 2 ≤ params.modelOrder)
        (_hD : StandardCap.transitionEnd + 10 < params.modelRadius)
        {ε C1 C2 qcan M Q a₀ K : ℝ} {Ctime Cgrad : ℝ≥0} (_hM : 0 < M) (_hqM : qcan ≤ M)
        (_hscalarA : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
        (_hscalarB : metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ M)
        (_htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2)
        (_hscale : ∀ (e : Fin H.eventCount), H.activeStage a ≤ e.castSucc →
          e.succ ≤ H.activeStage t → ∀ b, 4 * M < ((records e).static b).neck.scale)
        {ℓ : ℝ} (_hℓ : 0 < ℓ) {X : ℝ≥0∞}
        (_ha₀ : 0 ≤ a₀) (_hQ : 0 < Q) (_hlate : 1 ≤ Q * (a : ℝ))
        (_hspace : (Cgrad : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4)
        (_hKℓ : K * ℓ ^ 2 ≤ 1)
        (_hK : 2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K)
        (_hmargin : A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < X)
        (_hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → ∀ z : (H.stageAt w).Carrier,
            (z = A.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt) ∨
              z = B.point (H.activeStage w) (H.activeStage_mono haw)
                (H.activeStage_mono hwt)) →
            qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w z)
        (_hgrad : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → H.time (H.activeStage w) < (w : ℝ) →
            ∀ z : (H.stageAt w).Carrier,
            (z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (A.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) (2 * ℓ) ∨
              z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (B.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) (2 * ℓ)) →
            qcan < metricScalarAt (H.stageMetric (H.activeStage w) w) z →
            ∀ ξ : TangentSpace ThreeModel z,
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
                (metricScalarAt (H.stageMetric (H.activeStage w) w)) z ξ)| ≤
                Cgrad * metricScalarAt (H.stageMetric (H.activeStage w) w) z *
                  Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage w) w) z) *
                  Real.sqrt ((H.stageMetric (H.activeStage w) w).inner z ξ ξ))
        (_hpin : ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
          (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → A.pairEDist_CXSP (hat := hat) B w haw hwt < X) →
          ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
            v < w → w < t → H.time (H.activeStage w) < (w : ℝ) →
            ∀ z : (H.stageAt w).Carrier,
            (z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (A.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) ℓ ∨
              z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
                (B.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt)) ℓ) →
            InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage w) w) (a₀ + w) z),
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          A.pairEDist_CXSP (hat := hat) B v hav hvt < X ∧
            A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
              A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hfirst⟩ := exists_pair_firstExit_of_good_ricci_CXSP.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H a t hat p q A B params records hOld hcan hacc hm hD ε C1 C2 qcan M Q a₀ K Ctime
    Cgrad hM hqM hscalarA hscalarB htime hscale ℓ hℓ X ha₀ hQ hlate hspace hKℓ hK
    hmargin hgood hgrad hpin
  refine hfirst hat A B records hOld hcan hacc hm hD hM hqM hscalarA hscalarB htime hscale
    hℓ hmargin hgood ?_
  intro v hav hvt hstay j hf hl s hvs hjs hst hnext z ξ hz
  let w : Icc (0 : ℝ) H.horizon := ⟨s, v.2.1.trans hvs.le, hst.le.trans t.2.2⟩
  have haw : a ≤ w := (show (a : ℝ) ≤ v from hav).trans hvs.le
  have hwt : w ≤ t := hst.le
  have hact : H.activeStage w = j :=
    H.activeStage_eq_of_regular_stage_CXSP w j hjs.le hnext
  subst j
  have htimeV : Ctime * M * ((t : ℝ) - v) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ v from hav) (t : ℝ))
      (mul_nonneg Ctime.coe_nonneg hM.le)).trans htime
  have hlateW : 1 ≤ Q * (w : ℝ) :=
    hlate.trans (mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ w from haw) hQ.le)
  rcases hz with hz | hz
  · exact A.ricci_on_ball_of_good_suffix_CXSP hat hM hqM
      (fun u hau hut hvu hutlt hR =>
        hgood v hav hvt hstay u hau hut hvu hutlt _ (Or.inl rfl) hR)
      hscalarA htimeV w haw hvs hwt hjs
      (fun y hy hR η => hgrad v hav hvt hstay w haw hwt hvs hst hjs y (Or.inl hy) hR η)
      ha₀ hQ hlateW hℓ hspace hKℓ hK z
      (hpin v hav hvt hstay w haw hwt hvs hst hjs z (Or.inl hz)) hz ξ
  · exact B.ricci_on_ball_of_good_suffix_CXSP hat hM hqM
      (fun u hau hut hvu hutlt hR =>
        hgood v hav hvt hstay u hau hut hvu hutlt _ (Or.inr rfl) hR)
      hscalarB htimeV w haw hvs hwt hjs
      (fun y hy hR η => hgrad v hav hvt hstay w haw hwt hvs hst hjs y (Or.inr hy) hR η)
      ha₀ hQ hlateW hℓ hspace hKℓ hK z
      (hpin v hav hvt hstay w haw hwt hvs hst hjs z (Or.inr hz)) hz ξ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
