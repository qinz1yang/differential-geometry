import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ParabolicTerminalBallAlternative

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private ObservedHistory.rmNormSq_incomingFootprint_slab
  ObservedHistory.rmNormSq_incomingFootprint_last
  ObservedHistory.rmNormSq_incomingFootprint_slab_before from
    DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall

private theorem stage_norm_transport {H : ObservedHistory.{u}}
    {first last j k : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x)
    (hjk : j = k) (hj : first ≤ j) (hjl : j ≤ last)
    (hk : first ≤ k) (hkl : k ≤ last) (g : (l : Fin (H.eventCount + 1)) → (H.stage l).Metric) :
    normSq0S (g j) (A.point j hj hjl) 4 (metricRm04At (g j) (A.point j hj hjl)) =
      normSq0S (g k) (A.point k hk hkl) 4 (metricRm04At (g k) (A.point k hk hkl)) := by
  subst k
  rfl

private theorem test_of_stage_index
    (A : ObservedHistory.{u}) (t : Icc (0 : ℝ) A.horizon)
    (last : Fin (A.eventCount + 1)) (hlast : A.activeStage t = last)
    (p : (A.stage last).Carrier) {r : ℝ} (hr : 0 < r)
    (a : Icc (0 : ℝ) A.horizon) (hat : a ≤ t) (ha : (a : ℝ) = (t : ℝ) - r ^ 2)
    (first : Fin (A.eventCount + 1)) (hfirst : first ≤ A.activeStage a)
    (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (A.stageMetric last t) p r,
      ∃ B : BackwardPointTrace A first last hf x,
        (∀ (v : Icc (0 : ℝ) A.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          r ^ 4 * normSq0S (A.stageMetric (A.activeStage v) v)
            (B.point (A.activeStage v) (hfirst.trans (A.activeStage_mono hav))
              ((A.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (A.stageMetric (A.activeStage v) v)
              (B.point (A.activeStage v) (hfirst.trans (A.activeStage_mono hav))
                ((A.activeStage_mono hvt).trans hlast.le))) ≤ 1) ∧
        ∀ (j : Fin A.eventCount) (hj : A.activeStage a ≤ j.castSucc) (hjl : j.succ ≤ last),
          let y : (A.event j).incoming.terminalRegularOpen :=
            ⟨B.point j.castSucc (hfirst.trans hj) (j.castSucc_lt_succ.le.trans hjl),
              (B.crossing j (hfirst.trans hj) hjl).mem_terminalRegularRegion (A.event j)⟩;
          r ^ 4 * normSq0S (A.event j).terminal.metric y 4
            (metricRm04At (A.event j).terminal.metric y) ≤ 1) :
    ∃ p' : (A.stageAt t).Carrier, HEq p' p ∧ A.isParabolicallyRmControlledBall t p' r := by
  subst last
  refine ⟨p, HEq.rfl, hr, a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  refine ⟨B.restrictFirst hfirst (A.activeStage_mono hat),?_,?_⟩
  · intro v hav hvt
    exact hobs v hav hvt
  · intro j hj hjl
    exact hseam j hj hjl

theorem RetainedCoreHistory.isParabolicallyRmControlledBall_extendHorizon_of_incomingFootprint
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (first : Fin (H.eventCount + 1))
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount) (Fin.le_last first)
          j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) (Fin.le_last first) G)).restrictOpen
              (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K))
    {t r : ℝ} (ht : H.horizon < t) (hts : t < s) (hr : 0 < r)
    (hroom : H.time first ≤ t - r ^ 2)
    (p : (H.stage (Fin.last H.eventCount)).Carrier)
    (U : Set (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K))
    (hball : riemannianBallOf (G.flow.base.metric t) p r ⊆
      (fun z => (H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K z).val) '' U)
    (hbound : ∀ v ∈ Icc (t - r ^ 2) t, ∀ z ∈ U,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1) :
    let htstart := H.time_le_horizon.trans_lt ht;
    let A := H.extendHorizon t ht.le (G.closedPrefix t htstart hts) hinit;
    let time : Icc (0 : ℝ) A.horizon := ⟨t,H.horizon_nonneg.trans ht.le,le_rfl⟩;
    ∃ p' : (A.toHistory.stageAt time).Carrier, HEq p' p ∧
      A.toHistory.isParabolicallyRmControlledBall time p' r := by
  intro htstart A time
  have hactive : A.toHistory.activeStage time = Fin.last H.eventCount :=
    A.toHistory.activeStage_at_horizon
  let a : Icc (0 : ℝ) A.horizon := ⟨t - r ^ 2,
    (H.toHistory.time_nonneg first).trans hroom, sub_le_self _ (sq_nonneg r)⟩
  have hat : a ≤ time := sub_le_self _ (sq_nonneg r)
  have hfirst : first ≤ A.toHistory.activeStage a := A.toHistory.le_activeStage a first hroom
  have hmetric (v : ℝ) : A.toHistory.stageMetric (Fin.last H.eventCount) v = G.flow.base.metric v := by
    exact A.toHistory.stageMetric_last_of_lt (h := htstart) v
  apply test_of_stage_index A.toHistory time (Fin.last H.eventCount) hactive p hr a hat rfl first hfirst
    (Fin.le_last first)
  intro x hx
  change x ∈ riemannianBallOf (A.toHistory.stageMetric (Fin.last H.eventCount) t) p r at hx
  rw [hmetric] at hx
  obtain ⟨z,hz,rfl⟩ := hball hx
  let B₀ : BackwardPointTrace H.toHistory first (Fin.last H.eventCount) (Fin.le_last first)
      (H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K z).val := Classical.choice z.val.val.property
  let B : BackwardPointTrace A.toHistory first (Fin.last H.eventCount) (Fin.le_last first)
      (H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K z).val :=
    { point := B₀.point, endpoint_eq := B₀.endpoint_eq, crossing := B₀.crossing }
  refine ⟨B, ?_, ?_⟩
  · intro v hav hvt
    have hfv : first ≤ A.toHistory.activeStage v := hfirst.trans (A.toHistory.activeStage_mono hav)
    have hvl : A.toHistory.activeStage v ≤ Fin.last H.eventCount := Fin.le_last _
    have hvs : (v : ℝ) < s := (show (v : ℝ) ≤ t from hvt).trans_lt hts
    have hb := hbound v ⟨hav,hvt⟩ z hz
    by_cases he : A.toHistory.activeStage v = Fin.last H.eventCount
    · have hvlast : H.time (Fin.last H.eventCount) ≤ (v : ℝ) := by
        rw [← he]
        exact A.toHistory.activeStage_time_le v
      rw [hlast v ⟨hvlast,hvs.le⟩,
        ObservedHistory.rmNormSq_incomingFootprint_last H.toHistory first (Fin.last H.eventCount)
          (Fin.le_last first) G L K,
        L.extendedMetric_before hvs,Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen] at hb
      calc
        r ^ 4 * normSq0S (A.toHistory.stageMetric (A.toHistory.activeStage v) v)
            (B.point (A.toHistory.activeStage v) hfv ((A.toHistory.activeStage_mono hvt).trans hactive.le)) 4
            (metricRm04At (A.toHistory.stageMetric (A.toHistory.activeStage v) v)
              (B.point (A.toHistory.activeStage v) hfv ((A.toHistory.activeStage_mono hvt).trans hactive.le))) =
          r ^ 4 * normSq0S (A.toHistory.stageMetric (Fin.last H.eventCount) v)
            (B.point (Fin.last H.eventCount) (Fin.le_last first) le_rfl) 4
            (metricRm04At (A.toHistory.stageMetric (Fin.last H.eventCount) v)
              (B.point (Fin.last H.eventCount) (Fin.le_last first) le_rfl)) := by
                rw [stage_norm_transport B he hfv hvl (Fin.le_last first) le_rfl
                  (fun j => A.toHistory.stageMetric j v)]
        _ = r ^ 4 * normSq0S (G.flow.base.metric v)
            ((H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
              (Fin.le_last first) G K z).val) 4
            (metricRm04At (G.flow.base.metric v)
              ((H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
                (Fin.le_last first) G K z).val)) := by
              rw [B.endpoint_eq, hmetric]
              rfl
        _ ≤ 1 := hb
    · have hlt : (A.toHistory.activeStage v).val < H.eventCount := by
        have hh := (A.toHistory.activeStage v).isLt
        have hn : (A.toHistory.activeStage v).val ≠ H.eventCount := fun h => he (Fin.ext h)
        omega
      let j : Fin H.eventCount := ⟨(A.toHistory.activeStage v).val,hlt⟩
      have hj : j.castSucc = A.toHistory.activeStage v := rfl
      have hfj : first ≤ j.castSucc := hfv
      have hvj : (v : ℝ) ∈ Ico (H.time j.castSucc) (H.time j.succ) :=
        ⟨A.toHistory.activeStage_time_le v,A.toHistory.activeStage_before_next v j.isLt⟩
      rw [ObservedHistory.rmNormSq_incomingFootprint_slab_before H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) G K gflow j hfj (Fin.le_last _) v hvj.2
          (hslabs j hfj v ⟨hvj.1,hvj.2.le⟩) z B₀] at hb
      rw [stage_norm_transport B hj.symm hfv hvl hfj (by simpa only [hj] using hvl) (fun k => A.toHistory.stageMetric k v)]
      have hmetricj : A.toHistory.stageMetric j.castSucc v =
          H.toHistory.stageMetric j.castSucc v := by
        exact (ObservedHistory.stageMetric_castSucc_apply (H := A.toHistory) j v).trans
          (ObservedHistory.stageMetric_castSucc_apply (H := H.toHistory) j v).symm
      rw [hmetricj]
      change r ^ 4 * normSq0S (H.toHistory.stageMetric j.castSucc v)
        (B₀.point j.castSucc hfj (Fin.le_last _)) 4
        (metricRm04At (H.toHistory.stageMetric j.castSucc v)
          (B₀.point j.castSucc hfj (Fin.le_last _))) ≤ 1
      exact hb
  · intro j hj hjl y
    let jH : Fin H.eventCount := ⟨j.val, j.isLt⟩
    have hjcast : jH.castSucc = j.castSucc := by
      apply Fin.ext
      rfl
    have hfj : first ≤ j.castSucc := hfirst.trans hj
    have hfjH : first ≤ jH.castSucc := hjcast ▸ hfj
    have hcross := (A.toHistory.crossed_event_iff_mem_Ioc a time j).mp
      ⟨hj, by simpa only [hactive] using hjl⟩
    have hb := hbound (H.time jH.succ) ⟨hcross.1.le, hcross.2⟩ z hz
    rw [hslabs jH hfjH (H.time jH.succ)
        ⟨(H.time_strictMono jH.castSucc_lt_succ).le, le_rfl⟩,
      ObservedHistory.rmNormSq_incomingFootprint_slab H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) G K,
      (H.toHistory.event jH).terminal.extendedMetric_terminal] at hb
    have hy : H.toHistory.backwardSurvivorTerminalMap first (Fin.last H.eventCount)
        (Fin.le_last first) jH hfjH (Fin.le_last _) z.val.val = y := by
      apply Subtype.ext
      exact H.toHistory.backwardSurvivorMap_eq_point first (Fin.last H.eventCount)
        (Fin.le_last first) jH.castSucc hfjH (Fin.le_last _) z.val.val B₀
    rw [hy] at hb
    change r ^ 4 * normSq0S (H.coreEvent jH).toMetricCutCapEvent.terminal.metric y 4
      (metricRm04At (H.coreEvent jH).toMetricCutCapEvent.terminal.metric y) ≤ 1
    exact hb

open private OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume

private theorem RetainedCoreHistory.eventually_incomingFootprint_ball_subset_and_curvature_bound
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric) (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (p : G.terminalRegularOpen) {r : ℝ} (c : ℝ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p r))
    (hfirst : H.time first ≤ c) (hroom : c ≤ s - r ^ 2)
    (U : Set (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K))
    (hcapture : riemannianBallOf L.metric p r ⊆
      H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K '' U)
    (hbound : ∀ v ∈ Ico c s, ∀ z ∈ U,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    ∀ᶠ t in 𝓝[<] s,
      H.horizon < t ∧ t < s ∧ H.time first ≤ t - ρ ^ 2 ∧
      riemannianBallOf (G.flow.base.metric t) p.val ρ ⊆
        (fun z => (H.toHistory.backwardSurvivorIncomingFootprintMap first
          (Fin.last H.eventCount) (Fin.le_last first) G K z).val) '' U ∧
      ∀ v ∈ Icc (t - ρ ^ 2) t, ∀ z ∈ U,
        ρ ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1 := by
  have hr : 0 < r := hρ.trans hρr
  obtain ⟨R, hρR, hRr⟩ := exists_between hρr
  have hclosedR : IsClosed (riemannianClosedBallOf L.metric p R) :=
    isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist L.metric p)
      continuous_const
  have hcompactR : IsCompact (riemannianClosedBallOf L.metric p R) :=
    hcompact.of_isClosed_subset hclosedR (riemannianClosedBallOf_mono L.metric p hRr.le)
  have htime : c + ρ ^ 2 < s := by
    have hsq : ρ ^ 2 < r ^ 2 := by nlinarith
    linarith
  filter_upwards [Ioo_mem_nhdsLT hs, Ioo_mem_nhdsLT htime,
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ball_subset_compact_terminal_ball
      L p hρ hρR hcompactR] with t ht htroom htball
  have hroom' : H.time first ≤ t - ρ ^ 2 := by linarith [htroom.1]
  refine ⟨ht.1, ht.2, hroom', ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := htball hx
    have hy' : y ∈ riemannianBallOf L.metric p r := by
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr)
    obtain ⟨z, hz, hzy⟩ := hcapture hy'
    exact ⟨z, hz, congrArg Subtype.val hzy⟩
  · intro v hv z hz
    have hcv : c ≤ v := by linarith [htroom.1, hv.1]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ.le hρr.le 4)
      (normSq0S_nonneg _ _ _ _)).trans
        (hbound v ⟨hcv, hv.2.trans_lt ht.2⟩ z hz)

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem volume_ball_eq_of_activeStage_eq
    (A : ObservedHistory.{u}) (t : Icc (0 : ℝ) A.horizon)
    (last : Fin (A.eventCount + 1)) (hlast : A.activeStage t = last)
    (p : (A.stageAt t).Carrier) (q : (A.stage last).Carrier) (hpq : HEq p q) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel (A.stageAt t).Carrier
        (A.stageMetric (A.activeStage t) t)
        (riemannianBallOf (A.stageMetric (A.activeStage t) t) p r) =
      riemannianVolumeMeasure ThreeModel (A.stage last).Carrier
        (A.stageMetric last t) (riemannianBallOf (A.stageMetric last t) q r) := by
  subst last
  have hpq' : p = q := eq_of_heq hpq
  subst q
  rfl

theorem RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (p : G.terminalRegularOpen) {r κ σ : ℝ} (hr : 0 < r) (hrσ : r ≤ σ)
    (c : ℝ) (hcompact : IsCompact (riemannianClosedBallOf L.metric p r))
    (hfirst : H.time first ≤ c) (hroom : c ≤ s - r ^ 2)
    (U : Set (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K))
    (hcapture : riemannianBallOf L.metric p r ⊆
      H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K '' U)
    (hbound : ∀ v ∈ Ico c s, ∀ z ∈ U,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric p r) := by
  apply L.volume_ball_ge_of_eventually_volume_ball_ge p hr hcompact
  intro ρ hρ hρr
  filter_upwards [H.eventually_incomingFootprint_ball_subset_and_curvature_bound G L hs first K
    gflow p c hcompact hfirst hroom U hcapture hbound hρ hρr] with t ht
  obtain ⟨ht, hts, hroomt, hballt, hboundt⟩ := ht
  let A := H.extendHorizon t ht.le
    (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit
  let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩
  obtain ⟨q, hqp, htest⟩ :=
    H.isParabolicallyRmControlledBall_extendHorizon_of_incomingFootprint G L hinit first K
      gflow hslabs hlast ht hts hρ hroomt p.val U hballt hboundt
  have hvol := htested t ht hts q ρ hρ (hρr.le.trans hrσ) htest
  have hactive : A.toHistory.activeStage time = Fin.last H.eventCount :=
    A.toHistory.activeStage_at_horizon
  have hvolume := volume_ball_eq_of_activeStage_eq A.toHistory time (Fin.last H.eventCount)
    hactive q p.val hqp ρ
  have hmetric : A.toHistory.stageMetric (Fin.last H.eventCount) t = G.flow.base.metric t :=
    A.toHistory.stageMetric_last_of_lt (h := H.time_le_horizon.trans_lt ht) t
  change ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
    riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
      (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
      (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ) at hvol
  rw [hvolume] at hvol
  change ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
    riemannianVolumeMeasure ThreeModel (A.toHistory.stage (Fin.last H.eventCount)).Carrier
      (A.toHistory.stageMetric (Fin.last H.eventCount) t)
      (riemannianBallOf (A.toHistory.stageMetric (Fin.last H.eventCount) t) p.val ρ) at hvol
  rwa [hmetric] at hvol

theorem RetainedCoreHistory.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    {c : ℝ} (hfirst : H.time first ≤ c) (hcs : c ≤ s)
    (S : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K) (RealTimeInterval.closed c s hcs))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      S.base.metric v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (p : G.terminalRegularOpen)
    (B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric p B.radius))
    (himage : H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
      (Fin.le_last first) G K '' B.set = riemannianBallOf L.metric p B.radius)
    {κ σ : ℝ} (hrσ : B.radius ≤ σ)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal B.radius ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric p B.radius) := by
  have hstart : c ≤ s - B.radius ^ 2 :=
    (hB.1 ⟨le_rfl, sub_le_self s (sq_nonneg B.radius)⟩).1
  apply H.terminal_volume_ball_ge_of_tested_incomingFootprint G L hinit hs first K
    S.base.metric hslabs hlast p B.radius_pos hrσ (s - B.radius ^ 2) hcompact
    (hfirst.trans hstart) le_rfl B.set himage.ge
  · intro v hv z hz
    exact hB.2 v ⟨hv.1, hv.2.le⟩ z hz
  · exact htested

theorem RetainedCoreHistory.normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    {c : ℝ} (hfirst : H.time first ≤ c) (hcs : c ≤ s)
    (S : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K) (RealTimeInterval.closed c s hcs))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      S.base.metric v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (x p : G.terminalRegularOpen)
    {Q r a R : ℝ} (hQ : 0 < Q) (hr : 0 ≤ r) (hra : r + a ≤ R)
    (B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩)
    (hB : B.IsParabolicallyRmControlled)
    (hradius : B.radius = a / Real.sqrt Q)
    (hcompact : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ L.metric) x R))
    (hp : p ∈ riemannianClosedBallOf (scaleMetric Q hQ L.metric) x r)
    (himage : H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
      (Fin.le_last first) G K '' B.set = riemannianBallOf L.metric p B.radius)
    {κ σ : ℝ} (hrσ : B.radius ≤ σ)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal (κ * a ^ 3) ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen (scaleMetric Q hQ L.metric)
        (riemannianBallOf (scaleMetric Q hQ L.metric) p a) := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hscale : Real.sqrt Q * B.radius = a := by
    rw [hradius]
    field_simp
  have ha : 0 < a := hscale ▸ mul_pos hsqrt B.radius_pos
  have hsmall : IsCompact
      (riemannianClosedBallOf (scaleMetric Q hQ L.metric) p a) :=
    hcompact.of_isClosed_subset
      (isClosed_le (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
        (scaleMetric Q hQ L.metric) p) continuous_const)
      (riemannianClosedBallOf_subset_of_add_radius_le (scaleMetric Q hQ L.metric)
        hr ha.le hra hp)
  have hphysical : IsCompact (riemannianClosedBallOf L.metric p B.radius) := by
    rw [← riemannianClosedBallOf_scaleMetric Q hQ, hscale]
    exact hsmall
  have hv := H.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball G L hinit hs
    first K hfirst hcs S hslabs hlast p B hB hphysical himage hrσ htested
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled :=
    (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
      L.metric Q hQ p B.radius (ENNReal.ofReal κ)).mpr (by simpa only [hdim] using hv)
  rw [hscale, hdim] at hscaled
  simpa only [ENNReal.ofReal_mul' (pow_nonneg ha.le 3), ENNReal.ofReal_pow ha.le] using hscaled

theorem RetainedCoreHistory.exists_uniform_terminal_volume_lower_of_spatial_rm_bound_and_tested_history
    (D rcap eps R₁ κtest : ℝ) (C : ℝ≥0) (hκtest : 0 < κtest)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hrcap : StandardCap.transitionEnd + eps⁻¹ + 1 < rcap)
    (hfit : 64 * (rcap + eps⁻¹) < D)
    (hR₁ : 0 < R₁) (hRmargin : R₁ + 1 < D)
    (hreserve : 2 * StandardCap.transitionEnd + 4 < R₁ / 2) :
    ∃ C₀ η ε₀ δ₀ κ : ℝ, 0 < C₀ ∧ 0 < κ ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1 / 4 → 4 * θ ≤ η →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : RetainedCoreHistory.{u}) (first : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
        (H.time (Fin.last H.eventCount)) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q σ : ℝ},
    0 < r →
    r ≤ 1 → let Q := 16 / r ^ 2;
    ∀ hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount),
    H.horizon < s →
    IsCompact (riemannianClosedBallOf L.metric x (r / 2)) →
    0 < q → q ≤ Q →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y : (H.stage (Fin.last H.eventCount)).Carrier,
      ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc →
      Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) Phi) →
    (∀ y ∈ riemannianBallOf L.metric x r,
      r ^ 4 * normSq0S L.metric y 4 (metricRm04At L.metric y) ≤ 1) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc →
      s - θ / Q < H.time j.succ) →
    ∀ (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H.toHistory j parameters),
    (∀ j : Fin H.eventCount, first ≤ j.castSucc →
      ∀ (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records j).static b).neck.scale / 2 ≤
          metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
    D + 1 ≤ parameters.modelRadius → ⌈eps⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    parameters.modelAccuracy ≤ ε₀ →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc →
      ∀ b : (H.toHistory.event k).RetainedBoundaryIndex, ((records k).static b).hasCanonicalWindow) →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc → ∀ b, (records k).delta b ≤ δ₀) →
    ∀ a₀ : ℝ,
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc →
      ∀ b : (H.toHistory.event k).RetainedBoundaryIndex,
        q ≤ C₀ * ((records k).static b).neck.scale ∧ 1 ≤ a₀ * ((records k).static b).neck.scale) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    α * r / 4 ≤ σ →
    (∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κtest * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) →
    ENNReal.ofReal κ * ENNReal.ofReal (α * r / 4) ^ 3 ≤
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
        (riemannianBallOf L.metric x (α * r / 4)) := by
  obtain ⟨C₀, η, ε₀, δ₀, κcap, hC₀, hκcap, hη, hε₀, hεhalf, hδ₀, hvolume⟩ :=
    ObservedHistory.exists_uniform_parabolic_ball_or_volume_lower_of_spatial_rm_bound
      D rcap eps R₁ C heps hepssmall hrcap hfit hR₁ hRmargin hreserve
  refine ⟨C₀, η, ε₀, δ₀, min κcap κtest, hC₀, lt_min hκcap hκtest,
    hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro Phi hPhi θ hθ hθsmall hηθ
  obtain ⟨α, hα, hα1, hαθ, hball⟩ := hvolume Phi hPhi θ hθ hθsmall hηθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first s G L x r q σ hr hr1
  dsimp only
  intro hinit hs hcompact hq hqQ hderiv hfinal hpinch hpinchFinal hRm hcrossTime
    parameters records hcap hmargin hm haccuracy hcanonical hδ a₀ hfixed hlower
    hscalePremises hroom hbudget hrσ htested
  rcases hball H.toHistory first (Fin.last H.eventCount) (Fin.le_last first) G L x hr hr1
    hinit hcompact hq hqQ (fun j hf _ => hderiv j hf) hfinal
    (fun j hf _ => hpinch j hf) hpinchFinal hRm (fun j hf _ => hcrossTime j hf)
    parameters records (fun j hf _ => hcap j hf) hmargin hm haccuracy
    (fun j hf _ => hcanonical j hf) (fun j hf _ => hδ j hf) a₀ hfixed hlower
    (fun j hf _ => hscalePremises j hf) hroom hbudget with
    hflow | hcapvolume
  · obtain ⟨p, S, _, _, _, _, hslabs, hlast, B, _, hradius, hB, _, himage, _, _⟩ := hflow
    have hclosed : IsClosed (riemannianClosedBallOf L.metric x B.radius) :=
      isClosed_le (Geometry.Riemannian.continuous_riemannianEDist L.metric x) continuous_const
    have hradiusle : B.radius ≤ r / 2 := by rw [hradius]; nlinarith
    have hcompactB : IsCompact (riemannianClosedBallOf L.metric x B.radius) :=
      hcompact.of_isClosed_subset hclosed (riemannianClosedBallOf_mono L.metric x hradiusle)
    have hvol := H.terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball
      G L hinit hs first (riemannianClosedBallOf L.metric x (r / 2)) hroom
      (sub_le_self s (div_nonneg hθ.le (by positivity))) S
      (fun j hf => hslabs j hf (Fin.le_last _)) hlast x B hB hcompactB
      (by simpa only [hradius] using himage) (by simpa only [hradius] using hrσ) htested
    rw [hradius] at hvol
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_right κcap κtest)) le_rfl).trans hvol
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_left κcap κtest)) le_rfl).trans hcapvolume

private local instance (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) := by
  let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorDomain first (Fin.last H.eventCount)
      (Fin.le_last first)) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.toHistory.backwardSurvivorDomain first (Fin.last H.eventCount) (Fin.le_last first)).isOpen)
  let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
      (Fin.le_last first) G) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) (Fin.le_last first) G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel
    (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K).isOpen)

theorem RetainedCoreHistory.incomingFootprint_volume_ball_ge_of_tested_history_and_curvature_bound
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (p : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) {R r κ σ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hrσ : r ≤ σ)
    (hcompact : IsCompact (riemannianClosedBallOf (gflow s) p R))
    (hroom : H.time first ≤ s - r ^ 2)
    (hbound : ∀ v ∈ Ico (s - r ^ 2) s, ∀ z ∈ riemannianBallOf (gflow s) p r,
      r ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) (gflow s)
        (riemannianBallOf (gflow s) p r) := by
  have hterminal : gflow s = localPullMetric L.metric
      (H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K)
      (H.toHistory.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (Fin.last H.eventCount)
        (Fin.le_last first) G K) := by
    rw [hlast s ⟨H.time_le_horizon.trans hs.le, le_rfl⟩]
    exact H.toHistory.backwardSurvivorIncomingMetric_restrict_footprint_terminal first
      (Fin.last H.eventCount) (Fin.le_last first) G L K
  let f := H.toHistory.backwardSurvivorIncomingFootprintMap first (Fin.last H.eventCount)
      (Fin.le_last first) G K
  let hf := H.toHistory.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (Fin.last H.eventCount)
      (Fin.le_last first) G K
  have hinj : Function.Injective f := H.toHistory.backwardSurvivorIncomingFootprintMap_injective first (Fin.last H.eventCount)
      (Fin.le_last first) G K
  have hc : IsCompact (riemannianClosedBallOf (localPullMetric L.metric f hf) p R) := by
    simpa only [hterminal] using hcompact
  have himage := Geometry.Metric.image_riemannianBallOf_localPullMetric
    L.metric f hf hinj p hr hrR hc
  have himageClosed := Geometry.Metric.image_riemannianClosedBallOf_localPullMetric
    L.metric f hf hinj p hr.le hrR hc
  have hsmall : IsCompact (riemannianClosedBallOf (localPullMetric L.metric f hf) p r) :=
    hc.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ hrR.le)
  have htarget : IsCompact (riemannianClosedBallOf L.metric (f p) r) := by
    rw [← himageClosed]
    exact hsmall.image hf.contMDiff.continuous
  have himage' : f '' riemannianBallOf (gflow s) p r =
      riemannianBallOf L.metric (f p) r := by
    simpa only [hterminal] using himage
  have hvol := H.terminal_volume_ball_ge_of_tested_incomingFootprint G L hinit hs
    first K gflow hslabs hlast (f p) hr hrσ (s - r ^ 2) htarget hroom le_rfl
    (riemannianBallOf (gflow s) p r) himage'.ge hbound htested
  rw [hterminal, Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric
    L.metric f hf hinj p hr hrR hc]
  exact hvol


theorem RetainedCoreHistory.normalized_incomingFootprint_volume_ball_ge_of_tested_history_and_curvature_bound
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (hs : H.horizon < s)
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    (hlast : ∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    (p : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) {Q θ R a C κ σ : ℝ} (hQ : 0 < Q)
    (ha : 0 < a) (haR : a < R) (haσ : a / Real.sqrt Q ≤ σ)
    (hatime : a ^ 2 ≤ θ) (haC : a ^ 4 * C ≤ 1)
    (hcompact : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ (gflow s)) p R))
    (hroom : H.time first ≤ s - θ / Q)
    (hbound : ∀ v ∈ Ico (s - θ / Q) s,
      ∀ z ∈ riemannianBallOf (scaleMetric Q hQ (gflow s)) p a,
        normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ C * Q ^ 2)
    (htested : ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) :
    ENNReal.ofReal (κ * a ^ 3) ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) (scaleMetric Q hQ (gflow s))
        (riemannianBallOf (scaleMetric Q hQ (gflow s)) p a) := by
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hscale : Real.sqrt Q * (a / Real.sqrt Q) = a := by field_simp
  have hscaleR : Real.sqrt Q * (R / Real.sqrt Q) = R := by field_simp
  have hphysical : IsCompact (riemannianClosedBallOf (gflow s) p (R / Real.sqrt Q)) := by
    rwa [← hscaleR, riemannianClosedBallOf_scaleMetric] at hcompact
  have hball : riemannianBallOf (gflow s) p (a / Real.sqrt Q) =
      riemannianBallOf (scaleMetric Q hQ (gflow s)) p a := by
    simpa only [hscale] using (riemannianBallOf_scaleMetric Q hQ (gflow s) p (a / Real.sqrt Q)).symm
  have hrtime : (a / Real.sqrt Q) ^ 2 = a ^ 2 / Q := by rw [div_pow, hsq]
  have hroom' : H.time first ≤ s - (a / Real.sqrt Q) ^ 2 := by
    rw [hrtime]
    have hh := div_le_div_of_nonneg_right hatime hQ.le
    linarith
  have hbound' : ∀ v ∈ Ico (s - (a / Real.sqrt Q) ^ 2) s,
      ∀ z ∈ riemannianBallOf (gflow s) p (a / Real.sqrt Q),
        (a / Real.sqrt Q) ^ 4 * normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ 1 := by
    intro v hv z hz
    have hv' : v ∈ Ico (s - θ / Q) s := by
      rw [hrtime] at hv
      have hh := div_le_div_of_nonneg_right hatime hQ.le
      exact ⟨by linarith [hv.1], hv.2⟩
    have hh := mul_le_mul_of_nonneg_left (hbound v hv' z (hball ▸ hz))
      (pow_nonneg (div_nonneg ha.le hroot.le) 4)
    have heq : (a / Real.sqrt Q) ^ 4 * (C * Q ^ 2) = a ^ 4 * C := by
      have hfour : Real.sqrt Q ^ 4 = Q ^ 2 := by nlinarith only [hsq]
      rw [div_pow, hfour]
      field_simp
    rw [heq] at hh
    exact hh.trans haC
  have hv := H.incomingFootprint_volume_ball_ge_of_tested_history_and_curvature_bound
    G L hinit hs first K gflow hslabs hlast p (div_pos ha hroot)
    ((div_lt_div_iff_of_pos_right hroot).mpr haR) haσ hphysical hroom' hbound' htested
  have hscaled := (Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (gflow s) Q hQ p (a / Real.sqrt Q) (ENNReal.ofReal κ)).mpr
      (by simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hv)
  rw [hscale, show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] at hscaled
  simpa only [ENNReal.ofReal_mul' (pow_nonneg ha.le 3), ENNReal.ofReal_pow ha.le] using hscaled

theorem RetainedCoreHistory.exists_uniform_normalized_incomingFootprint_volume_radius
    {R θ C σ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hC : 0 ≤ C) (hσ : 0 < σ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
    ∀ (H : RetainedCoreHistory.{u}) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    , H.horizon < s → ∀ (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
        (Fin.le_last first) G K))
    , (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
      ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount)
          (Fin.le_last first) j hf (Fin.le_last _) v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount)
              (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
                  (Fin.le_last first) G K))
    → (∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
      gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
        (Fin.le_last first) G L v).restrictOpen
          (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
            (Fin.le_last first) G K))
    → ∀ (p : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) {Q κ : ℝ} (hQ : 1 ≤ Q),
    IsCompact (riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) p R) →
    H.time first ≤ s - θ / Q →
    (∀ v ∈ Ico (s - θ / Q) s, ∀ z : H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K,
      normSq0S (gflow v) z 4 (metricRm04At (gflow v) z) ≤ C * Q ^ 2) →
     (∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let A := H.extendHorizon t ht.le
        (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit;
      let time : Icc (0 : ℝ) A.horizon := ⟨t, H.horizon_nonneg.trans ht.le, le_rfl⟩;
      ∀ (q : (A.toHistory.stageAt time).Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ σ →
        A.toHistory.isParabolicallyRmControlledBall time q ρ →
          ENNReal.ofReal κ * ENNReal.ofReal ρ ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) q ρ)) →
    ∀ x ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) p (R / 4),
      ENNReal.ofReal (κ * a ^ 3) ≤
        riemannianVolumeMeasure ThreeModel (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount)
      (Fin.le_last first) G K) (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s))
          (riemannianBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow s)) x a) := by
  let a₀ := min (R / 8) (min (Real.sqrt θ / 2) (min (1 / (C + 1)) σ))
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; positivity
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha haa₀ H s G L hinit hs first K gflow hslabs hlast p Q κ hQ hcpt hroom hbound htested x hx
  have haR : a ≤ R / 8 := haa₀.trans (min_le_left _ _)
  have hatheta : a ≤ Real.sqrt θ / 2 :=
    haa₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haC : a ≤ 1 / (C + 1) :=
    haa₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haσ : a ≤ σ :=
    haa₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hatime : a ^ 2 ≤ θ := by nlinarith [Real.sq_sqrt hθ.le, Real.sqrt_nonneg θ]
  have haone : a ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity)).mp haC
    nlinarith [mul_nonneg ha.le hC]
  have haCbound : a * C ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity)).mp haC
    nlinarith
  have hac : a ^ 4 * C ≤ 1 := by
    have hh := mul_le_mul (pow_le_one₀ (n := 3) ha.le haone) haCbound (mul_nonneg ha.le hC) zero_le_one
    nlinarith only [hh]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hroot : 1 ≤ Real.sqrt Q := (Real.one_le_sqrt).mpr hQ
  have haroot : a / Real.sqrt Q ≤ σ :=
    (div_le_self ha.le hroot).trans haσ
  have hcptx : IsCompact (riemannianClosedBallOf (scaleMetric Q hQpos (gflow s)) x (R / 2)) :=
    hcpt.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_subset_of_add_radius_le _ (by positivity : 0 ≤ R / 4)
        (by positivity : 0 ≤ R / 2) (by linarith : R / 4 + R / 2 ≤ R) hx)
  exact H.normalized_incomingFootprint_volume_ball_ge_of_tested_history_and_curvature_bound
    G L hinit hs first K gflow hslabs hlast x hQpos ha (by linarith : a < R / 2) haroot
    hatime hac hcptx hroom (fun v hv z _ => hbound v hv z) htested

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
