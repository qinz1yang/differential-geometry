import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckAppend
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X

/-!
# Deep backward necks at an appended event (C12X, S16 round 3, O-C12X-S16K G1a)

Producer side of the route-β record contract `IncomingBackwardNeckDeep_C12X` (S16H G4a).  The
record backward necks of the main chain are produced by
`NormalizedNeck.exists_incomingBackwardNeck_appendEvent` (ST/IncomingBackwardNeckAppend) from a
historical row: a solution `S` on a closed window `[-θS, 0]`, the metric identification of `S`
with the rescaled backward survivor metric, the survivor footprint chart, and the time-difference
jets with parabolic closeness on `[-1, 0]`.  The rows of the main chain
(ST/ProspectiveNeckSurvivalVariableThreshold) have depth two (`θS = 2`) and converge to the
shrinking cylinder on `[-3/2, 0]`.

`NormalizedNeck.exists_incomingBackwardNeckDeep_appendEvent_C12X` is the deep analogue: for a
depth factor `1 < θ < θS`, metric identification on `Ico (-θ) 0`, the deep start
`time first ≤ s - θ / scale`, and jets with closeness on both `[-1, 0]` and `[-θ, 0]`, it builds
the deep backward neck (same metric, same charts on the depth-one range).  No tracked file is
changed: the private transport lemmas of the depth-one construction are reused via `open private`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private appendEvent_event_castSucc_heq appendEvent_event_last_heq exists_neck_heq
  castStageMap castStageMap_smooth neck_normalizedMetric_eq neck_chart_transport
  crossing_transport metric_transport ObservedHistory.prospective_slab_metric_inner
  ObservedHistory.prospective_final_metric_inner first_le_stage_of_time_lt
  solution_metric_smooth_on_neckBuffer from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckAppend

private local instance deepNeckBufferSigmaCompact_C12X {δ : ℝ} :
    SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)

/-- Local smooth coefficients of a solution metric on the deep window `[-θ, 0]`. -/
private theorem solution_metric_smooth_on_neckBuffer_deep_C12X {δ θ θS : ℝ} (hθ : 0 < θ)
    (hθS : θ < θS)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θS) 0 (by linarith))) (hS : IsSolutionOn S) :
    ∀ p : neckBuffer δ, ∀ t ∈ Icc (-θ) 0,
      ∃ U : Set (neckBuffer δ), IsOpen U ∧ p ∈ U ∧
        U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace NeckCylinderModel) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × neckBuffer δ → (EuclideanSpace ℝ (Fin 2) × ℝ) →
          (EuclideanSpace ℝ (Fin 2) × ℝ) → ℝ,
        (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod NeckCylinderModel) 𝓘(ℝ, ℝ) ∞
          (fun z => A z v w) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ Icc (-θ) 0, ∀ x ∈ U, ∀ v w,
          A (s, x) v w = (S.base.metric s).inner x
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x v)
            ((trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
              (TangentSpace NeckCylinderModel) p).symmL ℝ x w) := by
  intro p t _
  have hg := solution_metricCLMSection_contMDiffOn_closed S hS
    (show -θS < -θ by linarith) (show -θ < (0 : ℝ) by linarith)
    (show Icc (-θS) 0 ⊆ (RealTimeInterval.closed (-θS) 0 (by linarith)).carrier from
      Subset.rfl)
    (show Ioo (-θS) 0 ⊆ (RealTimeInterval.closed (-θS) 0 (by linarith)).regular from
      Subset.rfl)
  obtain ⟨U, hU, hp, hUb, A, hA, hEq⟩ :=
    Geometry.Metric.exists_local_metric_coefficient_extension S.base.metric
      (show -θ < (0 : ℝ) by linarith) hg p
  exact ⟨U, hU, hp, hUb, univ, isOpen_univ, mem_univ t, A, hA,
    fun s hs x hx v w => hEq s hs.2 x hx v w⟩

set_option maxHeartbeats 400000 in
-- One structure literal with both the depth-one and the deep fields (two copies of the slab
-- metric transport); the depth-one original alone is close to the default budget.
/-- **Deep backward neck at an appended event.**  Same data as
`NormalizedNeck.exists_incomingBackwardNeck_appendEvent`, with the metric identification on the
deep window `Ico (-θ) 0`, the deep start `time first ≤ s - θ / scale`, and jets with closeness on
`[-θ, 0]` in addition to `[-1, 0]` (`1 < θ < θS`, the row solution lives on `[-θS, 0]`). -/
theorem NormalizedNeck.exists_incomingBackwardNeckDeep_appendEvent_C12X
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (hle : first ≤ Fin.last H.eventCount) {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k)
    (K : Set E.incoming.terminalRegularOpen)
    (Φ : neckBuffer δ → H.backwardSurvivorIncomingFootprint first
      (Fin.last H.eventCount) hle E.incoming K)
    (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
    (hmap : H.backwardSurvivorIncomingFootprintMap first
      (Fin.last H.eventCount) hle E.incoming K ∘ Φ = N.chart)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    {θ θS : ℝ} (hθ : 1 < θ) (hθS : θ < θS)
    (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
      (RealTimeInterval.closed (-θS) 0 (by linarith))) (hS : IsSolutionOn S)
    (hterminal : S.base.metric 0 = N.normalizedMetric)
    (hmetric : ∀ t ∈ Ico (-θ) 0, S.base.metric t = localPullMetric
      (scaleMetric N.scale N.scale_pos (G (s + t / N.scale))) Φ hΦ)
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ Fin.last H.eventCount),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle
          j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle
            E.incoming)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    (hlast : ∀ t ∈ Icc (H.time (Fin.last H.eventCount)) s,
      G t = (H.backwardSurvivorIncomingMetric first (Fin.last H.eventCount) hle
        E.incoming E.terminal t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K))
    (hstart : H.time first ≤ s - θ * N.scale⁻¹)
    (Z : (b : ℕ) → (v : Icc (-1 : ℝ) 0) →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZ : ∀ b v x, Z b v x = iteratedDerivWithin b
      (fun t => metricTensorField (S.base.metric t) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x)
      (Icc (-1 : ℝ) 0) v.1)
    (hclose : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2 * b ≤ k →
      ∀ v : Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g x (a + 2) (cylinderTensorCovDeriv g (Z b v) a x)) ≤ η)
    (Zd : (b : ℕ) → (v : Icc (-θ) 0) →
      Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2)
    (hZd : ∀ b v x, Zd b v x = iteratedDerivWithin b
      (fun t => metricTensorField (S.base.metric t) x -
        metricTensorField ((shrinkingCylinderMetric
          ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)) x)
      (Icc (-θ) 0) v.1)
    (hcloseD : ∃ η : ℝ, η < δ ∧ ∀ a b : ℕ, a + 2 * b ≤ k →
      ∀ v : Icc (-θ) 0, ∀ x ∈ neckClosedTest δ,
        let g := (shrinkingCylinderMetric
          ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
        Real.sqrt (normSq0S g x (a + 2) (cylinderTensorCovDeriv g (Zd b v) a x)) ≤ η) :
    ∃ N' : NormalizedNeck
      ((H.appendEvent E.incoming.lt E hinit).event (Fin.last H.eventCount)).terminal.metric δ k,
      HEq N' N ∧ ∃ D : IncomingBackwardNeckDeep_C12X (H.appendEvent E.incoming.lt E hinit)
        (Fin.last H.eventCount) N' (Real.sqrt N.scale⁻¹) θ,
        D.metric = S.base.metric := by
  let J := H.appendEvent E.incoming.lt E hinit
  let r := Real.sqrt N.scale⁻¹
  have hrsq : r ^ 2 = N.scale⁻¹ := Real.sq_sqrt (inv_nonneg.mpr N.scale_pos.le)
  have hinvpos : 0 < N.scale⁻¹ := inv_pos.mpr N.scale_pos
  have hstart1 : H.time first ≤ s - N.scale⁻¹ := by
    have h1 : N.scale⁻¹ ≤ θ * N.scale⁻¹ := le_mul_of_one_le_left hinvpos.le hθ.le
    linarith
  have htime : J.time (Fin.last H.eventCount).succ = s :=
    H.appendEvent_time_last E.incoming.lt E hinit
  have hstage (j : Fin (H.eventCount + 1)) : J.stage j.castSucc = H.stage j :=
    H.appendEvent_stage_castSucc E.incoming.lt E hinit j
  have htimeOld (j : Fin (H.eventCount + 1)) : J.time j.castSucc = H.time j :=
    H.appendEvent_time_castSucc E.incoming.lt E hinit j
  have htimeCastSucc (j : Fin H.eventCount) : J.time j.castSucc.succ = H.time j.succ :=
    htimeOld j.succ
  have hevent := appendEvent_event_last_heq H E hinit
  obtain ⟨N', hneck⟩ := exists_neck_heq (hstage (Fin.last H.eventCount)).symm
    (H.extendStage_last Q E.outputMetric).symm
    (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm N
  refine ⟨N', hneck, ?_⟩
  have hf (j : Fin (H.eventCount + 1))
      (ha : J.time (Fin.last H.eventCount).succ - r ^ 2 < J.time j.succ) :
      first ≤ j := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply first_le_stage_of_time_lt hstart1 j
      simpa only [htime, hrsq, htimeCastSucc] using ha
    · exact hle
  have hfd (j : Fin (H.eventCount + 1))
      (ha : J.time (Fin.last H.eventCount).succ - θ * r ^ 2 < J.time j.succ) :
      first ≤ j := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · apply first_le_stage_of_time_lt hstart j
      simpa only [htime, hrsq, htimeCastSucc] using ha
    · exact hle
  let Ψ : neckBuffer δ → H.backwardSurvivorDomain first (Fin.last H.eventCount) hle :=
    fun x => (Φ x).val.val
  have hPhiEmb : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ := by
    apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hΦ
    intro x y hxy
    apply N.chart_smooth.isEmbedding.injective
    rw [← hmap]
    exact congrArg (H.backwardSurvivorIncomingFootprintMap first
      (Fin.last H.eventCount) hle E.incoming K) hxy
  have hΨ : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Ψ := by
    apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel
      (H.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) hle E.incoming)
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
      NeckCylinderModel ThreeModel
      (H.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) hle E.incoming K) Φ
      hPhiEmb
  let baseChart (j : Fin (H.eventCount + 1)) (hj : first ≤ j) :
      C(neckBuffer δ, (H.stage j).Carrier) :=
    ⟨H.backwardSurvivorMap first (Fin.last H.eventCount) hle j hj (Fin.le_last j) ∘ Ψ,
      ((H.backwardSurvivorMap_isSmoothEmbedding first (Fin.last H.eventCount) hle j hj
        (Fin.le_last j)).contMDiff.comp hΨ.contMDiff).continuous⟩
  let chart (j : Fin J.eventCount) (_hj : j.val ≤ (Fin.last H.eventCount).val)
      (ha : J.time (Fin.last H.eventCount).succ - r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap (hstage j).symm (baseChart j (hf j ha))
  let deepChart (j : Fin J.eventCount) (_hj : j.val ≤ (Fin.last H.eventCount).val)
      (ha : J.time (Fin.last H.eventCount).succ - θ * r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap (hstage j).symm (baseChart j (hfd j ha))
  change ∃ D : IncomingBackwardNeckDeep_C12X J (Fin.last H.eventCount) N' r θ,
    D.metric = S.base.metric
  refine ⟨{
    radius_pos := Real.sqrt_pos.mpr hinvpos
    left_nonneg := by erw [htime, hrsq]; exact (H.time_nonneg first).trans hstart1
    stageChart := chart
    stageChart_smooth := ?_
    terminal_chart := ?_
    crossing := ?_
    metric := S.base.metric
    terminal_metric := hterminal.trans ?_
    metric_on_slab := ?_
    timeDifferenceJet := Z
    timeDifferenceJet_eq := hZ
    parabolic_closeness := hclose
    metric_smooth := solution_metric_smooth_on_neckBuffer (lt_trans hθ hθS) S hS
    one_le_depth := hθ.le
    deep_left_nonneg := by erw [htime, hrsq]; exact (H.time_nonneg first).trans hstart
    deepChart := deepChart
    deepChart_smooth := ?_
    deepChart_eq := fun _ _ _ _ => rfl
    deep_crossing := ?_
    deep_metric_on_slab := ?_
    deepJet := Zd
    deepJet_eq := hZd
    deep_closeness := hcloseD
    deep_metric_smooth :=
      solution_metric_smooth_on_neckBuffer_deep_C12X (by linarith) hθS S hS }, rfl⟩
  · intro j hj ha
    apply castStageMap_smooth
    exact (H.backwardSurvivorMap_isSmoothEmbedding first (Fin.last H.eventCount) hle j
      (hf j ha) (Fin.le_last j)).comp hΨ (by decide)
  · intro ha
    apply neck_chart_transport (hstage (Fin.last H.eventCount)).symm
      (H.extendStage_last Q E.outputMetric).symm
      (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm hneck.symm
    intro x
    change H.backwardSurvivorMap first (Fin.last H.eventCount) hle
      (Fin.last H.eventCount) _ _ (Ψ x) = _
    rw [H.backwardSurvivorMap_last]
    exact congrArg Subtype.val (congrFun hmap x)
  · intro j hj next ha hn
    let j₀ : Fin H.eventCount := ⟨j.val, hj⟩
    exact crossing_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
      (appendEvent_event_castSucc_heq H E hinit j₀).symm
      (baseChart j₀.castSucc (hf j ha)) (baseChart j₀.succ (hf next hn))
      (fun x => H.backwardSurvivorMap_crossing first (Fin.last H.eventCount) hle j₀
        (hf j ha) (Fin.le_last j₀.succ) (Ψ x))
  · exact neck_normalizedMetric_eq (hstage (Fin.last H.eventCount)).symm
      (H.extendStage_last Q E.outputMetric).symm
      (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm hneck.symm
  · intro j hj ha v hv htlo hthi x V W
    have hv' : v ∈ Ico (-θ) 0 := ⟨by linarith [hv.1], hv.2⟩
    have hnormalized : s + r ^ 2 * v = s + v / N.scale := by
      rw [hrsq, div_eq_mul_inv, mul_comm]
    have hscale : (r ^ 2)⁻¹ = N.scale := by rw [hrsq, inv_inv]
    erw [htime, hnormalized] at htlo hthi ⊢
    rw [hmetric v hv', hscale]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
    · have hlo : H.time j₀.castSucc ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < H.time j₀.succ := by
        erw [htimeCastSucc] at hthi
        exact hthi
      have hm := ObservedHistory.prospective_slab_metric_inner H first (Fin.last H.eventCount)
        hle E.incoming K G N.scale N.scale_pos Φ hΦ j₀ (hf j₀.castSucc ha)
        (Fin.le_last j₀.succ) hhi (hslabs j₀ _ _ _ ⟨hlo, hhi.le⟩) x V W
      have hc := metric_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
        (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
        (appendEvent_event_castSucc_heq H E hinit j₀).symm
        (baseChart j₀.castSucc (hf j₀.castSucc ha)) (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)
    · have hlo : H.time (Fin.last H.eventCount) ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < s := by
        erw [htime] at hthi
        exact hthi
      have hm := ObservedHistory.prospective_final_metric_inner H first (Fin.last H.eventCount)
        hle E.incoming E.terminal K G N.scale N.scale_pos Φ hΦ hhi (hlast _ ⟨hlo, hhi.le⟩)
        x V W
      have hc := metric_transport (hstage (Fin.last H.eventCount)).symm
        (H.extendStage_last Q E.outputMetric).symm
        (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm
        (baseChart (Fin.last H.eventCount) (hf (Fin.last H.eventCount) ha))
        (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)
  · intro j hj ha
    apply castStageMap_smooth
    exact (H.backwardSurvivorMap_isSmoothEmbedding first (Fin.last H.eventCount) hle j
      (hfd j ha) (Fin.le_last j)).comp hΨ (by decide)
  · intro j hj next ha hn
    let j₀ : Fin H.eventCount := ⟨j.val, hj⟩
    exact crossing_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
      (appendEvent_event_castSucc_heq H E hinit j₀).symm
      (baseChart j₀.castSucc (hfd j ha)) (baseChart j₀.succ (hfd next hn))
      (fun x => H.backwardSurvivorMap_crossing first (Fin.last H.eventCount) hle j₀
        (hfd j ha) (Fin.le_last j₀.succ) (Ψ x))
  · intro j hj ha v hv htlo hthi x V W
    have hnormalized : s + r ^ 2 * v = s + v / N.scale := by
      rw [hrsq, div_eq_mul_inv, mul_comm]
    have hscale : (r ^ 2)⁻¹ = N.scale := by rw [hrsq, inv_inv]
    erw [htime, hnormalized] at htlo hthi ⊢
    rw [hmetric v hv, hscale]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
    · have hlo : H.time j₀.castSucc ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < H.time j₀.succ := by
        erw [htimeCastSucc] at hthi
        exact hthi
      have hm := ObservedHistory.prospective_slab_metric_inner H first (Fin.last H.eventCount)
        hle E.incoming K G N.scale N.scale_pos Φ hΦ j₀ (hfd j₀.castSucc ha)
        (Fin.le_last j₀.succ) hhi (hslabs j₀ _ _ _ ⟨hlo, hhi.le⟩) x V W
      have hc := metric_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
        (htimeOld j₀.castSucc).symm (htimeOld j₀.succ).symm
        (appendEvent_event_castSucc_heq H E hinit j₀).symm
        (baseChart j₀.castSucc (hfd j₀.castSucc ha)) (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)
    · have hlo : H.time (Fin.last H.eventCount) ≤ s + v / N.scale := by
        erw [htimeOld] at htlo
        exact htlo
      have hhi : s + v / N.scale < s := by
        erw [htime] at hthi
        exact hthi
      have hm := ObservedHistory.prospective_final_metric_inner H first (Fin.last H.eventCount)
        hle E.incoming E.terminal K G N.scale N.scale_pos Φ hΦ hhi (hlast _ ⟨hlo, hhi.le⟩)
        x V W
      have hc := metric_transport (hstage (Fin.last H.eventCount)).symm
        (H.extendStage_last Q E.outputMetric).symm
        (htimeOld (Fin.last H.eventCount)).symm htime.symm hevent.symm
        (baseChart (Fin.last H.eventCount) (hfd (Fin.last H.eventCount) ha))
        (s + v / N.scale) x V W
      exact hm.trans (congrArg (N.scale * ·) hc.symm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
