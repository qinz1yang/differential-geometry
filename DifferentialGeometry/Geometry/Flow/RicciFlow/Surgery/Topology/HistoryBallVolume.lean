import DifferentialGeometry.Geometry.Comparison.Volume.CompactSmallBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBallRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapRegularCrossing
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizerInwardPoint


noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open scoped Manifold ContDiff Topology ENNReal NNReal

private theorem exists_radius_enlargement_of_compact_strict_bound
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (d : M → ℝ≥0∞) (hd : Continuous d) (U : TopologicalSpace.Opens M)
    {a T r R : ℝ} (hrR : r < R) (ha : a < T - r ^ 2)
    (F : Icc a T × U → ℝ) (hF : Continuous F)
    (hbound : ∀ (t : Icc a T) (x : M), T - r ^ 2 ≤ t.val →
      d x ≤ ENNReal.ofReal r → ∃ y : U, y.val = x ∧ r ^ 4 * F (t, y) < 1) :
    ∃ r' : ℝ, r < r' ∧ r' < R ∧ a < T - r' ^ 2 ∧
      ∀ (t : Icc a T) (x : M), T - r' ^ 2 ≤ t.val →
        d x ≤ ENNReal.ofReal r' → ∃ y : U, y.val = x ∧ r' ^ 4 * F (t, y) < 1 := by
  let A : Set (ℝ × (Icc a T × M)) := {z | z.2.1.val < T - z.1 ^ 2}
  let B : Set (ℝ × (Icc a T × M)) := {z | ENNReal.ofReal z.1 < d z.2.2}
  let C : Set (ℝ × (Icc a T × U)) := {z | z.1 ^ 4 * F z.2 < 1}
  let f : ℝ × (Icc a T × U) → ℝ × (Icc a T × M) :=
    Prod.map id (Prod.map id Subtype.val)
  have hA : IsOpen A := isOpen_lt (by fun_prop) (by fun_prop)
  have hB : IsOpen B := isOpen_lt (ENNReal.continuous_ofReal.comp continuous_fst)
    (hd.comp (continuous_snd.comp continuous_snd))
  have hC : IsOpen C := isOpen_lt (by fun_prop) continuous_const
  have hf : IsOpenMap f := IsOpenMap.id.prodMap (IsOpenMap.id.prodMap U.isOpenEmbedding'.isOpenMap)
  have hn : IsOpen (A ∪ B ∪ f '' C) := (hA.union hB).union (hf _ hC)
  have hs : ({r} : Set ℝ) ×ˢ (univ : Set (Icc a T × M)) ⊆ A ∪ B ∪ f '' C := by
    rintro ⟨q, t, x⟩ ⟨hq, _⟩
    have hqr : q = r := hq
    subst q
    by_cases ht : t.val < T - r ^ 2
    · exact Or.inl (Or.inl ht)
    by_cases hx : ENNReal.ofReal r < d x
    · exact Or.inl (Or.inr hx)
    obtain ⟨y, rfl, hy⟩ := hbound t x (le_of_not_gt ht) (le_of_not_gt hx)
    exact Or.inr ⟨(r, t, y), hy, rfl⟩
  obtain ⟨V, W, hV, _, hrV, hW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hs
  have hnear : V ∩ Iio R ∩ {q : ℝ | a < T - q ^ 2} ∈ 𝓝 r := by
    refine inter_mem (inter_mem (hV.mem_nhds (hrV (mem_singleton r))) (Iio_mem_nhds hrR)) ?_
    exact (show ContinuousAt (fun q : ℝ => T - q ^ 2) r by fun_prop).eventually_const_lt ha
  have hevent : ∀ᶠ q in 𝓝[>] r, q ∈ V ∩ Iio R ∩ {q : ℝ | a < T - q ^ 2} ∧ r < q :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear).and self_mem_nhdsWithin
  obtain ⟨r', hr', hlt⟩ := hevent.exists
  refine ⟨r', hlt, hr'.1.2, hr'.2, ?_⟩
  intro t x ht hx
  have h := hVW (show (r', (t, x)) ∈ V ×ˢ W from
    ⟨hr'.1.1, hW (mem_univ (t, x))⟩)
  rcases h with ((h | h) | ⟨⟨q, u, y⟩, hy, heq⟩)
  · exact False.elim ((not_lt_of_ge ht) h)
  · exact False.elim ((not_lt_of_ge hx) h)
  · have hq : q = r' := congrArg Prod.fst heq
    have hu : u = t := congrArg (fun z => z.2.1) heq
    have hyx : y.val = x := congrArg (fun z => z.2.2) heq
    subst q
    subst u
    exact ⟨y, hyx, hy⟩

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem continuous_curvature_on_closed_time_comp
    {M X : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [TopologicalSpace X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : Icc a b ⊆ D.carrier)
    (f : X → M) (hf : Continuous f) :
    Continuous (fun p : Icc a b × X =>
      normSq0S (S.base.metric p.1.val) (f p.2) 4 (S.base.rm04 p.1.val (f p.2))) := by
  have hmap : Continuous (fun p : Icc a b × X => (p.1.val, f p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (hf.comp continuous_snd)
  have hc := hS.continuousOn_rmNormSq
  have hmem : ∀ p : Icc a b × X, (p.1.val, f p.2) ∈ D.carrier ×ˢ (univ : Set M) :=
    fun p => ⟨hab p.1.property, mem_univ _⟩
  have hres := hc.comp_continuous hmap hmem
  simpa only [Function.comp_def] using hres

private theorem exists_trace_solution_on_closed_buffer_of_time_gt
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (hat : a < t)
    (ht : H.time (H.activeStage t) < t.val) :
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat.le
    let U := H.backwardSurvivorDomain first last hle
    ∃ S : SolutionOn (I := ThreeModel) (M := U)
        (RealTimeInterval.closed a.val t.val hat.le), IsSolutionOn S ∧
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
        (v : Icc a.val t.val), v.val ∈ H.stageDomain j →
        S.base.metric v.val = localPullMetric (H.stageMetric j v.val)
          (H.backwardSurvivorMap first last hle j hf hl)
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hf hl)) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (_hv : H.time i.succ ∈ Icc a.val t.val),
        S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
          (H.backwardSurvivorTerminalMap first last hle i hf hl)
          (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hl)) := by
  classical
  dsimp only
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat.le
  let U := H.backwardSurvivorDomain first last hle
  let G := (H.closedPrefixAt t ht).restrictIncoming le_rfl (H.closedPrefixAt t ht).lt le_rfl
  let L := (H.closedPrefixAt t ht).endpointTerminalLimitMetric (H.stageAt t)
  have hG (v : ℝ) : G.flow.base.metric v = H.stageMetric last v := H.closedPrefixAt_metric t ht v
  have hinit : G.flow.base.metric (H.time last) = H.initialMetric last := H.closedPrefixAt_initial t ht
  have hregular (x : U) : x ∈ H.backwardSurvivorIncomingDomain first last hle G := by
    change x.val ∈ G.terminalRegularRegion
    rw [(H.closedPrefixAt t ht).terminalRegularRegion_eq_univ]
    exact mem_univ _
  let Ψ : U → H.backwardSurvivorIncomingDomain first last hle G := fun x => ⟨x, hregular x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hregular ((Diffeomorph.refl ThreeModel U ∞).isLocalDiffeomorph x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2
  have hf (j : H.StageInterval first last) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2
  obtain ⟨gflow, hslabs, hlast, _, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  let S₀ : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) t.val
        ((H.time_strictMono.monotone hle).trans ht.le)) := { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t.val hat.le)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) le_rfl)
    (Ioo_subset_Ioo (H.activeStage_time_le a) le_rfl)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t.val)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    rcases lt_or_eq_of_le hv.2 with hvt | rfl
    · rw [H.metric_eq_stage_pullback_of_backwardSurvivorIncoming first last hle t.val G L gflow
        (fun i hi hl v hv => hslabs i hi hl v (Ico_subset_Icc_self hv))
        (fun v hv => hlast v (Ico_subset_Icc_self hv)) (fun v _ => hG v)
        j.val j.property.1 j.property.2 hjv hvt]
      exact localPullMetric_comp (H.stageMetric j.val v)
        (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) Ψ
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1 j.property.2)
          (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G))) hΨ (hf j)
    · have hj : j = ⟨last, hle, le_rfl⟩ :=
        Subtype.ext ((H.mem_stageDomain_iff t j.val).mp hjv).symm
      subst j
      rw [hlast _ ⟨ht.le, le_rfl⟩, ObservedHistory.backwardSurvivorIncomingMetric]
      have hend : L.extendedMetric t.val =
          (H.stageMetric last t.val).restrictOpen G.terminalRegularOpen :=
        H.closedPrefixAt_endpointTerminalLimitMetric_extendedMetric t ht le_rfl
      rw [hend, ← localPullMetric_subtype_val]
      let k := H.backwardSurvivorIncomingMap first last hle G
      have hk := H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G
      have hv := isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen
      have hc := isLocalDiffeomorph_comp hv (isLocalDiffeomorph_comp hk hΨ)
      rw [localPullMetric_comp _ k Ψ hk hΨ (isLocalDiffeomorph_comp hk hΨ),
        localPullMetric_comp _ Subtype.val (k ∘ Ψ) hv (isLocalDiffeomorph_comp hk hΨ) hc]
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [localPullMetric_inner, localPullMetric_inner]
      have hfend : f ⟨last, hle, le_rfl⟩ = Subtype.val ∘ (k ∘ Ψ) := by
        funext y
        exact H.backwardSurvivorMap_last first last hle (Ψ y).val
      exact congrArg (fun F : U → (H.stage last).Carrier =>
        (H.stageMetric last t.val).inner (F x)
          (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) hfend.symm
  refine ⟨S, hS, ?_, ?_⟩
  · intro j hj hl v hv
    exact hmetric ⟨j, hj, hl⟩ v.val v.property hv
  · intro i hi hl hv
    change localPullMetric (gflow (H.time i.succ)) Ψ hΨ = _
    rw [hslabs i hi hl _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩]
    have hd (x : U) : mfderiv ThreeModel ThreeModel Ψ x = ContinuousLinearMap.id ℝ ThreeSpace := by
      have h := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel) Ψ x
      change mfderiv ThreeModel ThreeModel id x = mfderiv ThreeModel ThreeModel Ψ x at h
      exact h.symm.trans (mfderiv_id (I := ThreeModel))
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner, hd]
    simp only [ObservedHistory.backwardSurvivorSlabMetric,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
    rfl

private theorem exists_trace_solution_on_closed_buffer_of_time_eq
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (hat : a < t)
    (ht : H.time (H.activeStage t) = t.val) :
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat.le
    let U := H.backwardSurvivorDomain first last hle
    ∃ S : SolutionOn (I := ThreeModel) (M := U)
        (RealTimeInterval.closed a.val t.val hat.le), IsSolutionOn S ∧
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
        (v : Icc a.val t.val), v.val ∈ H.stageDomain j →
        S.base.metric v.val = localPullMetric (H.stageMetric j v.val)
          (H.backwardSurvivorMap first last hle j hf hl)
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hf hl)) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (_hv : H.time i.succ ∈ Icc a.val t.val),
        S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
          (H.backwardSurvivorTerminalMap first last hle i hf hl)
          (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hl)) := by
  classical
  dsimp only
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat.le
  let U := H.backwardSurvivorDomain first last hle
  have hlt : first < last := lt_of_le_of_ne hle (by
    intro he
    have hleft := H.activeStage_time_le a
    change H.time first ≤ a.val at hleft
    rw [he, ht] at hleft
    exact (not_le_of_gt hat) hleft)
  obtain ⟨g, hg, hstage, _, hsol⟩ := H.exists_backwardSurvivor_isSolutionOn first last hlt
  let S₀ : SolutionOn (I := ThreeModel) (M := U)
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le) :=
    { base := { metric := g } }
  let S := S₀.timeRestrict (RealTimeInterval.closed a.val t.val hat.le)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict hsol
    (Icc_subset_Icc (H.activeStage_time_le a) ht.ge)
    (Ioo_subset_Ioo (H.activeStage_time_le a) ht.ge)
  refine ⟨S, hS, ?_, ?_⟩
  · intro j hf hl v hv
    change g v.val = _
    by_cases hj : j = last
    · have hvlast : v.val = H.time j := le_antisymm
        (v.property.2.trans (ht.ge.trans (by rw [hj]))) (H.time_le_of_mem_stageDomain hv)
      rw [hvlast, hstage j hf hl, ObservedHistory.backwardSurvivorInitialMetric, H.stageMetric_initial]
    · have hjlt : j < last := lt_of_le_of_ne hl hj
      cases j using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hjlt)
      | cast i =>
        have hil : i.succ ≤ last := hjlt
        have hv' : v.val ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
          simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hv
        rw [hg i hf hil v.val (Ico_subset_Icc_self hv'), ObservedHistory.backwardSurvivorSlabMetric,
          (H.event i).terminal.extendedMetric_before hv'.2, ← localPullMetric_subtype_val]
        have hm := H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hil
        have hval := isLocalDiffeomorph_subtype_val (I := ThreeModel) (H.event i).incoming.terminalRegularOpen
        rw [localPullMetric_comp _ _ _ hval hm (isLocalDiffeomorph_comp hval hm)]
        simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
        rfl
  · intro i hf hl hv
    change g (H.time i.succ) = _
    rw [hg i hf hl _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
      ObservedHistory.backwardSurvivorSlabMetric,
      OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]

private theorem exists_trace_solution_on_closed_buffer
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (hat : a < t) :
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat.le
    let U := H.backwardSurvivorDomain first last hle
    ∃ S : SolutionOn (I := ThreeModel) (M := U)
        (RealTimeInterval.closed a.val t.val hat.le), IsSolutionOn S ∧
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
        (v : Icc a.val t.val), v.val ∈ H.stageDomain j →
        S.base.metric v.val = localPullMetric (H.stageMetric j v.val)
          (H.backwardSurvivorMap first last hle j hf hl)
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hf hl)) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (_hv : H.time i.succ ∈ Icc a.val t.val),
        S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
          (H.backwardSurvivorTerminalMap first last hle i hf hl)
          (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hl)) := by
  rcases lt_or_eq_of_le (H.activeStage_time_le t) with ht | ht
  · exact exists_trace_solution_on_closed_buffer_of_time_gt H a t hat ht
  · exact exists_trace_solution_on_closed_buffer_of_time_eq H a t hat ht

private theorem exists_continuous_trace_curvature_on_closed_buffer
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (hat : a < t) :
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat.le
    let U := H.backwardSurvivorDomain first last hle
    ∃ F : Icc a.val t.val × U → ℝ, Continuous F ∧
      (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last)
        (v : Icc a.val t.val), v.val ∈ H.stageDomain j → ∀ (x : U),
        F (v, x) = normSq0S (H.stageMetric j v.val) (H.backwardSurvivorMap first last hle j hf hl x) 4
          (metricRm04At (H.stageMetric j v.val) (H.backwardSurvivorMap first last hle j hf hl x))) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (hv : H.time i.succ ∈ Icc a.val t.val) (x : U),
        F (⟨H.time i.succ, hv⟩, x) =
          normSq0S (H.event i).terminal.metric (H.backwardSurvivorTerminalMap first last hle i hf hl x) 4
            (metricRm04At (H.event i).terminal.metric
              (H.backwardSurvivorTerminalMap first last hle i hf hl x))) := by
  obtain ⟨S, hS, hmetric, hterminal⟩ := exists_trace_solution_on_closed_buffer H a t hat
  refine ⟨fun p => normSq0S (S.base.metric p.1.val) p.2 4 (S.base.rm04 p.1.val p.2), ?_, ?_, ?_⟩
  · exact continuous_curvature_on_closed_time_comp S hS (Subset.refl _) id continuous_id
  · intro j hf hl v hv x
    change normSq0S (S.base.metric v.val) x 4 (metricRm04At (S.base.metric v.val) x) = _
    rw [hmetric j hf hl v hv, normSq0S_metricRm04At_localPullMetric]
  · intro i hf hl hv x
    change normSq0S (S.base.metric (H.time i.succ)) x 4
      (metricRm04At (S.base.metric (H.time i.succ)) x) = _
    rw [hterminal i hf hl hv, normSq0S_metricRm04At_localPullMetric]

private theorem exists_larger_parabolicallyRmControlledBall_of_closed_trace_buffer
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (ha : a.val < t.val - r ^ 2) :
    let hat : a ≤ t := le_of_lt (ha.trans_le (sub_le_self t.val (sq_nonneg r)))
    (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p r,
      Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x)) →
    (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p r,
      ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), t.val - r ^ 2 ≤ v.val →
        r ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) < 1) →
    ∃ r' : ℝ, r < r' ∧ r' < R ∧ a.val < t.val - r' ^ 2 ∧
      H.isParabolicallyRmControlledBall t p r' := by
  classical
  dsimp only
  intro htrace hstrict
  have hat : a < t := ha.trans_le (sub_le_self t.val (sq_nonneg r))
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat.le
  let U := H.backwardSurvivorDomain first last hle
  obtain ⟨F, hF, hstage, hterminal⟩ := exists_continuous_trace_curvature_on_closed_buffer H a t hat
  obtain ⟨r', hrr', hr'R, ha', hnew⟩ := exists_radius_enlargement_of_compact_strict_bound
    (riemannianEDistOf (H.stageMetric last t.val) p)
    (Geometry.Riemannian.continuous_riemannianEDist _ p) U hrR ha F hF (by
      intro v x hv hx
      obtain ⟨A⟩ := htrace x hx
      let y : U := ⟨x, ⟨A⟩⟩
      let vH : Icc (0 : ℝ) H.horizon :=
        ⟨v.val, a.property.1.trans v.property.1, v.property.2.trans t.property.2⟩
      have hav : a ≤ vH := v.property.1
      have hvt : vH ≤ t := v.property.2
      refine ⟨y, rfl, ?_⟩
      rw [hstage (H.activeStage vH) (H.activeStage_mono hav) (H.activeStage_mono hvt) v
        (H.activeStage_mem vH) y,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage vH)
          (H.activeStage_mono hav) (H.activeStage_mono hvt) y A]
      exact hstrict x hx A vH hav hvt hv)
  have hr' : 0 < r' := hr.trans hrr'
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨t.val - r' ^ 2, a.property.1.trans ha'.le,
      (sub_le_self t.val (sq_nonneg r')).trans t.property.2⟩
  have hab : a ≤ b := ha'.le
  have hbt : b ≤ t := sub_le_self t.val (sq_nonneg r')
  refine ⟨r', hrr', hr'R, ha', hr', b, hbt, rfl, ?_⟩
  intro x hx
  have hxb : riemannianEDistOf (H.stageMetric last t.val) p x ≤ ENNReal.ofReal r' := hx.le
  obtain ⟨y, hy, _⟩ := hnew ⟨t.val, hat.le, le_rfl⟩ x (sub_le_self t.val (sq_nonneg r')) hxb
  subst x
  let A : BackwardPointTrace H first last hle y.val := Classical.choice y.property
  let A' := A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)
  refine ⟨A', ?_, ?_⟩
  · intro v hbv hvt
    have hav : a ≤ v := hab.trans hbv
    let v' : Icc a.val t.val := ⟨v.val, hav, hvt⟩
    obtain ⟨z, hz, hbound⟩ := hnew v' y.val hbv hxb
    have hzy : z = y := Subtype.ext hz
    subst z
    rw [hstage (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) v'
      (H.activeStage_mem v) y,
      H.backwardSurvivorMap_eq_point first last hle (H.activeStage v)
        (H.activeStage_mono hav) (H.activeStage_mono hvt) y A] at hbound
    exact hbound.le
  · intro i hf hl
    have hiv : H.time i.succ ∈ Ioc b.val t.val := (H.crossed_event_iff_mem_Ioc b t i).mp ⟨hf, hl⟩
    have hiat : H.time i.succ ∈ Icc a.val t.val := ⟨(show a.val ≤ b.val from hab).trans hiv.1.le, hiv.2⟩
    obtain ⟨z, hz, hbound⟩ := hnew ⟨H.time i.succ, hiat⟩ y.val hiv.1.le hxb
    have hzy : z = y := Subtype.ext hz
    subst z
    rw [hterminal i ((H.activeStage_mono hab).trans hf) hl hiat y] at hbound
    have hpoint := H.backwardSurvivorMap_eq_point first last hle i.castSucc
      ((H.activeStage_mono hab).trans hf) (i.castSucc_lt_succ.le.trans hl) y A
    have hterminalPoint : H.backwardSurvivorTerminalMap first last hle i
        ((H.activeStage_mono hab).trans hf) hl y =
        (⟨A'.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
          (A'.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩ :
            (H.event i).incoming.terminalRegularOpen) := Subtype.ext hpoint
    rw [hterminalPoint] at hbound
    exact hbound.le


private theorem closedBall_subset_closure_ball_of_stage
    (P : OrientedThreeStage) (g : P.Metric) (p : P.Carrier) {r : ℝ} (hr : 0 < r) :
    riemannianClosedBallOf g p r ⊆ closure (riemannianBallOf g p r) := by
  intro x hx
  by_cases hxr : x ∈ riemannianBallOf g p r
  · exact subset_closure hxr
  have he : riemannianEDistOf g p x = ENNReal.ofReal r := le_antisymm hx (le_of_not_gt hxr)
  have hR : riemannianEDistOf g p x < ENNReal.ofReal (r + 1) := by
    rw [he]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
  obtain ⟨γ, hzero, hend, hγ, hd⟩ :=
    Geometry.Riemannian.exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall
      g p x hR (Geometry.Metric.isClosed_riemannianClosedBallOf g p (r + 1)).isCompact
  have hdist : (riemannianEDistOf g p x).toReal = r := by rw [he, ENNReal.toReal_ofReal hr.le]
  rw [hdist] at hend hγ hd
  have hc : ContinuousWithinAt γ (Ico 0 r) r :=
    (hγ.continuousOn r ⟨hr.le, le_rfl⟩).mono Ico_subset_Icc_self
  rw [← hend]
  apply hc.mem_closure (by rw [closure_Ico hr.ne]; exact ⟨hr.le, le_rfl⟩)
  intro s hs
  change riemannianEDistOf g p (γ s) < ENNReal.ofReal r
  rw [← hzero, hd 0 ⟨le_rfl, hr.le⟩ s ⟨hs.1, hs.2.le⟩]
  simpa only [zero_sub, abs_neg, abs_of_nonneg hs.1] using
    (ENNReal.ofReal_lt_ofReal_iff hr).mpr hs.2

private theorem curvature_le_on_closed_trace_buffer
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {σ : ℝ} (hσ : 0 < σ) (ha : a.val < t.val - σ ^ 2)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) :
    let hat : a ≤ t := le_of_lt (ha.trans_le (sub_le_self t.val (sq_nonneg σ)))
    ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), t.val - σ ^ 2 ≤ v.val →
        σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) ≤ 1 := by
  classical
  dsimp only
  have hat : a < t := ha.trans_le (sub_le_self t.val (sq_nonneg σ))
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat.le
  let U := H.backwardSurvivorDomain first last hle
  obtain ⟨F, hF, hstage, _⟩ := exists_continuous_trace_curvature_on_closed_buffer H a t hat
  have hopen (v : Icc a.val t.val) (hv : t.val - σ ^ 2 < v.val)
      (x : U) (hx : x.val ∈ riemannianBallOf (H.stageMetric last t.val) p σ) :
      σ ^ 4 * F (v, x) ≤ 1 := by
    let vH : Icc (0 : ℝ) H.horizon :=
      ⟨v.val, a.property.1.trans v.property.1, v.property.2.trans t.property.2⟩
    have hav : a ≤ vH := v.property.1
    have hvt : vH ≤ t := v.property.2
    have hc : ContinuousAt (fun q : ℝ => q ^ 4 * F (v, x)) σ := by fun_prop
    apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] σ ≤ 𝓝 σ))
    have hnear : ∀ᶠ q : ℝ in 𝓝 σ,
        0 < q ∧ riemannianEDistOf (H.stageMetric last t.val) p x.val < ENNReal.ofReal q ∧
          t.val - q ^ 2 < v.val := by
      refine (eventually_gt_nhds hσ).and
        ((ENNReal.continuous_ofReal.continuousAt.eventually_const_lt hx).and ?_)
      exact (show ContinuousAt (fun q : ℝ => t.val - q ^ 2) σ by fun_prop).eventually_lt_const hv
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqσ
    obtain ⟨_, b, hbt, hb, htrace⟩ := hsmall q hq.1 hqσ
    obtain ⟨B, hB⟩ := htrace x.val hq.2.1
    have hab : a ≤ b := by
      change a.val ≤ b.val
      rw [hb]
      have hsq : q ^ 2 < σ ^ 2 := (sq_lt_sq₀ hq.1.le hσ.le).mpr hqσ
      linarith
    have hbv : b ≤ vH := by change b.val ≤ v.val; rw [hb]; exact hq.2.2.le
    let A : BackwardPointTrace H first last hle x.val := Classical.choice x.property
    have he : A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt) = B :=
      Subsingleton.elim _ _
    have hp : A.point (H.activeStage vH) (H.activeStage_mono hav) (H.activeStage_mono hvt) =
        B.point (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt) :=
      congrArg (fun Z => Z.point (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) he
    rw [hstage (H.activeStage vH) (H.activeStage_mono hav) (H.activeStage_mono hvt) v
      (H.activeStage_mem vH) x,
      H.backwardSurvivorMap_eq_point first last hle (H.activeStage vH)
        (H.activeStage_mono hav) (H.activeStage_mono hvt) x A, hp]
    exact hB.1 vH hbv hvt
  have hspace (v : Icc a.val t.val) (hv : t.val - σ ^ 2 < v.val)
      (x : U) (hx : x.val ∈ riemannianClosedBallOf (H.stageMetric last t.val) p σ) :
      σ ^ 4 * F (v, x) ≤ 1 := by
    have hcl : x ∈ closure {y : U | y.val ∈ riemannianBallOf (H.stageMetric last t.val) p σ} :=
      U.isOpenEmbedding'.isOpenMap.preimage_closure_subset_closure_preimage
        (closedBall_subset_closure_ball_of_stage (H.stage last) (H.stageMetric last t.val) p hσ hx)
    apply le_on_closure (fun y hy => hopen v hv y hy) _ continuousOn_const hcl
    exact (continuous_const.mul (hF.comp (continuous_const.prodMk continuous_id))).continuousOn
  have hclosed (v : Icc a.val t.val) (hv : t.val - σ ^ 2 ≤ v.val)
      (x : U) (hx : x.val ∈ riemannianClosedBallOf (H.stageMetric last t.val) p σ) :
      σ ^ 4 * F (v, x) ≤ 1 := by
    let V : Set (Icc a.val t.val) := {u | t.val - σ ^ 2 < u.val}
    have himage : (Subtype.val : Icc a.val t.val → ℝ) '' V = Ioc (t.val - σ ^ 2) t.val := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.property.2⟩
      · intro hu
        exact ⟨⟨u, (ha.trans hu.1).le, hu.2⟩, hu.1, rfl⟩
    have hcl : v ∈ closure V := by
      rw [closure_subtype, himage, closure_Ioc (by nlinarith [sq_pos_of_pos hσ])]
      exact ⟨hv, v.property.2⟩
    apply le_on_closure (fun u hu => hspace u hu x hx) _ continuousOn_const hcl
    exact (continuous_const.mul (hF.comp (continuous_id.prodMk continuous_const))).continuousOn
  intro x hx A v hav hvt hv
  let y : U := ⟨x, ⟨A⟩⟩
  let v' : Icc a.val t.val := ⟨v.val, hav, hvt⟩
  have h := hclosed v' hv y hx
  rw [hstage (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) v'
    (H.activeStage_mem v) y,
    H.backwardSurvivorMap_eq_point first last hle (H.activeStage v)
      (H.activeStage_mono hav) (H.activeStage_mono hvt) y A] at h
  exact h

private theorem exists_larger_controlled_radius_or_actual_curvature_eq
    (H : ObservedHistory) (a t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {σ R : ℝ} (hσ : 0 < σ) (hσR : σ < R) (ha : a.val < t.val - σ ^ 2)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) :
    let hat : a ≤ t := le_of_lt (ha.trans_le (sub_le_self t.val (sq_nonneg σ)))
    (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) x)) →
    (∃ r' : ℝ, σ < r' ∧ r' < R ∧ a.val < t.val - r' ^ 2 ∧
      H.isParabolicallyRmControlledBall t p r') ∨
    ∃ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∃ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), t.val - σ ^ 2 ≤ v.val ∧
        σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) = 1 := by
  classical
  dsimp only
  intro htrace
  have hat : a ≤ t := le_of_lt (ha.trans_le (sub_le_self t.val (sq_nonneg σ)))
  by_cases hstrict : ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) x,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), t.val - σ ^ 2 ≤ v.val →
        σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
          (metricRm04At (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) < 1
  · exact Or.inl (exists_larger_parabolicallyRmControlledBall_of_closed_trace_buffer
      H a t p hσ hσR ha htrace hstrict)
  · push Not at hstrict
    obtain ⟨x, hx, A, v, hav, hvt, hv, hge⟩ := hstrict
    exact Or.inr ⟨x, hx, A, v, hav, hvt, hv,
      le_antisymm (curvature_le_on_closed_trace_buffer H a t p hσ ha hsmall x hx A v hav hvt hv) hge⟩



private theorem exists_before_with_no_event_between
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon)
    {τ : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t.val) :
    ∃ a : Icc (0 : ℝ) H.horizon, a.val < τ ∧
      ∀ i : Fin H.eventCount, a.val < H.time i.succ → τ ≤ H.time i.succ := by
  have hnear : ∀ᶠ u : ℝ in 𝓝 τ,
      ∀ i : Fin H.eventCount, H.time i.succ < τ → H.time i.succ < u := by
    apply eventually_all.mpr
    intro i
    by_cases hi : H.time i.succ < τ
    · exact (eventually_gt_nhds hi).mono (fun u hu _ => hu)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hevent : ∀ᶠ u : ℝ in 𝓝[<] τ,
      (∀ i : Fin H.eventCount, H.time i.succ < τ → H.time i.succ < u) ∧
        0 < u ∧ u < τ :=
    (hnear.filter_mono nhdsWithin_le_nhds).and
      ((eventually_gt_nhds hτ).filter_mono nhdsWithin_le_nhds |>.and self_mem_nhdsWithin)
  obtain ⟨u, hu, hupos, huτ⟩ := hevent.exists
  refine ⟨⟨u, hupos.le, huτ.le.trans (hτt.trans t.property.2)⟩, huτ, ?_⟩
  intro i hi
  by_contra h
  exact (not_lt_of_ge (hu i (lt_of_not_ge h)).le) hi

private theorem exists_failed_crossing_cap
    (H : ObservedHistory) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (x : (H.stage last).Carrier)
    (hOld : ∀ i : Fin H.eventCount, first ≤ i.castSucc → i.succ ≤ last →
      (H.event i).old = (H.event i).transition.trace.retainedCore)
    (hnot : ¬ Nonempty (BackwardPointTrace H first last hle x)) :
    ∃ (i : Fin H.eventCount) (_ : first ≤ i.castSucc) (hl : i.succ ≤ last)
      (A : BackwardPointTrace H i.succ last hl x)
      (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      (¬ ∃ y, (H.event i).RegularCrossing y (A.point i.succ le_rfl hl)) ∧
      (H.event i).transition.trace.presentation
        ((H.event i).transition.trace.capping.cap b.val z) =
          Sum.inl (A.point i.succ le_rfl hl) := by
  induction first using Fin.reverseInduction with
  | last =>
    have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
    subst last
    exact (hnot ⟨BackwardPointTrace.singleton H _ x⟩).elim
  | cast j ih =>
    by_cases he : j.castSucc = last
    · subst last
      exact (hnot ⟨BackwardPointTrace.singleton H _ x⟩).elim
    have hl : j.succ ≤ last := by
      have hlt : j.castSucc < last := lt_of_le_of_ne hle he
      exact Nat.succ_le_iff.mpr hlt
    by_cases hn : Nonempty (BackwardPointTrace H j.succ last hl x)
    · obtain ⟨A⟩ := hn
      have hfail : ¬ ∃ y, (H.event j).RegularCrossing y (A.point j.succ le_rfl hl) := by
        rintro ⟨y, hy⟩
        exact hnot ⟨A.prepend y hy⟩
      rcases (H.event j).exists_regularCrossing_or_cap (hOld j le_rfl hl)
          (A.point j.succ le_rfl hl) with hcross | ⟨b, z, hz⟩
      · obtain ⟨y, hy⟩ := hcross
        exact (hfail ⟨y.val, hy⟩).elim
      · exact ⟨j, le_rfl, hl, A, b, z, hfail, hz⟩
    · obtain ⟨i, hf, hi, A, b, z, hfail, hz⟩ := ih hl
        (fun i hf hi => hOld i (j.castSucc_lt_succ.le.trans hf) hi) hn
      exact ⟨i, j.castSucc_lt_succ.le.trans hf, hi, A, b, z, hfail, hz⟩

private theorem failed_crossing_on_radius_boundary
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    {σ : ℝ} (hσ : 0 < σ)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (hx : x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ)
    (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
    (A : BackwardPointTrace H i.succ (H.activeStage t) hl x)
    (hi : t.val - σ ^ 2 ≤ H.time i.succ)
    (hfail : ¬ ∃ y, (H.event i).RegularCrossing y (A.point i.succ le_rfl hl)) :
    H.time i.succ = t.val - σ ^ 2 ∨
      riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x = ENNReal.ofReal σ := by
  by_contra hn
  push Not at hn
  have htime : t.val - σ ^ 2 < H.time i.succ := lt_of_le_of_ne hi (Ne.symm hn.1)
  have hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x <
      ENNReal.ofReal σ := lt_of_le_of_ne hx hn.2
  have hqnear : ∀ᶠ q : ℝ in 𝓝 σ,
      0 < q ∧ riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x < ENNReal.ofReal q ∧
        t.val - q ^ 2 < H.time i.succ := by
    refine (eventually_gt_nhds hσ).and ((ENNReal.continuous_ofReal.continuousAt.eventually_const_lt hdist).and ?_)
    exact (show ContinuousAt (fun q : ℝ => t.val - q ^ 2) σ by fun_prop).eventually_lt_const htime
  obtain ⟨q, ⟨hq, hxq, htq⟩, hqσ⟩ :=
    ((hqnear.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ q : ℝ in 𝓝[<] σ, q < σ)).exists
  obtain ⟨_, a, hat, ha, htraces⟩ := hsmall q hq hqσ
  obtain ⟨B, _⟩ := htraces x hxq
  have hbi : H.activeStage a ≤ i.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    have hlt : H.activeStage a < i.succ := H.time_strictMono.lt_iff_lt.mp
      ((H.activeStage_time_le a).trans_lt (ha.symm ▸ htq))
    change (H.activeStage a).val ≤ i.val
    exact Nat.le_of_lt_succ hlt
  let C := B.restrictFirst (hbi.trans i.castSucc_lt_succ.le) hl
  have hCA : C = A := Subsingleton.elim _ _
  have hp : B.point i.succ (hbi.trans i.castSucc_lt_succ.le) hl =
      A.point i.succ le_rfl hl := congrArg (fun Z => Z.point i.succ le_rfl hl) hCA
  apply hfail
  refine ⟨B.point i.castSucc hbi (i.castSucc_lt_succ.le.trans hl), ?_⟩
  rw [← hp]
  exact B.crossing i hbi hl

private theorem exists_closed_trace_buffer_or_radius_boundary_cap
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {σ : ℝ} (hσ : 0 < σ) (hτ : 0 < t.val - σ ^ 2)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (hOld : ∀ i : Fin H.eventCount, t.val - σ ^ 2 ≤ H.time i.succ →
      H.time i.succ ≤ t.val → (H.event i).old = (H.event i).transition.trace.retainedCore) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val < t.val - σ ^ 2 ∧
      ((∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x)) ∨
       ∃ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
        ∃ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
          (A : BackwardPointTrace H i.succ (H.activeStage t) hl x)
          (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
          t.val - σ ^ 2 ≤ H.time i.succ ∧ H.time i.succ ≤ t.val ∧
          (¬ ∃ y, (H.event i).RegularCrossing y (A.point i.succ le_rfl hl)) ∧
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.cap b.val z) =
              Sum.inl (A.point i.succ le_rfl hl) ∧
          (H.time i.succ = t.val - σ ^ 2 ∨
            riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x = ENNReal.ofReal σ)) := by
  classical
  obtain ⟨a, ha, hevents⟩ := exists_before_with_no_event_between H t hτ
    (sub_le_self _ (sq_nonneg σ))
  have hat : a ≤ t := ha.le.trans (sub_le_self _ (sq_nonneg σ))
  refine ⟨a, hat, ha, ?_⟩
  by_cases hall : ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) x)
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x, hx, hn⟩ := hall
    have hnot : ¬ Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) x) := not_nonempty_iff.mpr hn
    have hevent (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t) :
        t.val - σ ^ 2 ≤ H.time i.succ ∧ H.time i.succ ≤ t.val := by
      have hi := (H.crossed_event_iff_mem_Ioc a t i).mp ⟨hf, hl⟩
      exact ⟨hevents i hi.1, hi.2⟩
    obtain ⟨i, hf, hl, A, b, z, hfail, hcap⟩ := exists_failed_crossing_cap H
      (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x
      (fun i hf hl => hOld i (hevent i hf hl).1 (hevent i hf hl).2) hnot
    refine Or.inr ⟨x, hx, i, hl, A, b, z,
      (hevent i hf hl).1, (hevent i hf hl).2, hfail, hcap, ?_⟩
    exact failed_crossing_on_radius_boundary H t p x hσ hsmall hx i hl A (hevent i hf hl).1 hfail


theorem ObservedHistory.csSup_parabolicallyRmControlledBall_eq_or_cap_or_curvature_eq
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {q₀ R : ℝ} (hq₀ : H.isParabolicallyRmControlledBall t p q₀) (hqR : q₀ ≤ R)
    (hRt : R ^ 2 ≤ t.val)
    (hOld : ∀ i : Fin H.eventCount, t.val - R ^ 2 < H.time i.succ →
      H.time i.succ ≤ t.val → (H.event i).old = (H.event i).transition.trace.retainedCore) :
    let σ := sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}
    σ ∈ Icc q₀ R ∧
      (σ = R ∨
       (∃ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
        ∃ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
          (A : BackwardPointTrace H i.succ (H.activeStage t) hl x)
          (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
          t.val - σ ^ 2 ≤ H.time i.succ ∧ H.time i.succ ≤ t.val ∧
          (¬ ∃ y, (H.event i).RegularCrossing y (A.point i.succ le_rfl hl)) ∧
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.cap b.val z) =
              Sum.inl (A.point i.succ le_rfl hl) ∧
          (H.time i.succ = t.val - σ ^ 2 ∨
            riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x = ENNReal.ofReal σ)) ∨
       ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val < t.val - σ ^ 2 ∧
        (∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
          Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x)) ∧
        ∃ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
          ∃ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x)
            (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), t.val - σ ^ 2 ≤ v.val ∧
            σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
              (metricRm04At (H.stageMetric (H.activeStage v) v.val)
                (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) = 1) := by
  classical
  dsimp only
  let σ := sSup {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r}
  have hσrange : σ ∈ Icc q₀ R := H.csSup_parabolicallyRmControlledBall_mem_Icc hq₀ hqR
  refine ⟨hσrange, ?_⟩
  by_cases he : σ = R
  · exact Or.inl he
  have hσR : σ < R := lt_of_le_of_ne hσrange.2 he
  have hσ : 0 < σ := hq₀.1.trans_le hσrange.1
  have hR : 0 < R := hq₀.1.trans_le hqR
  have hsq : σ ^ 2 < R ^ 2 := (sq_lt_sq₀ hσ.le hR.le).mpr hσR
  have hτ : 0 < t.val - σ ^ 2 := by linarith
  have hsmall (q : ℝ) (hq : 0 < q) (hqσ : q < σ) :
      H.isParabolicallyRmControlledBall t p q :=
    H.isParabolicallyRmControlledBall_of_lt_csSup hq₀ hqR hq hqσ
  obtain ⟨a, hat, ha, htrace | hcap⟩ := exists_closed_trace_buffer_or_radius_boundary_cap
    H t p hσ hτ hsmall (fun i hi hit => hOld i ((sub_lt_sub_left hsq t.val).trans_le hi) hit)
  · rcases exists_larger_controlled_radius_or_actual_curvature_eq
        H a t p hσ hσR ha hsmall htrace with hlarger | heq
    · obtain ⟨r', hσr', hr'R, _, hr'⟩ := hlarger
      have hbdd : BddAbove {r ∈ Icc q₀ R | H.isParabolicallyRmControlledBall t p r} :=
        ⟨R, fun r hr => hr.1.2⟩
      have hr'σ : r' ≤ σ := le_csSup hbdd
        ⟨⟨hσrange.1.trans hσr'.le, hr'R.le⟩, hr'⟩
      exact (not_lt_of_ge hr'σ hσr').elim
    · exact Or.inr (Or.inr ⟨a, hat, ha, htrace, heq⟩)
  · exact Or.inr (Or.inl hcap)

private theorem eventually_square_clock_before_later_stages
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (k : Fin (H.eventCount + 1))
    {σ : ℝ} (hb : t.val - σ ^ 2 ≤ H.time k) :
    ∀ᶠ q : ℝ in 𝓝 σ, ∀ j : Fin (H.eventCount + 1), k < j → t.val - q ^ 2 < H.time j := by
  apply eventually_all.mpr
  intro j
  by_cases hkj : k < j
  · have hstrict := hb.trans_lt (H.time_strictMono hkj)
    exact ((show ContinuousAt (fun q : ℝ => t.val - q ^ 2) σ by fun_prop).eventually_lt_const hstrict).mono
      (fun _ h _ => h)
  · exact Filter.Eventually.of_forall (fun _ h => (hkj h).elim)

private theorem open_ball_survives_to_birth_with_curvature_control
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (k : Fin (H.eventCount + 1)) {σ : ℝ} (hσ : 0 < σ)
    (hbirth : t.val - σ ^ 2 ≤ H.time k) (hkt : H.time k ≤ t.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) :
    let b := H.stageTime k
    let hbt : b ≤ t := hkt
    riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) ∧
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x,
        A.isRmControlled (hat := hbt) σ := by
  classical
  dsimp only
  let b := H.stageTime k
  have hbt : b ≤ t := hkt
  have hbk : H.activeStage b = k := H.activeStage_stageTime k
  have hclock := eventually_square_clock_before_later_stages H t k hbirth
  have hfirst (q : ℝ) (hqclock : ∀ j : Fin (H.eventCount + 1), k < j → t.val - q ^ 2 < H.time j)
      (a : Icc (0 : ℝ) H.horizon) (ha : a.val = t.val - q ^ 2) : H.activeStage a ≤ H.activeStage b := by
    rw [hbk]
    by_contra hn
    have hh := hqclock (H.activeStage a) (lt_of_not_ge hn)
    exact (not_lt_of_ge (H.activeStage_time_le a)) (ha.symm ▸ hh)
  have hnear (x : (H.stageAt t).Carrier)
      (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ) :
      ∀ᶠ q : ℝ in 𝓝 σ,
        0 < q ∧ riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x < ENNReal.ofReal q ∧
          ∀ j : Fin (H.eventCount + 1), k < j → t.val - q ^ 2 < H.time j :=
    (eventually_gt_nhds hσ).and
      ((ENNReal.continuous_ofReal.continuousAt.eventually_const_lt hx).and hclock)
  have hsurvive : riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) := by
    intro x hx
    obtain ⟨q, hq, hqσ⟩ := (((hnear x hx).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ q : ℝ in 𝓝[<] σ, q < σ)).exists
    obtain ⟨_, a, hat, ha, htrace⟩ := hsmall q hq.1 hqσ
    obtain ⟨A, _⟩ := htrace x hq.2.1
    exact ⟨A.restrictFirst (hfirst q hq.2.2 a ha) (H.activeStage_mono hbt)⟩
  refine ⟨hsurvive, ?_⟩
  intro x hx A
  rcases lt_or_eq_of_le hbt with hbt' | heq
  · let first := H.activeStage b
    let last := H.activeStage t
    have hle : first ≤ last := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    obtain ⟨F, hF, hstage, hterminal⟩ := exists_continuous_trace_curvature_on_closed_buffer H b t hbt'
    let y : U := ⟨x, ⟨A⟩⟩
    have hopen (v : Icc b.val t.val) (hv : b.val < v.val) : σ ^ 4 * F (v, y) ≤ 1 := by
      let vH : Icc (0 : ℝ) H.horizon :=
        ⟨v.val, b.property.1.trans v.property.1, v.property.2.trans t.property.2⟩
      have hbv : b ≤ vH := v.property.1
      have hvt : vH ≤ t := v.property.2
      have hτv : t.val - σ ^ 2 < v.val := hbirth.trans_lt hv
      have hc : ContinuousAt (fun q : ℝ => q ^ 4 * F (v, y)) σ := by fun_prop
      apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] σ ≤ 𝓝 σ))
      have htime : ∀ᶠ q : ℝ in 𝓝 σ, t.val - q ^ 2 < v.val :=
        (show ContinuousAt (fun q : ℝ => t.val - q ^ 2) σ by fun_prop).eventually_lt_const hτv
      filter_upwards [(hnear x hx).filter_mono nhdsWithin_le_nhds,
        htime.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqv hqσ
      obtain ⟨_, a, hat, ha, htrace⟩ := hsmall q hq.1 hqσ
      obtain ⟨B, hB⟩ := htrace x hq.2.1
      have hab := hfirst q hq.2.2 a ha
      have hav : a ≤ vH := by change a.val ≤ v.val; rw [ha]; exact hqv.le
      have he : B.restrictFirst hab (H.activeStage_mono hbt) = A := Subsingleton.elim _ _
      have hp : B.point (H.activeStage vH) (H.activeStage_mono hav) (H.activeStage_mono hvt) =
          A.point (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt) :=
        congrArg (fun Z => Z.point (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) he
      rw [hstage (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt) v
        (H.activeStage_mem vH) y,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage vH)
          (H.activeStage_mono hbv) (H.activeStage_mono hvt) y A, ← hp]
      exact hB.1 vH hav hvt
    have hclosed (v : Icc b.val t.val) : σ ^ 4 * F (v, y) ≤ 1 := by
      let V : Set (Icc b.val t.val) := {u | b.val < u.val}
      have himage : (Subtype.val : Icc b.val t.val → ℝ) '' V = Ioc b.val t.val := by
        ext u
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨hz, z.property.2⟩
        · intro hu
          exact ⟨⟨u, hu.1.le, hu.2⟩, hu.1, rfl⟩
      have hcl : v ∈ closure V := by
        rw [closure_subtype, himage, closure_Ioc (ne_of_lt (show b.val < t.val from hbt'))]
        exact v.property
      apply le_on_closure (fun u hu => hopen u hu) _ continuousOn_const hcl
      exact (continuous_const.mul (hF.comp (continuous_id.prodMk continuous_const))).continuousOn
    constructor
    · intro v hbv hvt
      have h := hclosed ⟨v.val, hbv, hvt⟩
      rw [hstage (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt) _
        (H.activeStage_mem v) y,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage v)
          (H.activeStage_mono hbv) (H.activeStage_mono hvt) y A] at h
      exact h
    · intro i hf hl
      have hiv : H.time i.succ ∈ Ioc b.val t.val := (H.crossed_event_iff_mem_Ioc b t i).mp ⟨hf, hl⟩
      have h := hclosed ⟨H.time i.succ, hiv.1.le, hiv.2⟩
      rw [hterminal i hf hl ⟨hiv.1.le, hiv.2⟩ y] at h
      have hp := H.backwardSurvivorMap_eq_point first last hle i.castSucc hf
        (i.castSucc_lt_succ.le.trans hl) y A
      have he : H.backwardSurvivorTerminalMap first last hle i hf hl y =
          (⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
            (A.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩ :
              (H.event i).incoming.terminalRegularOpen) := Subtype.ext hp
      rw [he] at h
      exact h
  · subst t
    constructor
    · intro v hbv hvb
      have hv : v = b := le_antisymm hvb hbv
      subst v
      rw [A.endpoint_eq]
      have hc : ContinuousAt (fun q : ℝ => q ^ 4 *
          normSq0S (H.stageMetric (H.activeStage b) b.val) x 4
            (metricRm04At (H.stageMetric (H.activeStage b) b.val) x)) σ := by fun_prop
      apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] σ ≤ 𝓝 σ))
      filter_upwards [(hnear x hx).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with q hq hqσ
      exact (hsmall q hq.1 hqσ).terminal_curvature_bound H x hq.2.1
    · intro i hf hl
      exact ((not_le_of_gt i.castSucc_lt_succ) (hl.trans hf)).elim

theorem ObservedHistory.ball_subset_backwardSurvivorDomain_and_closed_trace_isRmControlled
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (k : Fin (H.eventCount + 1)) {σ : ℝ} (hσ : 0 < σ)
    (hbirth : t.val - σ ^ 2 ≤ H.time k) (hkt : H.time k ≤ t.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) :
    let b := H.stageTime k
    let hbt : b ≤ t := hkt
    riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) ∧
    ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x,
        A.isRmControlled (hat := hbt) σ := by
  classical
  dsimp only
  let b := H.stageTime k
  have hbt : b ≤ t := hkt
  obtain ⟨hsurvive, hopen⟩ :=
    open_ball_survives_to_birth_with_curvature_control H t p k hσ hbirth hkt hsmall
  refine ⟨hsurvive, ?_⟩
  intro x hx A
  rcases lt_or_eq_of_le hbt with hbt' | heq
  · let first := H.activeStage b
    let last := H.activeStage t
    have hle : first ≤ last := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    obtain ⟨F, hF, hstage, hterminal⟩ := exists_continuous_trace_curvature_on_closed_buffer H b t hbt'
    let y : U := ⟨x, ⟨A⟩⟩
    have hcl : y ∈ closure {z : U | z.val ∈ riemannianBallOf (H.stageMetric last t.val) p σ} :=
      U.isOpenEmbedding'.isOpenMap.preimage_closure_subset_closure_preimage
        (closedBall_subset_closure_ball_of_stage (H.stage last) (H.stageMetric last t.val) p hσ hx)
    have hbound (v : Icc b.val t.val) : σ ^ 4 * F (v, y) ≤ 1 := by
      refine le_on_closure (f := fun z : U => σ ^ 4 * F (v, z)) (g := fun _ => (1 : ℝ))
        ?_ ?_ continuousOn_const hcl
      · intro z hz
        let B : BackwardPointTrace H first last hle z.val := Classical.choice z.property
        let vH : Icc (0 : ℝ) H.horizon :=
          ⟨v.val, b.property.1.trans v.property.1, v.property.2.trans t.property.2⟩
        have hbv : b ≤ vH := v.property.1
        have hvt : vH ≤ t := v.property.2
        rw [hstage (H.activeStage vH) (H.activeStage_mono hbv) (H.activeStage_mono hvt) v
          (H.activeStage_mem vH) z,
          H.backwardSurvivorMap_eq_point first last hle (H.activeStage vH)
            (H.activeStage_mono hbv) (H.activeStage_mono hvt) z B]
        exact (hopen z.val hz B).1 vH hbv hvt
      · exact (continuous_const.mul (hF.comp (continuous_const.prodMk continuous_id))).continuousOn
    constructor
    · intro v hbv hvt
      have h := hbound ⟨v.val, hbv, hvt⟩
      rw [hstage (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt) _
        (H.activeStage_mem v) y,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage v)
          (H.activeStage_mono hbv) (H.activeStage_mono hvt) y A] at h
      exact h
    · intro i hf hl
      have hiv : H.time i.succ ∈ Ioc b.val t.val := (H.crossed_event_iff_mem_Ioc b t i).mp ⟨hf, hl⟩
      have h := hbound ⟨H.time i.succ, hiv.1.le, hiv.2⟩
      rw [hterminal i hf hl ⟨hiv.1.le, hiv.2⟩ y] at h
      have hp := H.backwardSurvivorMap_eq_point first last hle i.castSucc hf
        (i.castSucc_lt_succ.le.trans hl) y A
      have he : H.backwardSurvivorTerminalMap first last hle i hf hl y =
          (⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
            (A.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩ :
              (H.event i).incoming.terminalRegularOpen) := Subtype.ext hp
      rw [he] at h
      exact h
  · subst t
    constructor
    · intro v hbv hvb
      have hv : v = b := le_antisymm hvb hbv
      subst v
      rw [A.endpoint_eq]
      have hcl := closedBall_subset_closure_ball_of_stage (H.stageAt b)
        (H.stageMetric (H.activeStage b) b.val) p hσ hx
      refine le_on_closure (f := fun z => σ ^ 4 * normSq0S
        (H.stageMetric (H.activeStage b) b.val) z 4
        (metricRm04At (H.stageMetric (H.activeStage b) b.val) z))
        (g := fun _ => (1 : ℝ)) ?_ ?_ continuousOn_const hcl
      · intro z hz
        let B := BackwardPointTrace.singleton H (H.activeStage b) z
        have h := (hopen z hz B).1 b le_rfl le_rfl
        rw [B.endpoint_eq] at h
        exact h
      · exact (continuous_const.mul
          (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth
            (H.stageMetric (H.activeStage b) b.val)
            (metricRm04 (H.stageMetric (H.activeStage b) b.val))).continuous).continuousOn
    · intro i hf hl
      exact ((not_le_of_gt i.castSucc_lt_succ) (hl.trans hf)).elim

private theorem earlier_survival_and_curvature_of_closed_trace_buffer
    (H : ObservedHistory) (a b t : Icc (0 : ℝ) H.horizon)
    (hab : a ≤ b) (hbt : b ≤ t) (p : (H.stageAt t).Carrier)
    {σ : ℝ} (hσ : 0 < σ) (ha : a.val < t.val - σ ^ 2)
    (hb : t.val - σ ^ 2 ≤ b.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (htrace : ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono (hab.trans hbt)) x)) :
    riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) ∧
    ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v.val)
              (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt))) ≤ 1 := by
  constructor
  · intro x hx
    obtain ⟨A⟩ := htrace x (show riemannianEDistOf (H.stageMetric (H.activeStage t) t.val) p x ≤ ENNReal.ofReal σ from hx.le)
    exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)⟩
  · intro x hx A v hbv hvt
    obtain ⟨B⟩ := htrace x hx
    have he : B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt) = A :=
      Subsingleton.elim _ _
    have hp : B.point (H.activeStage v) (H.activeStage_mono (hab.trans hbv))
        (H.activeStage_mono hvt) =
        A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt) :=
      congrArg (fun Z => Z.point (H.activeStage v) (H.activeStage_mono hbv)
        (H.activeStage_mono hvt)) he
    have hh := curvature_le_on_closed_trace_buffer H a t p hσ ha hsmall x hx B v
      (hab.trans hbv) hvt (hb.trans hbv)
    exact hp ▸ hh

private theorem earlier_distance_le_exp_nine_on_surviving_ball
    (H : ObservedHistory) (b t : Icc (0 : ℝ) H.horizon) (hbt : b < t)
    (p : (H.stageAt t).Carrier) {σ : ℝ} (hσ : 0 < σ)
    (htime : t.val - σ ^ 2 ≤ b.val)
    (hsurvive : riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt.le))
    (hcontrol : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt.le) x,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v.val)
              (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt))) ≤ 1) :
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt.le
    let W : TopologicalSpace.Opens (H.stageAt t).Carrier :=
      ⟨riemannianBallOf (H.stageMetric last t.val) p σ,
        isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
    ∀ x y : W,
        riemannianEDistOf (H.stageMetric first b.val)
          (H.backwardSurvivorMap first last hle first le_rfl hle ⟨x.val, hsurvive x.property⟩)
          (H.backwardSurvivorMap first last hle first le_rfl hle ⟨y.val, hsurvive y.property⟩) ≤
        ENNReal.ofReal (Real.exp 9) *
          riemannianEDistOf ((H.stageMetric last t.val).restrictOpen W) x y := by
  classical
  dsimp only
  let first := H.activeStage b
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hbt.le
  let U := H.backwardSurvivorDomain first last hle
  let W : TopologicalSpace.Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric last t.val) p σ,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let inc : W → U := fun x => ⟨x.val, hsurvive x.property⟩
  have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun x : W => hsurvive x.property)
      (isLocalDiffeomorph_subtype_val W x)
  let π := H.backwardSurvivorMap first last hle first le_rfl hle
  have hπ := H.backwardSurvivorMap_isLocalDiffeomorph first last hle first le_rfl hle
  let f := π ∘ inc
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f := isLocalDiffeomorph_comp hπ hinc
  obtain ⟨S, hS, hmetric, _⟩ := exists_trace_solution_on_closed_buffer H b t hbt
  have hSb : S.base.metric b.val = localPullMetric (H.stageMetric first b.val) π hπ :=
    hmetric first le_rfl hle ⟨b.val, le_rfl, hbt.le⟩ (H.activeStage_mem b)
  have hSt : S.base.metric t.val = (H.stageMetric last t.val).restrictOpen U := by
    have h := hmetric last hle le_rfl ⟨t.val, hbt.le, le_rfl⟩ (H.activeStage_mem t)
    have he : H.backwardSurvivorMap first last hle last hle le_rfl =
        (Subtype.val : U → (H.stage last).Carrier) := funext (H.backwardSurvivorMap_last first last hle)
    change S.base.metric t.val = localPullMetric (H.stageMetric last t.val)
      (H.backwardSurvivorMap first last hle last hle le_rfl)
      (H.backwardSurvivorMap_isLocalDiffeomorph first last hle last hle le_rfl) at h
    simp only [he] at h
    exact h.trans (localPullMetric_subtype_val (H.stageMetric last t.val) U)
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hσ4 : 0 < σ ^ 4 := pow_pos hσ 4
  have hsqrt : Real.sqrt (1 / σ ^ 4) = 1 / σ ^ 2 := by
    have he : 1 / σ ^ 4 = (1 / σ ^ 2) ^ 2 := by ring
    rw [he, Real.sqrt_sq (by positivity)]
  have he : 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (1 / σ ^ 4) *
      |b.val - t.val| ≤ 18 := by
    rw [hsqrt, abs_of_nonpos (sub_nonpos.mpr (show b.val ≤ t.val from hbt.le))]
    norm_num [ThreeSpace] at ⊢
    have hd : t.val - b.val ≤ σ ^ 2 := by linarith
    calc
      _ = 18 * ((t.val - b.val) / σ ^ 2) := by ring
      _ ≤ 18 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hσ2).mpr hd) (by norm_num)
      _ = 18 := by norm_num
  have hquad (x : W) (v : TangentSpace ThreeModel x) :
      (H.stageMetric first b.val).inner (f x)
        (mfderiv ThreeModel ThreeModel f x v) (mfderiv ThreeModel ThreeModel f x v) ≤
      Real.exp 18 * ((H.stageMetric last t.val).restrictOpen W).inner x v v := by
    have hRm (r : ℝ) (hr : r ∈ Icc b.val t.val) :
        normSq0S (S.base.metric r) (inc x) 4 (S.base.rm04 r (inc x)) ≤ 1 / σ ^ 4 := by
      let rH : Icc (0 : ℝ) H.horizon := ⟨r, b.property.1.trans hr.1, hr.2.trans t.property.2⟩
      have hbr : b ≤ rH := hr.1
      have hrt : rH ≤ t := hr.2
      let A : BackwardPointTrace H first last hle x.val := Classical.choice (inc x).property
      have h := hcontrol x.val x.property A rH hbr hrt
      apply (le_div_iff₀ hσ4).mpr
      change normSq0S (S.base.metric r) (inc x) 4 (metricRm04At (S.base.metric r) (inc x)) * σ ^ 4 ≤ 1
      rw [hmetric (H.activeStage rH) (H.activeStage_mono hbr) (H.activeStage_mono hrt)
        ⟨r, hr⟩ (H.activeStage_mem rH), normSq0S_metricRm04At_localPullMetric,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage rH)
          (H.activeStage_mono hbr) (H.activeStage_mono hrt) (inc x) A]
      simpa only [mul_comm] using h
    have hD : mfderiv ThreeModel ThreeModel inc x = ContinuousLinearMap.id ℝ ThreeSpace := by
      have h := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel) inc x
      exact h.symm.trans (DifferentialGeometry.mfderiv_subtype_val W x)
    have hbound := (metric_inner_exp_bounds_of_curvature_bound S hS (Subset.refl _)
      (Subset.refl _) (inc x) hRm ⟨le_rfl, hbt.le⟩ ⟨hbt.le, le_rfl⟩ v).2
    have hexp := Real.exp_le_exp.mpr he
    have hnonneg := metric_inner_self_nonneg (S.base.metric t.val) (inc x) v
    have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hexp hnonneg)
    rw [hSb, hSt] at hbound'
    erw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner] at hbound'
    change _ ≤ Real.exp 18 * (H.stageMetric last t.val).inner x.val v v
    have hd := mfderiv_comp x (hπ.mdifferentiable (by decide) (inc x)) (hinc.mdifferentiable (by decide) x)
    rw [show f = π ∘ inc from rfl, hd, hD]
    exact hbound'
  intro x y
  have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph ((H.stageMetric last t.val).restrictOpen W)
    (H.stageMetric first b.val) f hf (Real.exp_pos 18) hquad x y
  have he : Real.sqrt (Real.exp 18) = Real.exp 9 := by rw [← Real.exp_half]; norm_num
  rw [he] at h
  change riemannianEDistOf (H.stageMetric first b.val) (f x) (f y) ≤
    ENNReal.ofReal (Real.exp 9) * riemannianEDistOf ((H.stageMetric last t.val).restrictOpen W) x y
  exact h

private theorem inward_segment_earlier_distance_le_exp_nine
    (H : ObservedHistory) (b t : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t)
    (p : (H.stageAt t).Carrier) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (htime : t.val - σ ^ 2 ≤ b.val)
    (hsurvive : riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt))
    (hcontrol : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          σ ^ 4 * normSq0S (H.stageMetric (H.activeStage v) v.val)
            (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt)) 4
            (metricRm04At (H.stageMetric (H.activeStage v) v.val)
              (A.point (H.activeStage v) (H.activeStage_mono hbv) (H.activeStage_mono hvt))) ≤ 1)
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ) :
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    let g := H.stageMetric last t.val
    let ℓ := (riemannianEDistOf g p x).toReal
    ∀ (A : BackwardPointTrace H first last hle x) (γ : ℝ → (H.stageAt t).Carrier) (d : ℝ),
      γ 0 = p → γ ℓ = x → ContinuousOn γ (Icc 0 ℓ) →
      (∀ u ∈ Icc 0 ℓ, ∀ v ∈ Icc 0 ℓ,
        riemannianEDistOf g (γ u) (γ v) = ENNReal.ofReal |u - v|) →
      d ∈ Icc 0 ℓ → d ≤ σ - r → ℓ - d ≤ r →
      ∃ hd : γ d ∈ U,
        riemannianEDistOf (H.stageMetric first b.val)
          (H.backwardSurvivorMap first last hle first le_rfl hle ⟨γ d, hd⟩)
          (A.point first le_rfl hle) ≤ ENNReal.ofReal (Real.exp 9 * r) := by
  classical
  dsimp only
  intro A γ d hzero hend hγ hparam hd hdσ hdr
  let first := H.activeStage b
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hbt
  let U := H.backwardSurvivorDomain first last hle
  let g := H.stageMetric last t.val
  let ℓ := (riemannianEDistOf g p x).toReal
  have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
  have hℓσ : ℓ ≤ σ := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal hσ.le)
  let W : TopologicalSpace.Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf g p σ,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let π := H.backwardSurvivorMap first last hle first le_rfl hle
  have hπ := H.backwardSurvivorMap_isLocalDiffeomorph first last hle first le_rfl hle
  have hinside (s : ℝ) (hs : s ∈ Icc 0 ℓ) (hsσ : s < σ) : γ s ∈ W := by
    change riemannianEDistOf g p (γ s) < ENNReal.ofReal σ
    rw [← hzero, hparam 0 ⟨le_rfl, hℓ⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
    exact (ENNReal.ofReal_lt_ofReal_iff hσ).mpr hsσ
  have hdW : γ d ∈ W := hinside d hd (by linarith)
  have hsurv (s : ℝ) (hs : s ∈ Icc d ℓ) : γ s ∈ U := by
    rcases lt_or_eq_of_le hs.2 with hslt | rfl
    · exact hsurvive (hinside s ⟨hd.1.trans hs.1, hs.2⟩ (hslt.trans_le hℓσ))
    · rw [hend]
      exact ⟨A⟩
  let δ : ℝ → U := fun s => ⟨γ (projIcc d ℓ hd.2 s), hsurv _ (projIcc d ℓ hd.2 s).property⟩
  have hδ : Continuous δ := by
    apply Continuous.subtype_mk
    exact hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => ⟨hd.1.trans (projIcc d ℓ hd.2 s).property.1, (projIcc d ℓ hd.2 s).property.2⟩)
  have hδeq (s : ℝ) (hs : s ∈ Icc d ℓ) : (δ s).val = γ s := by
    exact congrArg γ (congrArg Subtype.val (projIcc_of_mem hd.2 hs))
  have hdist (y z : W) :
      riemannianEDistOf (H.stageMetric first b.val)
        (π ⟨y.val, hsurvive y.property⟩) (π ⟨z.val, hsurvive z.property⟩) ≤
      ENNReal.ofReal (Real.exp 9) * riemannianEDistOf (g.restrictOpen W) y z := by
    rcases lt_or_eq_of_le hbt with hlt | heq
    · exact earlier_distance_le_exp_nine_on_surviving_ball H b t hlt p hσ htime hsurvive hcontrol y z
    · subst t
      have hp (y : U) : π y = y.val := H.backwardSurvivorMap_last first last hle y
      rw [hp, hp]
      change riemannianEDistOf g y.val z.val ≤ _
      refine (riemannianEDistOf_le_restrictOpen g W y z).trans ?_
      have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp 9) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by norm_num))
      simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_right he (riemannianEDistOf (g.restrictOpen W) y z)
  have hbound (s : ℝ) (hs : s ∈ Ico d ℓ) :
      riemannianEDistOf (H.stageMetric first b.val) (π (δ d)) (π (δ s)) ≤
        ENNReal.ofReal (Real.exp 9 * r) := by
    let η : Icc d s → W := fun z =>
      ⟨γ z.val, hinside z.val ⟨hd.1.trans z.property.1, z.property.2.trans hs.2.le⟩
        ((z.property.2.trans_lt hs.2).trans_le hℓσ)⟩
    let zd : Icc d s := ⟨d, le_rfl, hs.1⟩
    let zs : Icc d s := ⟨s, hs.1, le_rfl⟩
    have hη (u v : Icc d s) : riemannianEDistOf g (η u) (η v) ≤ (1 : ℝ≥0) * edist u v := by
      rw [ENNReal.coe_one, one_mul, Subtype.edist_eq, edist_dist, Real.dist_eq]
      exact (hparam u.val ⟨hd.1.trans u.property.1, u.property.2.trans hs.2.le⟩
        v.val ⟨hd.1.trans v.property.1, v.property.2.trans hs.2.le⟩).le
    have hb := Geometry.riemannianEDistOf_restrictOpen_le_of_lipschitz g W ordConnected_Icc hη zd zs
    have hd' : (⟨(η zd).val, hsurvive (η zd).property⟩ : U) = δ d :=
      Subtype.ext (hδeq d ⟨le_rfl, hd.2⟩).symm
    have hs' : (⟨(η zs).val, hsurvive (η zs).property⟩ : U) = δ s :=
      Subtype.ext (hδeq s ⟨hs.1, hs.2.le⟩).symm
    have hb' := (hdist (η zd) (η zs)).trans (mul_le_mul_right hb (ENNReal.ofReal (Real.exp 9)))
    rw [hd', hs', ENNReal.coe_one, one_mul, Subtype.edist_eq, edist_dist, Real.dist_eq] at hb'
    have habs : |(zd : ℝ) - (zs : ℝ)| = s - d := abs_of_nonpos (sub_nonpos.mpr hs.1) |>.trans (by ring)
    rw [habs, ← ENNReal.ofReal_mul (Real.exp_pos 9).le] at hb'
    have hsr : s - d ≤ r := (sub_le_sub_right hs.2.le d).trans hdr
    exact hb'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsr (Real.exp_pos 9).le))
  have hfinal : riemannianEDistOf (H.stageMetric first b.val) (π (δ d)) (π (δ ℓ)) ≤
      ENNReal.ofReal (Real.exp 9 * r) := by
    rcases lt_or_eq_of_le hd.2 with hdl | rfl
    · apply le_on_closure hbound
        ((Geometry.Riemannian.continuous_riemannianEDist _ (π (δ d))).comp (hπ.contMDiff.continuous.comp hδ)).continuousOn
        continuousOn_const
      rw [closure_Ico hdl.ne]
      exact ⟨hd.2, le_rfl⟩
    · rw [riemannianEDistOf_self]
      exact bot_le
  refine ⟨hsurvive hdW, ?_⟩
  have hd' : (⟨γ d, hsurvive hdW⟩ : U) = δ d := Subtype.ext (hδeq d ⟨le_rfl, hd.2⟩).symm
  have hx' : (δ ℓ).val = x := (hδeq ℓ ⟨hd.2, le_rfl⟩).trans hend
  have hpoint : π (δ ℓ) = A.point first le_rfl hle := by
    have hy : δ ℓ = (⟨x, ⟨A⟩⟩ : U) := Subtype.ext hx'
    rw [hy]
    exact H.backwardSurvivorMap_eq_point first last hle first le_rfl hle ⟨x, ⟨A⟩⟩ A
  rwa [← hd', hpoint] at hfinal

private theorem inward_segment_birth_distance_le_exp_nine
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (k : Fin (H.eventCount + 1)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (hbirth : t.val - σ ^ 2 ≤ H.time k) (hkt : H.time k ≤ t.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ) :
    let b := H.stageTime k
    let hbt : b ≤ t := hkt
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    let g := H.stageMetric last t.val
    let ℓ := (riemannianEDistOf g p x).toReal
    ∀ (A : BackwardPointTrace H first last hle x) (γ : ℝ → (H.stageAt t).Carrier) (d : ℝ),
      γ 0 = p → γ ℓ = x → ContinuousOn γ (Icc 0 ℓ) →
      (∀ u ∈ Icc 0 ℓ, ∀ v ∈ Icc 0 ℓ,
        riemannianEDistOf g (γ u) (γ v) = ENNReal.ofReal |u - v|) →
      d ∈ Icc 0 ℓ → d ≤ σ - r → ℓ - d ≤ r →
      ∃ hd : γ d ∈ U,
        riemannianEDistOf (H.stageMetric first b.val)
          (H.backwardSurvivorMap first last hle first le_rfl hle ⟨γ d, hd⟩)
          (A.point first le_rfl hle) ≤ ENNReal.ofReal (Real.exp 9 * r) := by
  obtain ⟨hsurvive, hcontrol⟩ :=
    open_ball_survives_to_birth_with_curvature_control H t p k hσ hbirth hkt hsmall
  exact inward_segment_earlier_distance_le_exp_nine H (H.stageTime k) t hkt p hσ hr hbirth
    hsurvive (fun y hy A v hbv hvt => (hcontrol y hy A).1 v hbv hvt) x hx

private theorem earlier_ball_survives_and_volume_le_exp_of_protected_terminal_ball
    (H : ObservedHistory) (b t : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t)
    (p : (H.stageAt t).Carrier) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (htime : t.val - σ ^ 2 ≤ b.val)
    (hsurvive : riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ ⊆
      H.backwardSurvivorDomain (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt))
    (hcontrol : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      ∀ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x,
        ∀ (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hst : s ≤ t),
          σ ^ 4 * normSq0S (H.stageMetric (H.activeStage s) s.val)
            (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst)) 4
            (metricRm04At (H.stageMetric (H.activeStage s) s.val)
              (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))) ≤ 1)
    (z : (H.stageAt t).Carrier)
    (hprotect : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) z (r / 2) ⊆
      riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ) :
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    let π := H.backwardSurvivorMap first last hle first le_rfl hle
    let gb := H.stageMetric first b.val
    let gT := H.stageMetric last t.val
    let ρ := Real.exp (-9) * r / 8
    ∃ hz : z ∈ U,
      riemannianBallOf gb (π ⟨z, hz⟩) ρ ⊆
        π '' {y : U | y.val ∈ riemannianBallOf gT z (r / 2)} ∧
      ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier gb
            (riemannianBallOf gb (π ⟨z, hz⟩) ρ) ≤
        riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT
          (riemannianBallOf gT z (r / 2)) := by
  classical
  dsimp only
  let first := H.activeStage b
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hbt
  let U := H.backwardSurvivorDomain first last hle
  let π := H.backwardSurvivorMap first last hle first le_rfl hle
  have hπ := H.backwardSurvivorMap_isLocalDiffeomorph first last hle first le_rfl hle
  let gb := H.stageMetric first b.val
  let gT := H.stageMetric last t.val
  let ρ := Real.exp (-9) * r / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r / 2 := by
    have he : Real.exp (-9) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right he hr.le
    dsimp only [ρ]
    linarith
  have hecancel : Real.exp 9 * Real.exp (-9) = 1 := by rw [← Real.exp_add]; norm_num
  have hexpρ : Real.exp 9 * ρ = r / 8 := by dsimp [ρ]; nlinarith [hecancel]
  let W : TopologicalSpace.Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf gT p σ,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  have hzW : z ∈ W := hprotect (by
    change riemannianEDistOf gT z z ≤ ENNReal.ofReal (r / 2)
    rw [riemannianEDistOf_self]
    exact bot_le)
  let zW : W := ⟨z, hzW⟩
  let inc : W → U := fun x => ⟨x.val, hsurvive x.property⟩
  have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ inc := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun x : W => hsurvive x.property)
      (isLocalDiffeomorph_subtype_val W x)
  let f := π ∘ inc
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f := isLocalDiffeomorph_comp hπ hinc
  have hfinj : Function.Injective f :=
    (H.backwardSurvivorMap_injective first last hle first le_rfl hle).comp
      (fun x y h => Subtype.ext (congrArg (fun q : U => q.val) h))
  refine ⟨hsurvive hzW, ?_⟩
  change riemannianBallOf gb (f zW) ρ ⊆
      π '' {y : U | y.val ∈ riemannianBallOf gT z (r / 2)} ∧
    ENNReal.ofReal (Real.exp (-27)) *
      riemannianVolumeMeasure ThreeModel (H.stage first).Carrier gb (riemannianBallOf gb (f zW) ρ) ≤
    riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT (riemannianBallOf gT z (r / 2))
  rcases lt_or_eq_of_le hbt with hlt | heq
  · let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
    let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
    let : MeasurableSpace W := borel W
    let : BorelSpace W := ⟨rfl⟩
    obtain ⟨S₀, hS₀, hmetric, _⟩ := exists_trace_solution_on_closed_buffer H b t hlt
    let S := S₀.localPullback inc hinc
    have hS : IsSolutionOn S := hS₀.localPullback inc hinc
    have hS₀b : S₀.base.metric b.val = localPullMetric gb π hπ :=
      hmetric first le_rfl hle ⟨b.val, le_rfl, hbt⟩ (H.activeStage_mem b)
    have hS₀t : S₀.base.metric t.val = gT.restrictOpen U := by
      have h := hmetric last hle le_rfl ⟨t.val, hbt, le_rfl⟩ (H.activeStage_mem t)
      have he : H.backwardSurvivorMap first last hle last hle le_rfl =
          (Subtype.val : U → (H.stage last).Carrier) := funext (H.backwardSurvivorMap_last first last hle)
      change S₀.base.metric t.val = localPullMetric gT
        (H.backwardSurvivorMap first last hle last hle le_rfl)
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle last hle le_rfl) at h
      simp only [he] at h
      exact h.trans (localPullMetric_subtype_val gT U)
    have hSb : S.base.metric b.val = localPullMetric gb f hf := by
      change localPullMetric (S₀.base.metric b.val) inc hinc = _
      rw [hS₀b]
      exact localPullMetric_comp gb π inc hπ hinc hf
    have hSt : S.base.metric t.val = gT.restrictOpen W := by
      change localPullMetric (S₀.base.metric t.val) inc hinc = _
      rw [hS₀t, ← localPullMetric_subtype_val]
      rw [localPullMetric_comp _ Subtype.val inc (isLocalDiffeomorph_subtype_val U) hinc
        (isLocalDiffeomorph_subtype_val W)]
      exact localPullMetric_subtype_val gT W
    have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hσ4 : 0 < σ ^ 4 := pow_pos hσ 4
    have hsqrt : Real.sqrt (1 / σ ^ 4) = 1 / σ ^ 2 := by
      have he : 1 / σ ^ 4 = (1 / σ ^ 2) ^ 2 := by ring
      rw [he, Real.sqrt_sq (by positivity)]
    have hRm (s : ℝ) (hs : s ∈ Icc b.val t.val) (x : W) :
        normSq0S (S.base.metric s) x 4 (S.base.rm04 s x) ≤ 1 / σ ^ 4 := by
      let sH : Icc (0 : ℝ) H.horizon := ⟨s, b.property.1.trans hs.1, hs.2.trans t.property.2⟩
      have hbs : b ≤ sH := hs.1
      have hst : sH ≤ t := hs.2
      let A : BackwardPointTrace H first last hle x.val := Classical.choice (inc x).property
      have h := hcontrol x.val x.property A sH hbs hst
      apply (le_div_iff₀ hσ4).mpr
      change normSq0S (localPullMetric (S₀.base.metric s) inc hinc) x 4
        (metricRm04At (localPullMetric (S₀.base.metric s) inc hinc) x) * σ ^ 4 ≤ 1
      rw [normSq0S_metricRm04At_localPullMetric,
        hmetric (H.activeStage sH) (H.activeStage_mono hbs) (H.activeStage_mono hst)
          ⟨s, hs⟩ (H.activeStage_mem sH), normSq0S_metricRm04At_localPullMetric,
        H.backwardSurvivorMap_eq_point first last hle (H.activeStage sH)
          (H.activeStage_mono hbs) (H.activeStage_mono hst) (inc x) A]
      simpa only [mul_comm] using h
    let L := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (1 / σ ^ 4) * |b.val - t.val|
    have hL : L ≤ 9 := by
      dsimp only [L]
      rw [hsqrt, abs_of_nonpos (sub_nonpos.mpr (show b.val ≤ t.val from hbt))]
      norm_num [ThreeSpace]
      have hd : t.val - b.val ≤ σ ^ 2 := by linarith
      calc
        _ = 9 * ((t.val - b.val) / σ ^ 2) := by ring
        _ ≤ 9 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hσ2).mpr hd) (by norm_num)
        _ = 9 := by norm_num
    have hdist (x : W) : riemannianEDistOf (gT.restrictOpen W) zW x ≤
        ENNReal.ofReal (Real.exp 9) * riemannianEDistOf (S.base.metric b.val) zW x := by
      have h := (riemannianEDistOf_exp_bounds_of_curvature_bound S hS (Subset.refl _)
        (Subset.refl _) hRm ⟨hbt, le_rfl⟩ ⟨le_rfl, hbt⟩ zW x).2
      rw [hSt, abs_sub_comm t.val b.val] at h
      exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hL)) _)
    let R : ℝ≥0 := ⟨r / 2, by positivity⟩
    let Rb : ℝ≥0 := ⟨2 * ρ, by positivity⟩
    have hfit : ENNReal.ofReal (Real.exp L) * (Rb : ℝ≥0∞) ≤ (R : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      change Real.exp L * (2 * ρ) ≤ r / 2
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hL) (by positivity : 0 ≤ 2 * ρ)
      nlinarith [hexpρ]
    have hcompact : IsCompact {y : (H.stageAt t).Carrier | riemannianEDistOf gT z y ≤ (R : ℝ≥0∞)} :=
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist gT z) continuous_const).isCompact
    have hR : (R : ℝ≥0∞) = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    have hRb : (Rb : ℝ≥0∞) = ENNReal.ofReal (2 * ρ) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    have hRball : {y : (H.stageAt t).Carrier | riemannianEDistOf gT z y ≤ (R : ℝ≥0∞)} ⊆ W := by
      intro y hy
      rw [hR] at hy
      exact hprotect hy
    have hcpt := isCompact_intrinsic_closedBall_of_terminal_ball gT W S hS (Subset.refl _)
      (Subset.refl _) hRm ⟨le_rfl, hbt⟩ hSt zW hcompact hRball hfit
    have hcpt' : IsCompact (riemannianClosedBallOf (localPullMetric gb f hf) zW (2 * ρ)) := by
      simpa only [hSb, hRb, riemannianClosedBallOf] using hcpt
    let K := riemannianBallOf (S.base.metric b.val) zW ρ
    have hKopen : IsOpen K := isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ zW) continuous_const
    have hKimage : f '' K = riemannianBallOf gb (f zW) ρ := by
      dsimp only [K]
      rw [hSb]
      exact Geometry.Metric.image_riemannianBallOf_localPullMetric gb f hf hfinj zW hρ (by linarith) hcpt'
    have hKsub (y : W) (hy : y ∈ K) : y.val ∈ riemannianBallOf gT z (r / 2) := by
      have hbound := (riemannianEDistOf_le_restrictOpen gT W zW y).trans (hdist y)
      have hm : ENNReal.ofReal (Real.exp 9) * riemannianEDistOf (S.base.metric b.val) zW y ≤
          ENNReal.ofReal (Real.exp 9) * ENNReal.ofReal ρ := mul_le_mul_right hy.le _
      have hh := hbound.trans hm
      rw [← ENNReal.ofReal_mul (Real.exp_pos 9).le, hexpρ] at hh
      exact hh.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r / 2)).mpr (by linarith))
    constructor
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hKimage.symm ▸ hy
      exact ⟨inc x, hKsub x hx, rfl⟩
    · have hborn : riemannianVolumeMeasure ThreeModel W (S.base.metric b.val) K =
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier gb (riemannianBallOf gb (f zW) ρ) := by
        rw [← hKimage]
        apply Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
          (S.base.metric b.val) gb f hf hfinj _ hKopen.measurableSet
        intro x v w
        rw [hSb, localPullMetric_inner]
      have hvol := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
        (S.base.metric t.val) (S.base.metric b.val) (Real.exp_pos 18) hKopen.measurableSet
        (fun x _ v => by
          have h := (metric_inner_exp_bounds_of_curvature_bound S hS (Subset.refl _)
            (Subset.refl _) x (fun s hs => hRm s hs x) ⟨le_rfl, hbt⟩ ⟨hbt, le_rfl⟩ v).2
          refine h.trans (mul_le_mul_of_nonneg_right ?_ (metric_inner_self_nonneg _ x v))
          apply Real.exp_le_exp.mpr
          change 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (1 / σ ^ 4) * |b.val - t.val| ≤ 18
          change L ≤ 9 at hL
          dsimp only [L] at hL
          linarith)
      have hfactor : Real.sqrt (Real.exp 18 ^ Module.finrank ℝ ThreeSpace) = Real.exp 27 := by
        rw [← Real.exp_nat_mul, ← Real.exp_half]
        norm_num [ThreeSpace]
      rw [hfactor, hborn, hSt] at hvol
      have hterminal : riemannianVolumeMeasure ThreeModel W (gT.restrictOpen W) K ≤
          riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT (riemannianBallOf gT z (r / 2)) := by
        rw [Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
          (gT.restrictOpen W) gT Subtype.val (isLocalDiffeomorph_subtype_val W) Subtype.val_injective
          (fun x v w => by rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply,
            mfderiv_subtype_val_apply]) hKopen.measurableSet]
        exact MeasureTheory.measure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hKsub x hx)
      have hh := hvol.trans (mul_le_mul_right hterminal (ENNReal.ofReal (Real.exp 27)))
      have hm := mul_le_mul_right hh (ENNReal.ofReal (Real.exp (-27)))
      have he : ENNReal.ofReal (Real.exp (-27)) * ENNReal.ofReal (Real.exp 27) = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        norm_num
      simpa only [← mul_assoc, he, one_mul] using hm
  · subst t
    have hp (x : U) : π x = x.val := H.backwardSurvivorMap_last first last hle x
    have hfz : f zW = z := hp (inc zW)
    rw [hfz]
    change riemannianBallOf gT z ρ ⊆ π '' {y : U | y.val ∈ riemannianBallOf gT z (r / 2)} ∧ _
    have hsub : riemannianBallOf gT z ρ ⊆ riemannianBallOf gT z (r / 2) :=
      riemannianBallOf_mono gT z hρr.le
    constructor
    · intro x hx
      have hxclosed : x ∈ riemannianClosedBallOf gT z (r / 2) := by
        change riemannianEDistOf gT z x ≤ ENNReal.ofReal (r / 2)
        exact le_of_lt (hsub hx)
      have hxW : x ∈ W := hprotect hxclosed
      exact ⟨⟨x, hsurvive hxW⟩, hsub hx, hp _⟩
    · have he : ENNReal.ofReal (Real.exp (-27)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by norm_num))
      have hm := mul_le_mul_left he
        (riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT (riemannianBallOf gT z ρ))
      have hm' : ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT (riemannianBallOf gT z ρ) ≤
          riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT (riemannianBallOf gT z ρ) := by
        simpa only [one_mul] using hm
      exact hm'.trans (MeasureTheory.measure_mono hsub)

theorem ObservedHistory.exists_inward_point_with_earlier_volume_comparison
    (H : ObservedHistory) (a b t : Icc (0 : ℝ) H.horizon)
    (hab : a ≤ b) (hbt : b ≤ t) (p : (H.stageAt t).Carrier)
    {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hrσ : r ≤ σ)
    (ha : a.val < t.val - σ ^ 2) (hb : t.val - σ ^ 2 ≤ b.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (htrace : ∀ x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ,
      Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono (hab.trans hbt)) x))
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ)
    (A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) x) :
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    let π := H.backwardSurvivorMap first last hle first le_rfl hle
    let gb := H.stageMetric first b.val
    let gT := H.stageMetric last t.val
    ∃ (z : (H.stageAt t).Carrier) (hz : z ∈ U),
      riemannianClosedBallOf gT z (r / 2) ⊆ riemannianBallOf gT p σ ∧
      riemannianEDistOf gb (π ⟨z, hz⟩) (A.point first le_rfl hle) ≤
        ENNReal.ofReal (Real.exp 9 * r) ∧
      σ ^ 4 * normSq0S gb (π ⟨z, hz⟩) 4 (metricRm04At gb (π ⟨z, hz⟩)) ≤ 1 ∧
      riemannianBallOf gb (π ⟨z, hz⟩) (Real.exp (-9) * r / 8) ⊆
        π '' {y : U | y.val ∈ riemannianBallOf gT z (r / 2)} ∧
      ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier gb
            (riemannianBallOf gb (π ⟨z, hz⟩) (Real.exp (-9) * r / 8)) ≤
        riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT
          (riemannianBallOf gT z (r / 2)) := by
  classical
  dsimp only
  let gT := H.stageMetric (H.activeStage t) t.val
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcompact : IsCompact (riemannianClosedBallOf gT p (σ + 1)) :=
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist gT p) continuous_const).isCompact
  obtain ⟨γ, d, hzero, hend, hsmooth, hparam, hd, hdσ, hdr, _, hprotect⟩ :=
    Geometry.Riemannian.exists_inward_point_and_minimizer_of_isCompact_closedBall
      gT p x hr hrσ hx (by linarith) hcompact
  obtain ⟨hsurvive, hcontrol⟩ := earlier_survival_and_curvature_of_closed_trace_buffer
    H a b t hab hbt p hσ ha hb hsmall htrace
  have hopen := fun y (hy : y ∈ riemannianBallOf gT p σ) => hcontrol y
    (show riemannianEDistOf gT p y ≤ ENNReal.ofReal σ from hy.le)
  obtain ⟨hz, hdistance⟩ := inward_segment_earlier_distance_le_exp_nine H b t hbt p hσ hr hb
    hsurvive hopen x hx A γ d hzero hend hsmooth.continuousOn hparam hd hdσ hdr
  obtain ⟨hz', hball, hvolume⟩ := earlier_ball_survives_and_volume_le_exp_of_protected_terminal_ball
    H b t hbt p hσ hr hb hsurvive hopen (γ d) hprotect
  refine ⟨γ d, hz, hprotect, hdistance, ?_, hball, hvolume⟩
  have hy : γ d ∈ riemannianBallOf gT p σ := hprotect (by
    change riemannianEDistOf gT (γ d) (γ d) ≤ ENNReal.ofReal (r / 2)
    rw [riemannianEDistOf_self]
    exact bot_le)
  let B : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) (γ d) := Classical.choice hz
  have hc := hcontrol (γ d)
    (show riemannianEDistOf gT p (γ d) ≤ ENNReal.ofReal σ from hy.le) B b le_rfl hbt
  rw [H.backwardSurvivorMap_eq_point (H.activeStage b) (H.activeStage t)
    (H.activeStage_mono hbt) (H.activeStage b) le_rfl (H.activeStage_mono hbt) ⟨γ d, hz⟩ B]
  exact hc

private theorem birth_ball_survives_and_volume_le_exp_of_protected_terminal_ball
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (k : Fin (H.eventCount + 1)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (hbirth : t.val - σ ^ 2 ≤ H.time k) (hkt : H.time k ≤ t.val)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (z : (H.stageAt t).Carrier)
    (hprotect : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) z (r / 2) ⊆
      riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ) :
    let b := H.stageTime k
    let hbt : b ≤ t := hkt
    let first := H.activeStage b
    let last := H.activeStage t
    let hle := H.activeStage_mono hbt
    let U := H.backwardSurvivorDomain first last hle
    let π := H.backwardSurvivorMap first last hle first le_rfl hle
    let gb := H.stageMetric first b.val
    let gT := H.stageMetric last t.val
    let ρ := Real.exp (-9) * r / 8
    ∃ hz : z ∈ U,
      riemannianBallOf gb (π ⟨z, hz⟩) ρ ⊆
        π '' {y : U | y.val ∈ riemannianBallOf gT z (r / 2)} ∧
      ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier gb
            (riemannianBallOf gb (π ⟨z, hz⟩) ρ) ≤
        riemannianVolumeMeasure ThreeModel (H.stage last).Carrier gT
          (riemannianBallOf gT z (r / 2)) := by
  obtain ⟨hsurvive, hcontrol⟩ :=
    open_ball_survives_to_birth_with_curvature_control H t p k hσ hbirth hkt hsmall
  exact earlier_ball_survives_and_volume_le_exp_of_protected_terminal_ball
    H (H.stageTime k) t hkt p hσ hr hbirth hsurvive
      (fun x hx A => (hcontrol x hx A).1) z hprotect

private theorem exists_cap_contact_scale_bound
    (D : ℝ) (hD : StandardCap.transitionEnd < D) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
        {σ : ℝ}, 0 < σ →
        (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
        ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
          (x : (H.stageAt t).Carrier),
        x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ →
        ∀ (A : BackwardPointTrace H i.succ (H.activeStage t) hl x),
        t.val - σ ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t.val →
        ∀ {fixed : StaticCapScaffold} {m : ℕ} {ε : ℝ}, ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : (H.event i).RetainedBoundaryIndex}
          (S : (H.event i).PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
        ∀ z : ThreeBall,
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.cap b.val z) =
              Sum.inl (A.point i.succ le_rfl hl) →
          S.neck.scale * σ ^ 2 ≤ 18 := by
  obtain ⟨ε₀, hε₀, hscalar⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window D hD
  refine ⟨ε₀, hε₀, ?_⟩
  intro H t p σ hσ hsmall i hl x hx A hbirth hkt fixed m ε hε hm b S hcanonical z hpres
  let tb := H.stageTime i.succ
  have hbt : tb ≤ t := hkt
  have hstage : H.activeStage tb = i.succ := H.activeStage_stageTime i.succ
  have hbound := (ObservedHistory.ball_subset_backwardSurvivorDomain_and_closed_trace_isRmControlled
    H t p i.succ hσ hbirth hkt hsmall).2 x hx
  have hbirthBound : σ ^ 4 * normSq0S (H.initialMetric i.succ)
      (A.point i.succ le_rfl hl) 4
      (metricRm04At (H.initialMetric i.succ) (A.point i.succ le_rfl hl)) ≤ 1 := by
    have hforall (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage tb)
        (hjt : j ≤ H.activeStage t) (B : BackwardPointTrace H j (H.activeStage t) hjt x) :
        σ ^ 4 * normSq0S (H.stageMetric j tb.val) (B.point j le_rfl hjt) 4
          (metricRm04At (H.stageMetric j tb.val) (B.point j le_rfl hjt)) ≤ 1 := by
      subst j
      exact (hbound B).1 tb le_rfl hbt
    have h := hforall i.succ hstage.symm hl A
    have htb : tb.val = H.time i.succ := rfl
    rw [htb, H.stageMetric_initial] at h
    exact h
  have hnorm := sq_mul_scalar_abs_le_of_rm_bound (H.initialMetric i.succ)
    (A.point i.succ le_rfl hl) hbirthBound
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by norm_num [ThreeSpace]
  rw [hdim] at hnorm
  have hvalue : S.inclusion (S.witness.cap z) = A.point i.succ le_rfl hl :=
    Sum.inl_injective ((S.cap_eq z).symm.trans hpres)
  have hlow := hscalar (H.event i) hε hm S hcanonical z
  rw [S.scalar_eq (H.event i), hvalue] at hlow
  rw [H.event_output i] at hlow
  have hmul := mul_le_mul_of_nonneg_right
    (hlow.trans (le_abs_self _)) (sq_nonneg σ)
  nlinarith

namespace ObservedHistory

private theorem volume_mul_cube_le_of_smaller_controlled_radii
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsmall : ∀ q : ℝ, 0 < q → q < R → H.isParabolicallyRmControlledBall t p q) :
    riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (H.stageMetric (H.activeStage t) t.val)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p R) *
      ENNReal.ofReal r ^ 3 ≤
    ENNReal.ofReal (8 * Real.exp 6) * ENNReal.ofReal R ^ 3 *
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (H.stageMetric (H.activeStage t) t.val)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p r) := by
  have hR : 0 < R := hr.trans_le hrR
  let g := H.stageMetric (H.activeStage t) t.val
  have hcurv (x : (H.stageAt t).Carrier) (hx : x ∈ riemannianBallOf g p R) :
      R ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 := by
    have hc : ContinuousAt (fun q : ℝ => q ^ 4 * normSq0S g x 4 (metricRm04At g x)) R := by
      fun_prop
    apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R))
    have hxq : ∀ᶠ q : ℝ in 𝓝 R, riemannianEDistOf g p x < ENNReal.ofReal q :=
      ENNReal.continuous_ofReal.continuousAt.eventually_const_lt hx
    filter_upwards [hxq.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hxq hq hqR
    exact (hsmall q hq hqR).terminal_curvature_bound H x hxq
  have hRic (x : (H.stageAt t).Carrier) (hx : x ∈ riemannianBallOf g p R)
      (v : TangentSpace ThreeModel x) :
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * (3 / R) ^ 2) *
          g.inner x v v ≤ ricciTensor g x v v := by
    have hnorm : normSq0S g x 4 (metricRm04At g x) ≤ 1 / R ^ 4 := by
      apply (le_div_iff₀ (pow_pos hR 4)).mpr
      simpa only [mul_comm] using hcurv x hx
    have hroot : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ 1 / R ^ 2 := by
      have hh := Real.sqrt_le_sqrt hnorm
      rwa [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
        show R ^ 4 = (R ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg R)] at hh
    have hh := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm g hroot v
    norm_num [ThreeSpace] at hh ⊢
    have hinner : 0 ≤ g.inner x v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos x v hv).le
    have hcoeff : -(2 * (3 / R) ^ 2) ≤ -(9 * (1 / R ^ 2)) := by
      field_simp
      norm_num
    have hbound := (mul_le_mul_of_nonneg_right hcoeff hinner).trans (show
      -(9 * (1 / R ^ 2)) * g.inner x v v ≤ ricciTensor g x v v from by
        simpa only [one_div, neg_mul] using hh)
    simpa only [neg_mul] using hbound
  have hbg := Geometry.Riemannian.VolumeComparison.volume_mul_pow_le_of_local_ricci_lower_bound
    g p (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hR.le) hr hrR
    (Geometry.Metric.isClosed_riemannianClosedBallOf g p R).isCompact hRic
  have he : 3 / R * (2 : ℝ) * R = 6 := by field_simp; ring
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by norm_num [ThreeSpace]
  norm_num only [hdim, Nat.cast_ofNat, Nat.reduceSub, he] at hbg
  simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * Real.exp 6),
    ENNReal.ofReal_pow hR.le, ENNReal.ofReal_pow hr.le] using hbg

private theorem volume_lower_bound_of_smaller_controlled_radii
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {r R κ : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsmall : ∀ q : ℝ, 0 < q → q < R → H.isParabolicallyRmControlledBall t p q)
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal R ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (H.stageMetric (H.activeStage t) t.val)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p R)) :
    ENNReal.ofReal (κ / (8 * Real.exp 6)) * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (H.stageMetric (H.activeStage t) t.val)
        (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p r) := by
  have hR : 0 < R := hr.trans_le hrR
  have hC : 0 < (8 : ℝ) * Real.exp 6 := by positivity
  have hCR : 0 < ENNReal.ofReal (8 * Real.exp 6) * ENNReal.ofReal R ^ 3 := by positivity
  have hfinite : ENNReal.ofReal (8 * Real.exp 6) * ENNReal.ofReal R ^ 3 ≠ ⊤ := by finiteness
  apply (ENNReal.mul_le_mul_iff_left hCR.ne' hfinite).mp
  have hcancel : ENNReal.ofReal (κ / (8 * Real.exp 6)) * ENNReal.ofReal (8 * Real.exp 6) =
      ENNReal.ofReal κ := by
    rw [ENNReal.ofReal_div_of_pos hC,
      ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top]
  calc
    _ = (ENNReal.ofReal κ * ENNReal.ofReal R ^ 3) * ENNReal.ofReal r ^ 3 := by
      calc
        _ = (ENNReal.ofReal (κ / (8 * Real.exp 6)) * ENNReal.ofReal (8 * Real.exp 6)) *
            ENNReal.ofReal R ^ 3 * ENNReal.ofReal r ^ 3 := by ac_rfl
        _ = _ := by rw [hcancel]
    _ ≤ _ := mul_le_mul' hvolume le_rfl
    _ ≤ _ := volume_mul_cube_le_of_smaller_controlled_radii H t p hr hrR hsmall
    _ = _ := mul_comm _ _


end ObservedHistory

theorem ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_cap_contact
    (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < κ ∧
      ∀ (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
        {σ : ℝ}, 0 < σ →
        (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
        ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
          (x : (H.stageAt t).Carrier),
        x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p σ →
        ∀ (A : BackwardPointTrace H i.succ (H.activeStage t) hl x),
        t.val - σ ^ 2 ≤ H.time i.succ → H.time i.succ ≤ t.val →
        ∀ {fixed : StaticCapScaffold} {m : ℕ} {ε : ℝ}, ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : (H.event i).RetainedBoundaryIndex}
          (S : (H.event i).PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
        ∀ z : ThreeBall,
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.cap b.val z) =
              Sum.inl (A.point i.succ le_rfl hl) →
          ∀ r : ℝ, 0 < r → r ≤ σ →
          ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
              (H.stageMetric (H.activeStage t) t.val)
              (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p r) := by
  have hE := StandardCap.transitionEnd_pos
  have hD' : StandardCap.transitionEnd < D := by linarith
  let R₁ := 4 * StandardCap.transitionEnd + 4
  have hR₁ : 0 < R₁ := by dsimp [R₁]; linarith
  have hmargin : R₁ + 1 < D := by dsimp [R₁]; linarith
  obtain ⟨εs, hεs, hscale⟩ := exists_cap_contact_scale_bound D hD'
  obtain ⟨κ₀, hκ₀, hstatic⟩ := StandardCap.exists_uniform_nearby_scaled_window_ball_volume_lower R₁ hR₁
  let θ := Real.exp (-9) / 100
  let α := Real.exp (-9) * θ / 8
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθsmall : θ ≤ 1 / 100 := by
    have he := Real.exp_le_one_iff.mpr (by norm_num : (-9 : ℝ) ≤ 0)
    dsimp only [θ]
    linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hαsmall : α ≤ 1 / 800 := by
    have he := mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by norm_num : (-9 : ℝ) ≤ 0)) hθ.le
    dsimp only [α]
    linarith
  have hsqrt18 : Real.sqrt 18 ≤ 5 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hαfit : α * Real.sqrt 18 ≤ 1 := by
    have he := mul_le_mul_of_nonneg_left hsqrt18 hα.le
    linarith
  let κ := Real.exp (-27) * κ₀ * α ^ 3
  refine ⟨min εs (1 / 2), κ / (8 * Real.exp 6), lt_min hεs (by norm_num), min_le_right _ _, ?_, ?_⟩
  · dsimp [κ]
    positivity
  intro H t p σ hσ hsmall i hl x hx A hbirth hkt fixed m ε hε hm b S hcanonical z hpres
  have hεs' : ε ≤ εs := hε.trans (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := hε.trans (min_le_right _ _)
  have hqσ := hscale H t p hσ hsmall i hl x hx A hbirth hkt hεs' hm S hcanonical z hpres
  let r := θ * σ
  have hr : 0 < r := mul_pos hθ hσ
  have hrσ : r ≤ σ := by
    have hh := mul_le_mul_of_nonneg_right (show θ ≤ 1 by linarith) hσ.le
    simpa only [one_mul] using hh
  let gT := H.stageMetric (H.activeStage t) t.val
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
  have hcompact : IsCompact (riemannianClosedBallOf gT p (σ + 1)) :=
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist gT p) continuous_const).isCompact
  obtain ⟨γ, d, hzero, hend, hsmooth, hparam, hd, hdσ, hdr, _, hprotect⟩ :=
    Geometry.Riemannian.exists_inward_point_and_minimizer_of_isCompact_closedBall gT p x hr hrσ hx (by linarith) hcompact
  let tb := H.stageTime i.succ
  have hstage : H.activeStage tb = i.succ := H.activeStage_stageTime i.succ
  have hsegment (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage tb)
      (hjt : j ≤ H.activeStage t) (B : BackwardPointTrace H j (H.activeStage t) hjt x) :
      ∃ hy : γ d ∈ H.backwardSurvivorDomain j (H.activeStage t) hjt,
        riemannianEDistOf (H.stageMetric j tb.val)
          (H.backwardSurvivorMap j (H.activeStage t) hjt j le_rfl hjt ⟨γ d, hy⟩)
          (B.point j le_rfl hjt) ≤ ENNReal.ofReal (Real.exp 9 * r) := by
    subst j
    exact inward_segment_birth_distance_le_exp_nine H t p i.succ hσ hr hbirth hkt hsmall x hx
      B γ d hzero hend hsmooth.continuousOn hparam hd hdσ hdr
  obtain ⟨hy, hnear⟩ := hsegment i.succ hstage.symm hl A
  let U := H.backwardSurvivorDomain i.succ (H.activeStage t) hl
  let π := H.backwardSurvivorMap i.succ (H.activeStage t) hl i.succ le_rfl hl
  let y := π ⟨γ d, hy⟩
  have htb : tb.val = H.time i.succ := rfl
  rw [htb, H.stageMetric_initial] at hnear
  obtain ⟨x₀, δ, k, datum, w, _, hmetric, hcap⟩ := hcanonical
  obtain ⟨u, hu, hupoint⟩ := hcap z
  have hcontact : S.window u = A.point i.succ le_rfl hl :=
    hupoint.trans (Sum.inl_injective ((S.cap_eq z).symm.trans hpres))
  let Q := 1 / σ ^ 2
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hrootQ : Real.sqrt Q = 1 / σ := by
    have he : Q = (1 / σ) ^ 2 := by dsimp [Q]; ring
    rw [he, Real.sqrt_sq (by positivity)]
  have hscaleQ : S.neck.scale ≤ 18 * Q := by
    dsimp only [Q]
    rw [mul_one_div]
    exact (le_div_iff₀ (sq_pos_of_pos hσ)).mpr hqσ
  have hdistance : riemannianEDistOf (H.initialMetric i.succ) (S.window u) y ≤
      ENNReal.ofReal ((1 / 100 : ℝ) / Real.sqrt Q) := by
    rw [hcontact, riemannianEDistOf_comm]
    have he : Real.exp 9 * r = (1 / 100 : ℝ) / Real.sqrt Q := by
      rw [hrootQ]
      dsimp [r, θ]
      have hh : Real.exp 9 * Real.exp (-9) = 1 := by rw [← Real.exp_add]; norm_num
      field_simp
      nlinarith [hh]
    simpa only [he] using hnear
  have hreserve : 2 * ‖u.val‖ + (1 / 100 : ℝ) * Real.sqrt 18 < R₁ / 2 := by
    dsimp only [R₁]
    nlinarith
  have hmetricBounds (v : standardCapWindow D) (hv : ‖v.val‖ < D)
      (X : TangentSpace ThreeModel v) :
      (1 / 4 : ℝ) * StandardCap.metric.inner v.val X X ≤
        (scaleMetric S.neck.scale S.neck.scale_pos (H.initialMetric i.succ)).inner (S.window v)
          (mfderiv ThreeModel ThreeModel S.window v X) (mfderiv ThreeModel ThreeModel S.window v X) ∧
      (scaleMetric S.neck.scale S.neck.scale_pos (H.initialMetric i.succ)).inner (S.window v)
          (mfderiv ThreeModel ThreeModel S.window v X) (mfderiv ThreeModel ThreeModel S.window v X) ≤
        4 * StandardCap.metric.inner v.val X X := by
    have hb := w.window_inner_bounds hεhalf hv X
    simp only [SmoothRiemannianMetric.restrictOpen_inner, standardCapMetric_eq_metric] at hb
    rw [hmetric v X X, H.event_output i] at hb
    rw [scaleMetric_inner]
    have hn := metric_inner_self_nonneg StandardCap.metric v.val X
    constructor <;> nlinarith [hb.1, hb.2]
  have hstaticVol := hstatic (H.initialMetric i.succ) S.window S.window_smooth
    S.neck.scale Q 18 S.neck.scale_pos hQ (by norm_num) hscaleQ hmetricBounds hmargin
    u y (1 / 100) (by norm_num) hdistance hreserve α hα hαfit
  let ρ := Real.exp (-9) * r / 8
  have hρασ : ρ = α * σ := by dsimp [ρ, r, α]; ring
  have hρroot : α / Real.sqrt Q = ρ := by
    rw [hrootQ, hρασ]
    field_simp
  rw [hρroot] at hstaticVol
  have htransport (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage tb)
      (hjt : j ≤ H.activeStage t) :
      ∃ hz : γ d ∈ H.backwardSurvivorDomain j (H.activeStage t) hjt,
        ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.stageMetric j tb.val)
            (riemannianBallOf (H.stageMetric j tb.val)
              (H.backwardSurvivorMap j (H.activeStage t) hjt j le_rfl hjt ⟨γ d, hz⟩) ρ) ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier gT (riemannianBallOf gT (γ d) (r / 2)) := by
    subst j
    obtain ⟨hz, _, hv⟩ := birth_ball_survives_and_volume_le_exp_of_protected_terminal_ball
      H t p i.succ hσ hr hbirth hkt hsmall (γ d) hprotect
    exact ⟨hz, hv⟩
  obtain ⟨hz, hvol⟩ := htransport i.succ hstage.symm hl
  rw [htb, H.stageMetric_initial] at hvol
  have hsub : riemannianBallOf gT (γ d) (r / 2) ⊆ riemannianBallOf gT p σ := by
    intro v hv
    apply hprotect
    change riemannianEDistOf gT (γ d) v ≤ ENNReal.ofReal (r / 2)
    exact le_of_lt hv
  have hbound := (mul_le_mul_right hstaticVol (ENNReal.ofReal (Real.exp (-27)))).trans
    (hvol.trans (MeasureTheory.measure_mono hsub))
  have he : ENNReal.ofReal κ * ENNReal.ofReal σ ^ 3 =
      ENNReal.ofReal (Real.exp (-27)) * (ENNReal.ofReal κ₀ * ENNReal.ofReal ρ ^ 3) := by
    dsimp only [κ]
    rw [ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) hκ₀).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hα.le,
      hρασ, ENNReal.ofReal_mul hα.le, mul_pow]
    ring
  have hseed := he ▸ hbound
  intro radius hradius hradiusσ
  exact H.volume_lower_bound_of_smaller_controlled_radii t p hradius hradiusσ hsmall hseed

private theorem terminal_ball_volume_lower_of_initial_time_contact
    (H : ObservedHistory) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    {σ ρ κ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (htime : t.val = σ ^ 2)
    (hsmall : ∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q)
    (hvolume : ∀ x : (H.stage 0).Carrier, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0)
          (riemannianBallOf (H.initialMetric 0) x r)) :
    ∀ r : ℝ, 0 < r → r ≤ σ →
      ENNReal.ofReal
          ((Real.exp (-27) * κ * (Real.exp (-9) / 8) ^ 3) / (8 * Real.exp 6)) *
          ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t.val)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p r) := by
  have hbirth : t.val - σ ^ 2 ≤ H.time 0 := by rw [htime, sub_self, H.time_zero]
  have hkt : H.time 0 ≤ t.val := by rw [H.time_zero]; exact t.property.1
  have hprotect :
      riemannianClosedBallOf (H.stageMetric (H.activeStage t) t.val) p (σ / 2) ⊆
        riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hσ).mpr (by linarith))
  let tb := H.stageTime 0
  have hstage : H.activeStage tb = 0 := H.activeStage_stageTime 0
  have htransport (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage tb)
      (hjt : j ≤ H.activeStage t) :
      ∃ hz : p ∈ H.backwardSurvivorDomain j (H.activeStage t) hjt,
        ENNReal.ofReal (Real.exp (-27)) *
          riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.stageMetric j tb.val)
            (riemannianBallOf (H.stageMetric j tb.val)
              (H.backwardSurvivorMap j (H.activeStage t) hjt j le_rfl hjt ⟨p, hz⟩)
              (Real.exp (-9) * σ / 8)) ≤
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t.val)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p (σ / 2)) := by
    subst j
    obtain ⟨hz, _, hv⟩ := birth_ball_survives_and_volume_le_exp_of_protected_terminal_ball
      H t p 0 hσ hσ hbirth hkt hsmall p hprotect
    exact ⟨hz, hv⟩
  obtain ⟨hz, hv⟩ := htransport 0 hstage.symm (Fin.zero_le _)
  have htb : tb.val = H.time 0 := rfl
  rw [htb, H.stageMetric_initial] at hv
  have hr : 0 < Real.exp (-9) * σ / 8 := by positivity
  have hrρ : Real.exp (-9) * σ / 8 ≤ ρ := by
    have he : Real.exp (-9) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have heσ := mul_le_mul_of_nonneg_right he hσ.le
    linarith
  have hinit := hvolume
    (H.backwardSurvivorMap 0 (H.activeStage t) (Fin.zero_le _) 0 le_rfl (Fin.zero_le _) ⟨p, hz⟩)
    _ hr hrρ
  have hsub : riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p (σ / 2) ⊆
      riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p σ :=
    riemannianBallOf_mono _ _ (by linarith)
  have hbound := (mul_le_mul_right hinit (ENNReal.ofReal (Real.exp (-27)))).trans
    (hv.trans (MeasureTheory.measure_mono hsub))
  have he :
      ENNReal.ofReal (Real.exp (-27) * κ * (Real.exp (-9) / 8) ^ 3) *
        ENNReal.ofReal σ ^ 3 =
      ENNReal.ofReal (Real.exp (-27)) *
        (ENNReal.ofReal κ * ENNReal.ofReal (Real.exp (-9) * σ / 8) ^ 3) := by
    rw [ENNReal.ofReal_mul' (by positivity : 0 ≤ (Real.exp (-9) / 8) ^ 3),
      ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_pow (by positivity : 0 ≤ Real.exp (-9) / 8),
      show Real.exp (-9) * σ / 8 = (Real.exp (-9) / 8) * σ by ring,
      ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-9) / 8), mul_pow]
    ring
  have hseed := he ▸ hbound
  intro r hr hrσ
  exact H.volume_lower_bound_of_smaller_controlled_radii t p hr hrσ hsmall hseed

theorem ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_initial_time_contact
    (P : OrientedThreeStage) (g : P.Metric) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ (H : ObservedHistory) (_ : InitialIdentification P g H)
        (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {σ : ℝ},
        0 < σ → σ ≤ ρ → t.val = σ ^ 2 →
        (∀ q : ℝ, 0 < q → q < σ → H.isParabolicallyRmControlledBall t p q) →
        ∀ r : ℝ, 0 < r → r ≤ σ →
          ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
              (H.stageMetric (H.activeStage t) t.val)
              (riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p r) := by
  obtain ⟨ρ, κ, hρ, hκ, hbound⟩ :=
    Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound g
  refine ⟨ρ, (Real.exp (-27) * κ * (Real.exp (-9) / 8) ^ 3) / (8 * Real.exp 6),
    hρ, by positivity, ?_⟩
  intro H A t p σ hσ hσρ htime hsmall
  apply terminal_ball_volume_lower_of_initial_time_contact H t p hσ hσρ htime hsmall
  intro x r hr hrρ
  have hmap := Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    g (H.initialMetric 0) A.map A.map.isLocalDiffeomorph A.map.injective
    (fun y v w => (A.metric_eq y v w).symm) (A.map.symm x) r
  rw [A.map.apply_symm_apply] at hmap
  have hbound' : ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g
        (riemannianBallOf g (A.map.symm x) r) := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using
      hbound (A.map.symm x) r hr hrρ
  exact hbound'.trans hmap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
