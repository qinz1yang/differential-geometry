import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
  (K : Set G.terminalRegularOpen)

def backwardSurvivorIncomingFootprintStageMap
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    H.backwardSurvivorIncomingFootprint first last hle G K → (H.stage j).Carrier :=
  fun z => H.backwardSurvivorMap first last hle j hf hl z.val.val

theorem backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j hf hl) :=
  DifferentialGeometry.isLocalDiffeomorph_comp
    (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hf hl)
    (DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingDomain first last hle G))
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingFootprint first last hle G K)))

@[simp] theorem backwardSurvivorIncomingFootprintStageMap_last
    (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
    H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl z =
      (H.backwardSurvivorIncomingFootprintMap first last hle G K z).val :=
  H.backwardSurvivorMap_last first last hle z.val.val

theorem backwardSurvivorIncomingFootprintStageMap_crossing
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
    (H.event j).RegularCrossing
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.castSucc hf
        (j.castSucc_lt_succ.le.trans hl) z)
      (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.succ
        (hf.trans j.castSucc_lt_succ.le) hl z) :=
  H.backwardSurvivorMap_crossing first last hle j hf hl z.val.val

private theorem slabMetric_restrict_eq_localPull
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {t : ℝ} (ht : t < H.time j.succ) :
    ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
      (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K) =
      localPullMetric ((H.event j).incoming.flow.base.metric t)
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.castSucc hf
          (j.castSucc_lt_succ.le.trans hl))
        (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) := by
  rw [H.backwardSurvivorSlabMetric_before first last hle j hf hl ht,
    ← DifferentialGeometry.localPullMetric_subtype_val,
    ← DifferentialGeometry.localPullMetric_subtype_val,
    DifferentialGeometry.localPullMetric_comp,
    DifferentialGeometry.localPullMetric_comp]
  · rfl
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingDomain first last hle G))
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingFootprint first last hle G K))

private theorem incomingMetric_restrict_eq_localPull
    {t : ℝ} (ht : t < s) :
    (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
      (H.backwardSurvivorIncomingFootprint first last hle G K) =
      localPullMetric (G.flow.base.metric t)
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl)
        (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
          last hle le_rfl) := by
  rw [H.backwardSurvivorIncomingMetric_before first last hle G L ht,
    ← DifferentialGeometry.localPullMetric_subtype_val,
    ← DifferentialGeometry.localPullMetric_subtype_val,
    ← DifferentialGeometry.localPullMetric_subtype_val,
    DifferentialGeometry.localPullMetric_comp,
    DifferentialGeometry.localPullMetric_comp]
  · congr 1
    funext z
    exact (H.backwardSurvivorIncomingFootprintStageMap_last first last hle G K z).symm
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorDomain first last hle))
      (DifferentialGeometry.isLocalDiffeomorph_comp
        (DifferentialGeometry.isLocalDiffeomorph_subtype_val
          (H.backwardSurvivorIncomingDomain first last hle G))
        (DifferentialGeometry.isLocalDiffeomorph_subtype_val
          (H.backwardSurvivorIncomingFootprint first last hle G K)))
  · exact DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingDomain first last hle G))
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val
        (H.backwardSurvivorIncomingFootprint first last hle G K))


theorem lRegularizedAction_backwardSurvivorIncomingFootprintStageMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    (hmetric : ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
      S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K))
    (T a b : ℝ)
    (α : ℝ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hslab : ∀ v ∈ uIoo a b, T - v ^ 2 ∈ Ico (H.time j.castSucc) (H.time j.succ)) :
    lRegularizedAction S T α a b =
      lRegularizedAction (H.event j).incoming.flow T
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.castSucc hf
          (j.castSucc_lt_succ.le.trans hl) ∘ α) a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_uIoo
  intro v hv
  have ht := hslab v hv
  have hm := (hmetric _ ⟨ht.1, ht.2.le⟩).trans
    (slabMetric_restrict_eq_localPull H first last hle G K j hf hl ht.2)
  calc
    _ = lRegularizedLagrangian ((H.event j).incoming.flow.localPullback
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K j.castSucc hf
          (j.castSucc_lt_succ.le.trans hl))
        (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
          j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) T α v := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
      rfl
    _ = _ := lRegularizedLagrangian_localPullback _ _ _ _ (hα.mdifferentiable one_ne_zero v)

theorem lRegularizedAction_backwardSurvivorIncomingFootprintMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D)
    (hmetric : ∀ t ∈ Icc (H.time last) s,
      S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (T a b : ℝ)
    (α : ℝ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hslab : ∀ v ∈ uIoo a b, T - v ^ 2 ∈ Ico (H.time last) s) :
    lRegularizedAction S T α a b =
      lRegularizedAction G.flow T
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl ∘ α)
        a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_uIoo
  intro v hv
  have ht := hslab v hv
  have hm := (hmetric _ ⟨ht.1, ht.2.le⟩).trans
    (incomingMetric_restrict_eq_localPull H first last hle G L K ht.2)
  calc
    _ = lRegularizedLagrangian (G.flow.localPullback
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl)
        (H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K
          last hle le_rfl)) T α v := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
      rfl
    _ = _ := lRegularizedLagrangian_localPullback _ _ _ _ (hα.mdifferentiable one_ne_zero v)

private theorem integral_lRegularizedLagrangian
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hcarrier : ∀ v ∈ uIcc a b, T - v ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
  have hmap : ContinuousOn (fun v : ℝ => (T, v)) (uIcc a b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : MapsTo (fun v : ℝ => (T, v)) (uIcc a b)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := hcarrier
  exact ContinuousOn.intervalIntegrable (μ := volume)
    ((lRegularizedLagrangian_continuousOn_carrier (I := ThreeModel) (M := M) (D := D)
      S hS α hα).comp (f := fun v : ℝ => (T, v)) hmap hmaps)

theorem lRegularizedAction_incomingFootprint_eq_sum
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D)
    (hS : IsSolutionOn S)
    (hmetric : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ u ∈ Icc (H.time j.castSucc) (H.time j.succ),
        S.base.metric u = ((H.backwardSurvivorSlabMetric first last hle j hf hl u).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hcurrent : ∀ u ∈ Icc (H.time last) s,
      S.base.metric u = (H.backwardSurvivorIncomingMetric first last hle G L u).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (T : ℝ) (α : ℝ → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    {n : ℕ} (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (event : Fin n → Fin H.eventCount)
    (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last)
    (hslab : ∀ k : Fin n, ∀ v ∈ uIoo (t k.val) (t (k.val + 1)),
      T - v ^ 2 ∈ Ico (H.time (event k).castSucc) (H.time (event k).succ))
    (hhead : ∀ v ∈ uIoo 0 (t 0), T - v ^ 2 ∈ Ico (H.time last) s)
    (hcarrier : ∀ v ∈ Icc 0 (t n), T - v ^ 2 ∈ D.carrier) :
    lRegularizedAction S T α 0 (t n) =
      lRegularizedAction G.flow T
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl ∘ α)
        0 (t 0) +
      ∑ k : Fin n, lRegularizedAction (H.event (event k)).incoming.flow T
        (H.backwardSurvivorIncomingFootprintStageMap first last hle G K (event k).castSucc
          (hf k) ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α) (t k.val) (t (k.val + 1)) := by
  have hint (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) :
      IntervalIntegrable (lRegularizedLagrangian S T α) volume (t a) (t b) := by
    apply integral_lRegularizedLagrangian S hS T (t a) (t b) α hα
    intro v hv
    rw [uIcc_of_le (ht hab)] at hv
    exact hcarrier v ⟨ht0.trans ((ht (Nat.zero_le a)).trans hv.1), hv.2.trans (ht hbn)⟩
  have hint0 : IntervalIntegrable (lRegularizedLagrangian S T α) volume 0 (t 0) := by
    apply integral_lRegularizedLagrangian S hS T 0 (t 0) α hα
    intro v hv
    rw [uIcc_of_le ht0] at hv
    exact hcarrier v ⟨hv.1, hv.2.trans (ht (Nat.zero_le n))⟩
  rw [← lRegularizedAction_add S T α 0 (t 0) (t n) hint0 (hint 0 n (Nat.zero_le n) le_rfl),
    H.lRegularizedAction_backwardSurvivorIncomingFootprintMap first last hle G L K S hcurrent
      T 0 (t 0) α hα hhead]
  congr 1
  rw [← lRegularizedAction_sum S T α (fun k hk => hint k (k + 1) (by omega) hk),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact H.lRegularizedAction_backwardSurvivorIncomingFootprintStageMap first last hle G K S
    (event k) (hf k) (hl k) (hmetric (event k) (hf k) (hl k)) T (t k.val) (t (k.val + 1))
    α hα (hslab k)

theorem exists_backwardSurvivorIncomingFootprint_isSolutionOn_preserving_action
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      gflow s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
          (RealTimeInterval.closed (H.time first) s
            ((H.time_strictMono.monotone hle).trans G.lt.le))) ∧
      ∀ (α : ℝ → H.backwardSurvivorIncomingFootprint first last hle G K),
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α →
        ∀ (n : ℕ) (t : ℕ → ℝ), Monotone t → 0 ≤ t 0 →
        H.time first ≤ s - (t n) ^ 2 →
        ∀ (event : Fin n → Fin H.eventCount)
          (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last),
        (∀ k : Fin n, ∀ v ∈ uIoo (t k.val) (t (k.val + 1)),
          s - v ^ 2 ∈ Ico (H.time (event k).castSucc) (H.time (event k).succ)) →
        (∀ v ∈ uIoo 0 (t 0), s - v ^ 2 ∈ Ico (H.time last) s) →
        reducedAction gflow s ((t n) ^ 2) (squareRootReparametrization α) =
          lLength G.flow s
            (squareRootReparametrization
              (H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl ∘ α))
            0 ((t 0) ^ 2) +
          ∑ k : Fin n, lLength (H.event (event k)).incoming.flow s
            (squareRootReparametrization
              (H.backwardSurvivorIncomingFootprintStageMap first last hle G K (event k).castSucc
                (hf k) ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α))
            ((t k.val) ^ 2) ((t (k.val + 1)) ^ 2) := by
  obtain ⟨gflow, hmetric, hcurrent, hterminal, _, hsol⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_isSolutionOn first last hle G L hinit K
  refine ⟨gflow, hmetric, hcurrent, hterminal, hsol, ?_⟩
  intro α hα n t ht ht0 htime event hf hl hslab hhead
  let S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K)
      (RealTimeInterval.closed (H.time first) s
        ((H.time_strictMono.monotone hle).trans G.lt.le)) := { base := { metric := gflow } }
  have hn : 0 ≤ t n := ht0.trans (ht (Nat.zero_le n))
  have hcarrier : ∀ v ∈ Icc 0 (t n),
      s - v ^ 2 ∈ (RealTimeInterval.closed (H.time first) s
        ((H.time_strictMono.monotone hle).trans G.lt.le)).carrier := by
    intro v hv
    have hsquare : v ^ 2 ≤ (t n) ^ 2 := (sq_le_sq₀ hv.1 hn).mpr hv.2
    exact ⟨by linarith, sub_le_self _ (sq_nonneg v)⟩
  have hsum := H.lRegularizedAction_incomingFootprint_eq_sum first last hle G L K
    S hsol hmetric hcurrent s α hα t ht ht0 event hf hl hslab hhead hcarrier
  change reducedAction S.base.metric s ((t n) ^ 2) (squareRootReparametrization α) = _
  rw [reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg (t n)),
    Real.sqrt_sq hn, hsum]
  congr 1
  · simpa only [zero_pow two_ne_zero] using
      (lLength_squareRootReparametrization_sq G.flow s _ 0 (t 0) le_rfl ht0).symm
  · apply Finset.sum_congr rfl
    intro k _
    exact (lLength_squareRootReparametrization_sq (H.event (event k)).incoming.flow s _
      (t k.val) (t (k.val + 1)) (ht0.trans (ht (Nat.zero_le k.val)))
      (ht0.trans (ht (Nat.zero_le (k.val + 1))))).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.incomingFootprint_stage_maps_extendHorizon
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
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
    {t : ℝ} (ht : H.horizon < t) (hts : t < s) :
    let htstart := H.time_le_horizon.trans_lt ht
    let A := H.extendHorizon t ht.le (G.closedPrefix t htstart hts) hinit
    let X := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K
    let f : (j : A.toHistory.StageInterval first (Fin.last H.eventCount)) → X → (A.stage j.val).Carrier :=
      fun j => H.toHistory.backwardSurvivorIncomingFootprintStageMap first (Fin.last H.eventCount)
        (Fin.le_last first) G K j.val j.property.1 j.property.2
    ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
      (∀ j, Injective (f j)) ∧
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ Fin.last H.eventCount), ∀ z : X,
        (A.toHistory.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
          (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z)) ∧
      (∀ j, ∀ r ∈ Ioo (A.toHistory.regularizedStageStart t 0 j.val)
        (A.toHistory.regularizedStageEnd t (Real.sqrt (t - H.time first)) j.val),
        gflow (t - r ^ 2) = localPullMetric (A.toHistory.stageMetric j.val (t - r ^ 2)) (f j) (hf j)) := by
  intro htstart A X f
  let hf (j : A.toHistory.StageInterval first (Fin.last H.eventCount)) :
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    H.toHistory.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first (Fin.last H.eventCount)
      (Fin.le_last first) G K j.val j.property.1 j.property.2
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro j
    exact (H.toHistory.backwardSurvivorMap_injective first (Fin.last H.eventCount) (Fin.le_last first)
      j.val j.property.1 j.property.2).comp (Subtype.val_injective.comp Subtype.val_injective)
  · intro i hi hl z
    exact H.toHistory.backwardSurvivorIncomingFootprintStageMap_crossing first (Fin.last H.eventCount)
      (Fin.le_last first) G K i hi hl z
  · intro j r hr
    have hstage := A.toHistory.mapsTo_regularizedStage_Ioo t 0 (Real.sqrt (t - H.time first)) j.val hr
    have hphys_le : t - r ^ 2 ≤ t := sub_le_self _ (sq_nonneg r)
    have hphys_s : t - r ^ 2 < s := hphys_le.trans_lt hts
    by_cases hjlast : j.val = Fin.last H.eventCount
    · rcases j with ⟨j, hjfirst, hjlast'⟩
      dsimp only at hjlast
      subst j
      have hlower : H.time (Fin.last H.eventCount) ≤ t - r ^ 2 := A.toHistory.time_le_of_mem_stageDomain hstage
      have hAmetric : A.toHistory.stageMetric (Fin.last H.eventCount) (t - r ^ 2) = G.flow.base.metric (t - r ^ 2) :=
        A.toHistory.stageMetric_last_of_lt (h := htstart) _
      rw [hAmetric, hlast _ ⟨hlower, hphys_s.le⟩]
      exact ObservedHistory.incomingMetric_restrict_eq_localPull H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) G L K hphys_s
    · have hjN : j.val.val < H.eventCount := by
        have hh : j.val.val < H.eventCount + 1 := j.val.isLt
        have hn : j.val.val ≠ H.eventCount := fun h => hjlast (Fin.ext h)
        omega
      obtain ⟨i, hi⟩ : ∃ i : Fin H.eventCount, j.val = i.castSucc :=
        ⟨⟨j.val.val, hjN⟩, Fin.ext rfl⟩
      rcases j with ⟨j, hjfirst, hjlast'⟩
      dsimp only at hi
      subst j
      change t - r ^ 2 ∈ A.toHistory.stageDomain i.castSucc at hstage
      let iA : Fin A.eventCount := ⟨i.val, i.isLt⟩
      have hstageA : t - r ^ 2 ∈ A.toHistory.stageDomain iA.castSucc := hstage
      have hstage' : t - r ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        change t - r ^ 2 ∈ Ico (A.time iA.castSucc) (A.time iA.succ)
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hstageA
      have hAmetric : A.toHistory.stageMetric i.castSucc (t - r ^ 2) =
          (H.toHistory.event i).incoming.flow.base.metric (t - r ^ 2) :=
        ObservedHistory.stageMetric_castSucc_apply (H := A.toHistory) i _
      change gflow (t - r ^ 2) = localPullMetric (A.toHistory.stageMetric i.castSucc (t - r ^ 2))
        (H.toHistory.backwardSurvivorIncomingFootprintStageMap first (Fin.last H.eventCount)
          (Fin.le_last first) G K i.castSucc hjfirst hjlast') _
      rw [hAmetric, hslabs i hjfirst _ ⟨hstage'.1, hstage'.2.le⟩]
      exact ObservedHistory.slabMetric_restrict_eq_localPull H.toHistory first (Fin.last H.eventCount)
        (Fin.le_last first) G K i hjfirst (Fin.le_last _) hstage'.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_incomingFootprint_regularizedCost_minimum
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (first : Fin (H.eventCount + 1)) (K : Set G.terminalRegularOpen)
 :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc),
        ∀ v ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow v = ((H.toHistory.backwardSurvivorSlabMetric first (Fin.last H.eventCount) (Fin.le_last first)
            j hf (Fin.le_last _) v).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain first (Fin.last H.eventCount) (Fin.le_last first) G)).restrictOpen
                (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K)) ∧
      (∀ v ∈ Icc (H.time (Fin.last H.eventCount)) s,
        gflow v = (H.toHistory.backwardSurvivorIncomingMetric first (Fin.last H.eventCount)
          (Fin.le_last first) G L v).restrictOpen
            (H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K)) ∧
      ∀ (t : ℝ) (ht : H.horizon < t) (hts : t < s),
      let htstart := H.time_le_horizon.trans_lt ht
      let A := H.extendHorizon t ht.le (G.closedPrefix t htstart hts) hinit
      let X := H.toHistory.backwardSurvivorIncomingFootprint first (Fin.last H.eventCount) (Fin.le_last first) G K
      let D := RealTimeInterval.closed (H.time first) s
        ((H.time_strictMono.monotone (Fin.le_last first)).trans G.lt.le)
      let S : SolutionOn (I := ThreeModel) (M := X) D := { base := { metric := gflow } }
      let v := Real.sqrt (t - H.time first)
      let f : (j : A.toHistory.StageInterval first (Fin.last H.eventCount)) → X → (A.stage j.val).Carrier :=
        fun j => H.toHistory.backwardSurvivorIncomingFootprintStageMap first (Fin.last H.eventCount)
          (Fin.le_last first) G K j.val j.property.1 j.property.2
      ∀ (Q : Set X), IsCompact Q → ∀ (g : SmoothRiemannianMetric ThreeModel X) (μ B r : ℝ),
      0 ≤ μ → 0 < r →
      (∀ z ∈ Ioo 0 v, ∀ p ∈ Q, ∀ w : TangentSpace ThreeModel p,
        μ * g.inner p w w ≤ (gflow (t - z ^ 2)).inner p w w) →
      (∀ j : A.toHistory.StageInterval first (Fin.last H.eventCount),
        ∀ z ∈ Ioo (A.toHistory.regularizedStageStart t 0 j.val) (A.toHistory.regularizedStageEnd t v j.val),
        ∀ p : (A.stage j.val).Carrier, -B ≤ metricScalarAt (A.toHistory.stageMetric j.val (t - z ^ 2)) p) →
      ∀ x : X, x ∈ interior Q →
      (∀ z ∈ frontier Q, ENNReal.ofReal r ≤ riemannianEDistOf g x z) →
      ∀ (y : X) (γ : ℝ → X), ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ 0 = x → γ v = y →
      lRegularizedAction S t γ 0 v < μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3 →
      ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧ η v = y ∧
        MapsTo η (Icc 0 v) Q ∧ lRegularizedAction S t η 0 v ≤ lRegularizedAction S t γ 0 v ∧
        (lRegularizedAction S t η 0 v : WithTop ℝ) ∈ A.toHistory.regularizedActionValues first
          (Fin.last H.eventCount) (Fin.le_last first) t B 0 v
          (f ⟨Fin.last H.eventCount, Fin.le_last first, le_rfl⟩ x) (f ⟨first, le_rfl, Fin.le_last first⟩ y) ∧
        A.toHistory.regularizedCost first (Fin.last H.eventCount) (Fin.le_last first) t B 0 v
          (f ⟨Fin.last H.eventCount, Fin.le_last first, le_rfl⟩ x) (f ⟨first, le_rfl, Fin.le_last first⟩ y) =
            (lRegularizedAction S t η 0 v : WithTop ℝ) := by
  obtain ⟨gflow, hslabs, hlast, hterminal, hsmooth, hS⟩ :=
    H.toHistory.exists_backwardSurvivorIncomingFootprint_isSolutionOn first (Fin.last H.eventCount)
      (Fin.le_last first) G L hinit K
  refine ⟨gflow, (fun j hf v hv => hslabs j hf (Fin.le_last _) v hv), hlast, ?_⟩
  intro t ht hts htstart A X D S v f Q hQ g μ B r hμ hr hcompare hscalar x hx hfront y γ hγ hstart hend hact
  obtain ⟨hf, hinj, hcross, hmetric⟩ := H.incomingFootprint_stage_maps_extendHorizon G L hinit first K gflow
    (fun j hj v hv => hslabs j hj (Fin.le_last _) v hv) hlast ht hts
  have hfirst : H.time first < t := (H.toHistory.time_le_horizon_at first).trans_lt ht
  have hv : 0 < v := Real.sqrt_pos.mpr (sub_pos.mpr hfirst)
  have hv2 : v ^ 2 = t - H.time first := Real.sq_sqrt (sub_nonneg.mpr hfirst.le)
  have hupper : t - (0 : ℝ) ^ 2 ∈ A.toHistory.stageDomain (Fin.last H.eventCount) := by
    change t - (0 : ℝ) ^ 2 ∈ A.toHistory.stageDomain (Fin.last A.eventCount)
    simp only [zero_pow two_ne_zero, sub_zero, ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨htstart.le, le_rfl⟩
  have hlower : t - v ^ 2 ∈ A.toHistory.stageDomain first := by
    rw [hv2, sub_sub_cancel]
    exact A.toHistory.time_mem_stageDomain first
  have hclock : ∀ z ∈ Icc 0 v, t - z ^ 2 ∈ Icc (H.time first) s := by
    intro z hz
    have hz2 := (sq_le_sq₀ hz.1 hv.le).mpr hz.2
    rw [hv2] at hz2
    exact ⟨by linarith, (sub_le_self _ (sq_nonneg z)).trans hts.le⟩
  have hreg : ∀ z ∈ Ioo 0 v, t - z ^ 2 ∈ D.regular := by
    intro z hz
    have hz2 := (sq_lt_sq₀ hz.1.le hv.le).mpr hz.2
    rw [hv2] at hz2
    exact ⟨by linarith, (sub_le_self _ (sq_nonneg z)).trans_lt hts⟩
  apply A.toHistory.exists_regularizedCost_minimum_of_joint_metric_of_action_lt_compact_barrier first
    (Fin.last H.eventCount) (Fin.le_last first) f hf hinj Q hQ hcross le_rfl hv hupper hlower
    S hS (Icc (H.time first) s) Subset.rfl hclock hreg hsmooth g hμ hr hmetric hcompare hscalar
    x hx hfront y γ hγ hstart hend
  simpa only [sub_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
