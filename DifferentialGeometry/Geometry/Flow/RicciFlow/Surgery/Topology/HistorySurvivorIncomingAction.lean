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
