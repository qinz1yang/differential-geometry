import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

private theorem intervalIntegrable_lRegularizedLagrangian
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
  have hmap : ContinuousOn (fun s : ℝ => (T, s)) (uIcc a b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : MapsTo (fun s : ℝ => (T, s)) (uIcc a b)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := hcarrier
  have hc : ContinuousOn (lRegularizedLagrangian S T α) (uIcc a b) :=
    (lRegularizedLagrangian_continuousOn_carrier (I := ThreeModel) (M := M) (D := D)
      S hS α hα).comp (f := fun s : ℝ => (T, s)) hmap hmaps
  exact ContinuousOn.intervalIntegrable (μ := volume) hc

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)

theorem backwardSurvivorSlabMetric_before
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {t : ℝ} (ht : t < H.time i.succ) :
    H.backwardSurvivorSlabMetric first last hle i hf hl t =
      localPullMetric ((H.event i).incoming.flow.base.metric t)
        (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl))
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorSlabMetric_inner,
    (H.event i).terminal.extendedMetric_before ht,
    SmoothRiemannianMetric.restrictOpen_inner, localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (H.backwardSurvivorTerminalMap first last hle i hf hl) x
  change mfderiv ThreeModel ThreeModel
      (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) x =
      mfderiv ThreeModel ThreeModel
        (H.backwardSurvivorTerminalMap first last hle i hf hl) x at hd
  rw [hd]
  rfl

theorem lRegularizedLagrangian_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T : ℝ) {α : ℝ → H.backwardSurvivorDomain first last hle} {s : ℝ}
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hs : T - s ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    lRegularizedLagrangian S T α s =
      lRegularizedLagrangian (H.event i).incoming.flow T
        (H.backwardSurvivorMap first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl) ∘ α) s := by
  let p := H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl)
  let hp := H.backwardSurvivorMap_isLocalDiffeomorph first last hle i.castSucc hf
    (i.castSucc_lt_succ.le.trans hl)
  have hm : S.base.metric (T - s ^ 2) =
      ((H.event i).incoming.flow.localPullback p hp).base.metric (T - s ^ 2) :=
    (hmetric _ ⟨hs.1, hs.2.le⟩).trans
      (H.backwardSurvivorSlabMetric_before first last hle i hf hl hs.2)
  calc
    _ = lRegularizedLagrangian ((H.event i).incoming.flow.localPullback p hp) T α s := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
    _ = _ := lRegularizedLagrangian_localPullback (H.event i).incoming.flow p hp T hα

theorem lRegularizedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T : ℝ) {α : ℝ → H.backwardSurvivorDomain first last hle}
    (a b : ℝ) (hα : ∀ s ∈ uIoo a b, MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hslab : ∀ s ∈ uIoo a b, T - s ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    lRegularizedAction S T α a b =
      lRegularizedAction (H.event i).incoming.flow T
        (H.backwardSurvivorMap first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl) ∘ α) a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_uIoo
  intro s hs
  exact H.lRegularizedLagrangian_backwardSurvivorMap first last hle S i hf hl hmetric T
    (hα s hs) (hslab s hs)

theorem sum_lRegularizedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (hS : IsSolutionOn S) (T : ℝ)
    (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    {n : ℕ} (t : ℕ → ℝ) (event : Fin n → Fin H.eventCount)
    (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last)
    (hmetric : ∀ k, ∀ u ∈ Icc (H.time (event k).castSucc) (H.time (event k).succ),
      S.base.metric u = H.backwardSurvivorSlabMetric first last hle (event k) (hf k) (hl k) u)
    (hslab : ∀ k : Fin n, ∀ s ∈ uIoo (t k.val) (t (k.val + 1)),
      T - s ^ 2 ∈ Ico (H.time (event k).castSucc) (H.time (event k).succ))
    (hcarrier : ∀ k < n, ∀ s ∈ uIcc (t k) (t (k + 1)), T - s ^ 2 ∈ D.carrier) :
    (∑ k : Fin n, lRegularizedAction (H.event (event k)).incoming.flow T
      (H.backwardSurvivorMap first last hle (event k).castSucc (hf k)
        ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α) (t k.val) (t (k.val + 1))) =
      lRegularizedAction S T α (t 0) (t n) := by
  have hint (k : ℕ) (hk : k < n) :
      IntervalIntegrable (lRegularizedLagrangian S T α) volume (t k) (t (k + 1)) := by
    exact intervalIntegrable_lRegularizedLagrangian S hS T (t k) (t (k + 1)) α hα
      (hcarrier k hk)
  calc
    _ = ∑ k : Fin n, lRegularizedAction S T α (t k.val) (t (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (H.lRegularizedAction_backwardSurvivorMap first last hle S
        (event k) (hf k) (hl k) (hmetric k) T (t k.val) (t (k.val + 1))
        (fun s _ => hα.mdifferentiable one_ne_zero s) (hslab k)).symm
    _ = lRegularizedAction S T α (t 0) (t n) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => lRegularizedAction S T α (t k) (t (k + 1))) n]
      exact lRegularizedAction_sum S T α hint

omit hle in
theorem exists_backwardSurvivor_isSolutionOn_preserving_action (hlt : first < last) :
    ∃ S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
        (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le),
      IsSolutionOn S ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
          S.base.metric t = H.backwardSurvivorSlabMetric first last hlt.le i hf hl t) ∧
      (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
        S.base.metric (H.time j) = H.backwardSurvivorInitialMetric first last hlt.le j hj hl) ∧
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (T : ℝ) (α : ℝ → H.backwardSurvivorDomain first last hlt.le),
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → ∀ a b : ℝ,
        (∀ s ∈ uIoo a b, T - s ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ)) →
        lRegularizedAction S T α a b =
          lRegularizedAction (H.event i).incoming.flow T
            (H.backwardSurvivorMap first last hlt.le i.castSucc hf
              (i.castSucc_lt_succ.le.trans hl) ∘ α) a b := by
  obtain ⟨G, hslabs, hinitial, _, hS⟩ := H.exists_backwardSurvivor_isSolutionOn first last hlt
  let S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le) :=
    { base := { metric := G } }
  refine ⟨S, hS, hslabs, hinitial, ?_⟩
  intro i hf hl T α hα a b hslab
  exact H.lRegularizedAction_backwardSurvivorMap first last hlt.le S i hf hl
    (hslabs i hf hl) T a b (fun s _ => hα.mdifferentiable one_ne_zero s) hslab

theorem reducedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T τ : ℝ) (hτ : 0 ≤ τ) (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ∀ s ∈ Ioo 0 (Real.sqrt τ), MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hslab : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      T - s ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    reducedAction S.base.metric T τ (squareRootReparametrization α) =
      reducedAction (H.event i).incoming.flow.base.metric T τ
        (squareRootReparametrization
          (H.backwardSurvivorMap first last hle i.castSucc hf
            (i.castSucc_lt_succ.le.trans hl) ∘ α)) := by
  rw [reducedAction_eq_lLength, reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ]
  exact H.lRegularizedAction_backwardSurvivorMap first last hle S i hf hl hmetric T
    0 (Real.sqrt τ) (by simpa only [uIoo_of_le (Real.sqrt_nonneg τ)] using hα)
    (by simpa only [uIoo_of_le (Real.sqrt_nonneg τ)] using hslab)

theorem reducedAction_eq_sum_stage_lLength
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (hS : IsSolutionOn S) (T τ : ℝ) (hτ : 0 ≤ τ)
    (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    {n : ℕ} (t : ℕ → ℝ) (ht : ∀ k ≤ n, 0 ≤ t k)
    (hzero : t 0 = 0) (hlast : t n = Real.sqrt τ) (event : Fin n → Fin H.eventCount)
    (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last)
    (hmetric : ∀ k, ∀ u ∈ Icc (H.time (event k).castSucc) (H.time (event k).succ),
      S.base.metric u = H.backwardSurvivorSlabMetric first last hle (event k) (hf k) (hl k) u)
    (hslab : ∀ k : Fin n, ∀ s ∈ uIoo (t k.val) (t (k.val + 1)),
      T - s ^ 2 ∈ Ico (H.time (event k).castSucc) (H.time (event k).succ))
    (hcarrier : ∀ k < n, ∀ s ∈ uIcc (t k) (t (k + 1)), T - s ^ 2 ∈ D.carrier) :
    reducedAction S.base.metric T τ (squareRootReparametrization α) =
      ∑ k : Fin n, lLength (H.event (event k)).incoming.flow T
        (squareRootReparametrization
          (H.backwardSurvivorMap first last hle (event k).castSucc (hf k)
            ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α))
        ((t k.val) ^ 2) ((t (k.val + 1)) ^ 2) := by
  rw [reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ,
    ← hzero, ← hlast]
  rw [← H.sum_lRegularizedAction_backwardSurvivorMap first last hle S hS T α hα
    t event hf hl hmetric hslab hcarrier]
  apply Finset.sum_congr rfl
  intro k _
  exact (lLength_squareRootReparametrization_sq (H.event (event k)).incoming.flow T _
    (t k.val) (t (k.val + 1)) (ht k.val k.isLt.le) (ht (k.val + 1) k.isLt)).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
