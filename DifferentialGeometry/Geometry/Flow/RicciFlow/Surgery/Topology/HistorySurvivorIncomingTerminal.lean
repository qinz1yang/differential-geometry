import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open private slabMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

theorem exists_backwardSurvivorIncomingFootprint_interior_endpoint
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (K : Set G.terminalRegularOpen)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {τ : ℝ} (hτ : τ ∈ Ioo (H.time j.castSucc) (H.time j.succ)) :
    ∃ (J : (H.stage j.castSucc).IncomingSlab (H.time j.castSucc) τ)
      (L : J.TerminalLimitMetric)
      (Ψ : H.backwardSurvivorIncomingFootprint first last hle G K → J.terminalRegularOpen)
      (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ),
      (∀ t, J.flow.base.metric t = (H.event j).incoming.flow.base.metric t) ∧
      J.flow.base.metric (H.time j.castSucc) = H.initialMetric j.castSucc ∧
      J.terminalRegularRegion = univ ∧
      L.metric = ((H.event j).incoming.flow.base.metric τ).restrictOpen J.terminalRegularOpen ∧
      Function.Injective Ψ ∧
      (∀ z, (Ψ z).val = H.backwardSurvivorIncomingFootprintStageMap
        first last hle G K j.castSucc hf (j.castSucc_lt_succ.le.trans hl) z) ∧
      localPullMetric L.metric Ψ hΨ =
        ((H.backwardSurvivorSlabMetric first last hle j hf hl τ).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let P := H.stage j.castSucc
  let S := (H.event j).incoming.closedPrefix τ hτ.1 hτ.2
  let J := S.restrictIncoming le_rfl S.lt le_rfl
  let L := S.endpointTerminalLimitMetric P
  have hregular : J.terminalRegularRegion = univ := S.terminalRegularRegion_eq_univ P
  let f := H.backwardSurvivorIncomingFootprintStageMap
    first last hle G K j.castSucc hf (j.castSucc_lt_succ.le.trans hl)
  have hfLocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph
      first last hle G K j.castSucc hf (j.castSucc_lt_succ.le.trans hl)
  have hfmem (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
      f z ∈ J.terminalRegularOpen := by
    change f z ∈ J.terminalRegularRegion
    rw [hregular]
    trivial
  let Ψ : H.backwardSurvivorIncomingFootprint first last hle G K → J.terminalRegularOpen :=
    fun z => ⟨f z, hfmem z⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ :=
    fun z => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hfmem (hfLocal z)
  refine ⟨J, L, Ψ, hΨ, fun _ => rfl, H.event_initial j, hregular, rfl, ?_,
    fun _ => rfl, ?_⟩
  · intro z w hzw
    have hz : z.val.val = w.val.val :=
      H.backwardSurvivorMap_injective first last hle j.castSucc hf
        (j.castSucc_lt_succ.le.trans hl) (congrArg Subtype.val hzw)
    exact Subtype.ext (Subtype.ext hz)
  · have hpull : localPullMetric L.metric Ψ hΨ =
        localPullMetric ((H.event j).incoming.flow.base.metric τ) f hfLocal := by
      apply SmoothRiemannianMetric.ext_inner
      intro z v w
      rw [localPullMetric_inner, localPullMetric_inner]
      change ((H.event j).incoming.flow.base.metric τ).inner (f z)
        (mfderiv ThreeModel ThreeModel Ψ z v) (mfderiv ThreeModel ThreeModel Ψ z w) = _
      have hd : mfderiv ThreeModel ThreeModel Ψ z = mfderiv ThreeModel ThreeModel f z :=
        (DifferentialGeometry.mfderiv_subtypeVal_comp Ψ z).symm
      rw [hd]
      rfl
    exact hpull.trans (slabMetric_restrict_eq_localPull H first last hle G K j hf hl hτ.2).symm

open private incomingMetric_restrict_eq_localPull from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingAction

theorem exists_backwardSurvivorIncomingFootprint_final_interior_endpoint
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s)
    (K : Set G.terminalRegularOpen)
    {τ : ℝ} (hτ : τ ∈ Ioo (H.time last) s) :
    ∃ (J : (H.stage last).IncomingSlab (H.time last) τ)
      (L : J.TerminalLimitMetric)
      (Ψ : H.backwardSurvivorIncomingFootprint first last hle G K → J.terminalRegularOpen)
      (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ),
      (∀ t, J.flow.base.metric t = G.flow.base.metric t) ∧
      J.terminalRegularRegion = univ ∧
      L.metric = (G.flow.base.metric τ).restrictOpen J.terminalRegularOpen ∧
      Function.Injective Ψ ∧
      (∀ z, (Ψ z).val = (H.backwardSurvivorIncomingFootprintMap first last hle G K z).val) ∧
      ∀ L₀ : G.TerminalLimitMetric, localPullMetric L.metric Ψ hΨ =
        (H.backwardSurvivorIncomingMetric first last hle G L₀ τ).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let P := H.stage last
  let S := G.closedPrefix τ hτ.1 hτ.2
  let J := S.restrictIncoming le_rfl S.lt le_rfl
  let L := S.endpointTerminalLimitMetric P
  have hregular : J.terminalRegularRegion = univ := S.terminalRegularRegion_eq_univ P
  let f := H.backwardSurvivorIncomingFootprintStageMap first last hle G K last hle le_rfl
  have hfLocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    H.backwardSurvivorIncomingFootprintStageMap_isLocalDiffeomorph first last hle G K last hle le_rfl
  have hfmem (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
      f z ∈ J.terminalRegularOpen := by
    change f z ∈ J.terminalRegularRegion
    rw [hregular]
    trivial
  let Ψ : H.backwardSurvivorIncomingFootprint first last hle G K → J.terminalRegularOpen :=
    fun z => ⟨f z, hfmem z⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ :=
    fun z => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hfmem (hfLocal z)
  have hmap (z : H.backwardSurvivorIncomingFootprint first last hle G K) :
      (Ψ z).val = (H.backwardSurvivorIncomingFootprintMap first last hle G K z).val :=
    H.backwardSurvivorIncomingFootprintStageMap_last first last hle G K z
  refine ⟨J, L, Ψ, hΨ, fun _ => rfl, hregular, rfl, ?_, hmap, ?_⟩
  · intro z w hzw
    apply H.backwardSurvivorIncomingFootprintMap_injective first last hle G K
    apply Subtype.ext
    exact (hmap z).symm.trans ((congrArg Subtype.val hzw).trans (hmap w))
  · intro L₀
    have hpull : localPullMetric L.metric Ψ hΨ =
        localPullMetric (G.flow.base.metric τ) f hfLocal := by
      apply SmoothRiemannianMetric.ext_inner
      intro z v w
      rw [localPullMetric_inner, localPullMetric_inner]
      change (G.flow.base.metric τ).inner (f z)
        (mfderiv ThreeModel ThreeModel Ψ z v) (mfderiv ThreeModel ThreeModel Ψ z w) = _
      have hd : mfderiv ThreeModel ThreeModel Ψ z = mfderiv ThreeModel ThreeModel f z :=
        (DifferentialGeometry.mfderiv_subtypeVal_comp Ψ z).symm
      rw [hd]
      rfl
    exact hpull.trans (incomingMetric_restrict_eq_localPull H first last hle G L₀ K hτ.2).symm


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
