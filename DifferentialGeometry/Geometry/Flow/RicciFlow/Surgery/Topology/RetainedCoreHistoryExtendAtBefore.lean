import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryHorizonExtension

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

theorem stageMetric_activeStage_extendHorizon_eq (H : RetainedCoreHistory.{u}) {T₁ T₂ : ℝ}
    (hT₁ : H.horizon ≤ T₁) (hT₂ : H.horizon ≤ T₂)
    (S₁ : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T₁)
    (S₂ : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T₂)
    (hS₁ : S₁.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hS₂ : S₂.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) (min T₁ T₂),
      S₁.flow.base.metric τ = S₂.flow.base.metric τ)
    (v : Icc (0 : ℝ) (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.horizon) (hv : (v : ℝ) ≤ T₂) :
    (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageMetric
        ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage v) v =
      (H.extendHorizon T₂ hT₂ S₂ hS₂).toHistory.stageMetric
        ((H.extendHorizon T₂ hT₂ S₂ hS₂).toHistory.activeStage ⟨v, v.2.1, hv⟩) v := by
  have hlow := (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage_time_le v
  change (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageMetric
      ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage v) v =
    (H.extendHorizon T₂ hT₂ S₂ hS₂).toHistory.stageMetric
      ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage v) v
  generalize (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage v = k at hlow ⊢
  cases k using Fin.lastCases with
  | last =>
    exact (H.stageMetric_extendHorizon_last_of_mem_Icc hT₁ S₁ hS₁ ⟨hlow, v.2.2⟩).trans
      ((hagree v ⟨hlow, le_min v.2.2 hv⟩).trans
        (H.stageMetric_extendHorizon_last_of_mem_Icc hT₂ S₂ hS₂ ⟨hlow, hv⟩).symm)
  | cast i =>
    unfold ObservedHistory.stageMetric
    erw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    rfl

theorem isParabolicallyRmControlledBall_extendHorizon_of_agree (H : RetainedCoreHistory.{u})
    {T₁ T₂ : ℝ} (hT₁ : H.horizon ≤ T₁) (hT₂ : H.horizon ≤ T₂)
    (S₁ : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T₁)
    (S₂ : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T₂)
    (hS₁ : S₁.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hS₂ : S₂.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) (min T₁ T₂),
      S₁.flow.base.metric τ = S₂.flow.base.metric τ)
    (v : Icc (0 : ℝ) (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.horizon) (hv : (v : ℝ) ≤ T₂)
    (p : ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageAt v).Carrier) (r : ℝ)
    (hball : (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.isParabolicallyRmControlledBall v p r) :
    (H.extendHorizon T₂ hT₂ S₂ hS₂).toHistory.isParabolicallyRmControlledBall ⟨v, v.2.1, hv⟩ p
      r := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  have hav : (a : ℝ) ≤ T₂ := (show (a : ℝ) ≤ v from hat).trans hv
  refine ⟨hr, ⟨a, a.2.1, hav⟩, hat, ha, fun x hx => ?_⟩
  have hx' : x ∈ riemannianBallOf ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageMetric
      ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage v) v) p r := by
    rw [stageMetric_activeStage_extendHorizon_eq H hT₁ hT₂ S₁ S₂ hS₁ hS₂ hagree v hv]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htrace x hx'
  refine ⟨⟨A.point, A.endpoint_eq, A.crossing⟩, fun s has hst => ?_, hA2⟩
  have hsT : (s : ℝ) ≤ T₁ := (show (s : ℝ) ≤ v from hst).trans v.2.2
  have e := stageMetric_activeStage_extendHorizon_eq H hT₁ hT₂ S₁ S₂ hS₁ hS₂ hagree
    ⟨s, s.2.1, hsT⟩ s.2.2
  have h2 : r ^ 4 * normSq0S ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageMetric
      ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage ⟨s, s.2.1, hsT⟩)
        ((⟨s, s.2.1, hsT⟩ : Icc (0 : ℝ) (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.horizon) : ℝ))
      (A.point ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage ⟨s, s.2.1, hsT⟩)
        ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage_mono has)
        ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage_mono hst)) 4
      (metricRm04At ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.stageMetric
        ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage ⟨s, s.2.1, hsT⟩)
          ((⟨s, s.2.1, hsT⟩ : Icc (0 : ℝ) (H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.horizon) : ℝ))
        (A.point ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage ⟨s, s.2.1, hsT⟩)
          ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage_mono has)
          ((H.extendHorizon T₁ hT₁ S₁ hS₁).toHistory.activeStage_mono hst))) ≤ 1 :=
    hA1 ⟨s, s.2.1, hsT⟩ has hst
  rw [e] at h2
  exact h2

theorem isParabolicallyRmControlledBall_of_extendHorizon (H : RetainedCoreHistory.{u})
    {T' : ℝ} (hT' : H.horizon ≤ T')
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T')
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
      S.flow.base.metric τ = H.toHistory.stageMetric (Fin.last H.eventCount) τ)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ)
    (hball : (H.extendHorizon T' hT' S hS).toHistory.isParabolicallyRmControlledBall
      ⟨t.1, t.2.1, t.2.2.trans hT'⟩ p r) :
    H.toHistory.isParabolicallyRmControlledBall t p r := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  refine ⟨hr, ⟨a.1, a.2.1, (show (a : ℝ) ≤ t from hat).trans t.2.2⟩, hat, ha, fun x hx => ?_⟩
  have hx' : x ∈ riemannianBallOf ((H.extendHorizon T' hT' S hS).toHistory.stageMetric
      (H.toHistory.activeStage t) t) p r := by
    rw [H.stageMetric_extendHorizon hT' S hS hagree _ (H.toHistory.activeStage_mem t)]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htrace x hx'
  refine ⟨⟨A.point, A.endpoint_eq, A.crossing⟩, fun s has hst => ?_, hA2⟩
  have h1 := hA1 ⟨s.1, s.2.1, s.2.2.trans hT'⟩ has hst
  have e := H.stageMetric_extendHorizon hT' S hS hagree _ (H.toHistory.activeStage_mem s)
  have h2 : r ^ 4 * normSq0S ((H.extendHorizon T' hT' S hS).toHistory.stageMetric
      (H.toHistory.activeStage s) s)
      (A.point (H.toHistory.activeStage s) (H.toHistory.activeStage_mono has)
        (H.toHistory.activeStage_mono hst)) 4
      (metricRm04At ((H.extendHorizon T' hT' S hS).toHistory.stageMetric
        (H.toHistory.activeStage s) s)
        (A.point (H.toHistory.activeStage s) (H.toHistory.activeStage_mono has)
          (H.toHistory.activeStage_mono hst))) ≤ 1 := h1
  rw [e] at h2
  exact h2

theorem volume_ge_extendAt_of_terminalNoncollapsedBefore (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ (H.time (Fin.last H.eventCount)))
    (hnc : H.TerminalNoncollapsedBefore hend G hG κ ρ t₀)
    (v : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon)
    (p : ((H.extendAt hend G hG hat hts).toHistory.stageAt v).Carrier) (r : ℝ)
    (hv : (v : ℝ) < t₀) (hr : r ≤ ρ)
    (hball : (H.extendAt hend G hG hat hts).toHistory.isParabolicallyRmControlledBall v p r) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel
        ((H.extendAt hend G hG hat hts).toHistory.stageAt v).Carrier
        ((H.extendAt hend G hG hat hts).toHistory.stageMetric
          ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v)
        (riemannianBallOf ((H.extendAt hend G hG hat hts).toHistory.stageMetric
          ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) p r) := by
  by_cases hva : (v : ℝ) ≤ H.horizon
  · have hagree : ∀ τ ∈ H.toHistory.stageDomain (Fin.last H.eventCount),
        (G.closedPrefix t hat hts).flow.base.metric τ =
          H.toHistory.stageMetric (Fin.last H.eventCount) τ := by
      intro τ hτ
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last, mem_Icc] at hτ
      have hτa : τ = H.time (Fin.last H.eventCount) := le_antisymm (hτ.2.trans hend.ge) hτ.1
      subst hτa
      exact hG.trans (ObservedHistory.stageMetric_last_of_le (H := H.toHistory)
        (h := le_of_eq hend.symm) (H.time (Fin.last H.eventCount))).symm
    let w : Icc (0 : ℝ) H.horizon := ⟨v, v.2.1, hva⟩
    have hballH := H.isParabolicallyRmControlledBall_of_extendHorizon (hend ▸ hat.le)
      (G.closedPrefix t hat hts) hG hagree w p r hball
    have h1 := hH w p r (hva.trans hend.ge) hr hballH
    rw [← H.stageMetric_extendHorizon (hend ▸ hat.le) (G.closedPrefix t hat hts) hG hagree _
      (H.toHistory.activeStage_mem w)] at h1
    exact h1
  · have hva' : H.time (Fin.last H.eventCount) < v := by rw [hend]; exact lt_of_not_ge hva
    have hvs : (v : ℝ) < s := v.2.2.trans_lt hts
    have hagree : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) (min t v),
        (G.closedPrefix t hat hts).flow.base.metric τ =
          (G.closedPrefix v hva' hvs).flow.base.metric τ := fun _ _ => rfl
    have hball' := H.isParabolicallyRmControlledBall_extendHorizon_of_agree (hend ▸ hat.le)
      (hend ▸ hva'.le) (G.closedPrefix t hat hts) (G.closedPrefix v hva' hvs) hG hG hagree v
      le_rfl p r hball
    have h1 := hnc v hva' hvs hv.le ⟨v, v.2.1, le_rfl⟩ p r le_rfl hr hball'
    have hagree' : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) (min v t),
        (G.closedPrefix v hva' hvs).flow.base.metric τ =
          (G.closedPrefix t hat hts).flow.base.metric τ := fun _ _ => rfl
    rw [show (H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v =
        (H.extendHorizon v (hend ▸ hva'.le) (G.closedPrefix v hva' hvs) hG).toHistory.stageMetric
          ((H.extendHorizon v (hend ▸ hva'.le) (G.closedPrefix v hva' hvs) hG).toHistory.activeStage
            ⟨v, v.2.1, le_rfl⟩) v from
      (stageMetric_activeStage_extendHorizon_eq H (hend ▸ hva'.le) (hend ▸ hat.le)
        (G.closedPrefix v hva' hvs) (G.closedPrefix t hat hts) hG hG hagree'
        ⟨v, v.2.1, le_rfl⟩ v.2.2).symm]
    exact h1

theorem exists_spatialCanonicalWitness_extendAt_of_before (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) {ε C1 C2 q t₀ : ℝ}
    (hslab : H.EventSlabsSpatiallyCanonical ε C1 C2 q (Fin.last H.eventCount))
    (hbefore : G.SpatiallyCanonicalBefore ε C1 C2 q t₀)
    (v : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon) (hv : (v : ℝ) < t₀)
    (hvk : (H.extendAt hend G hG hat hts).toHistory.time
      ((H.extendAt hend G hG hat hts).toHistory.activeStage v) < v)
    (p : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage v)).Carrier)
    (hq : q < metricScalarAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
      ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) p) :
    ∃ W : SpatialCanonicalWitness ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) ε C1 C2 p,
      W.capTubeHasNeckChart ε := by
  have hmem := (H.extendAt hend G hG hat hts).toHistory.activeStage_mem v
  revert p hq
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage v = k at hvk hmem ⊢
  intro p hq
  cases k using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at hmem
    have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric
        (Fin.last (H.extendAt hend G hG hat hts).toHistory.eventCount) v =
          G.flow.base.metric v :=
      H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
        hmem
    rw [hmet] at hq ⊢
    exact hbefore p v ⟨hvk, hv⟩ hq
  | cast j =>
    rw [ObservedHistory.stageMetric_castSucc_apply] at hq ⊢
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
    exact hslab j (Fin.castSucc_lt_last j) p v ⟨hvk, hmem.2⟩ hq

theorem curvatureOperatorLowerBoundAt_extendAt_of_pinched (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) {phi : ℝ → ℝ}
    (hpinch : H.EventSlabsPinched phi)
    (hpG : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (v : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon)
    (x : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage v)).Carrier) :
    curvatureOperatorLowerBoundAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) x
      (metricAlgebraicCurvatureTensorAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) x)
      (phi (metricScalarAt ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage v) v) x)) := by
  have hmem := (H.extendAt hend G hG hat hts).toHistory.activeStage_mem v
  revert x
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage v = k at hmem ⊢
  intro x
  cases k using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at hmem
    have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric
        (Fin.last (H.extendAt hend G hG hat hts).toHistory.eventCount) v =
          G.flow.base.metric v :=
      H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
        hmem
    rw [hmet]
    exact hpG v ⟨hmem.1, hmem.2.trans_lt hts⟩ x
  | cast j =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
    exact hpinch j v hmem x

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
