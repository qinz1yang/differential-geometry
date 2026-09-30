import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckTrigger

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (SpatialNeck)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable (H : RetainedCoreHistory.{u})

theorem exists_currentSlab_stronglyCanonicalBefore {ε ε₁ C1 C2 qcan : ℝ}
    (hclass : H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount))
    (v : Icc (0 : ℝ) H.toHistory.horizon)
    (hterm : H.toHistory.activeStage v = Fin.last H.eventCount →
      ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
          (H.time (H.toHistory.activeStage v)) s),
        (v : ℝ) < s ∧
        (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
          G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
        H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s) :
    ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
        (H.time (H.toHistory.activeStage v)) s),
      (v : ℝ) < s ∧
      (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
        G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
      H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s := by
  by_cases hl : H.toHistory.activeStage v = Fin.last H.eventCount
  · exact hterm hl
  · obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hl
    have hmem := H.toHistory.activeStage_mem v
    rw [← hj] at hmem ⊢
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
    refine ⟨H.time j.succ, (H.toHistory.event j).incoming, hmem.2, ?_,
      hclass j (Fin.castSucc_lt_last j)⟩
    intro τ _
    exact (ObservedHistory.stageMetric_castSucc_apply j τ).symm

theorem exists_tolerance_hasStrongNeckAt_of_spatialNeck (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (H : RetainedCoreHistory.{u}) {ε ε₁ eps qcan : ℝ},
      ε ≤ 1 / 1000 → eps ≤ eta →
      H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount) →
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt v).Carrier),
        H.time (H.toHistory.activeStage v) < v →
        (H.toHistory.activeStage v = Fin.last H.eventCount →
          ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
              (H.time (H.toHistory.activeStage v)) s),
            (v : ℝ) < s ∧
            (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
              G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
            H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s) →
        qcan < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p →
        Nonempty (SpatialNeck (H.toHistory.stageMetric (H.toHistory.activeStage v) v) eps p) →
        H.toHistory.HasStrongNeckAt ε₁ v p := by
  obtain ⟨eta, heta, htrig⟩ := exists_tolerance_historyStrongNeck_of_spatialNeck.{u} C1 C2
  refine ⟨eta, heta, ?_⟩
  intro H ε ε₁ eps qcan hε heps hclass v p hev hterm hq hnk
  obtain ⟨s, G, hvs, hG, hbefore⟩ := H.exists_currentSlab_stronglyCanonicalBefore hclass v hterm
  have hGv : G.flow.base.metric v = H.toHistory.stageMetric (H.toHistory.activeStage v) v :=
    hG v ⟨(H.toHistory.activeStage_time_le v), le_rfl⟩
  have hq' : qcan < G.flow.scalar v p := by
    change qcan < metricScalarAt (G.flow.base.metric v) p
    rw [hGv]
    exact hq
  have hnk' : Nonempty (SpatialNeck (G.flow.base.metric v) eps p) := by
    rw [hGv]
    exact hnk
  exact ⟨s, G, hvs, hG,
    htrig H _ G hε (hbefore p v ⟨hev, hvs⟩ hq') heps hnk'⟩

theorem exists_tolerance_isTracedRegion_of_spatialNecks (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (H : RetainedCoreHistory.{u}) {phi : ℝ → ℝ},
      Perelman.AdmissiblePinchingFunction phi → H.EventSlabsPinched phi →
    ∀ {ε ε₁ eps qcan : ℝ}, ε ≤ 1 / 1000 → eps ≤ eta → ε₁ ≤ 1 / 30000 →
      H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last H.eventCount) →
    ∀ {t : Icc (0 : ℝ) H.toHistory.horizon},
      (H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) →
      H.time (H.toHistory.activeStage t) < t →
    ∀ {p : (H.toHistory.stageAt t).Carrier} {ρ T Qlow Qup L : ℝ}, 0 < ρ → 0 ≤ T →
      T ≤ (t : ℝ) → 0 < L → qcan < L →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
        Qlow ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x) →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ Qup) →
      L ≤ Qlow * (3 / 4) ^ ⌈10 * Qup * T⌉₊ →
      (∀ v : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) - T ≤ v → v ≤ t →
        H.time (H.toHistory.activeStage v) < v →
        H.toHistory.activeStage v = Fin.last H.eventCount →
          ∃ (s : ℝ) (G : (H.stage (H.toHistory.activeStage v)).IncomingSlab
              (H.time (H.toHistory.activeStage v)) s),
            (v : ℝ) < s ∧
            (∀ τ ∈ Icc (H.time (H.toHistory.activeStage v)) (v : ℝ),
              G.flow.base.metric τ = H.toHistory.stageMetric (H.toHistory.activeStage v) τ) ∧
            H.StronglyCanonicalBefore (H.toHistory.activeStage v) G ε ε₁ C1 C2 qcan s) →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ρ,
        ∀ v : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) - T ≤ v → ∀ hvt : v ≤ t,
        H.time (H.toHistory.activeStage v) < v →
        ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage v)
            (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hvt) x,
          L ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)) →
          Nonempty (SpatialNeck (H.toHistory.stageMetric (H.toHistory.activeStage v) v) eps
            (B.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)))) →
      H.toHistory.isTracedRegion t p ρ (T + (10 * Qup)⁻¹)
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * max Qup 1) := by
  obtain ⟨eta, heta, hsup⟩ := exists_tolerance_hasStrongNeckAt_of_spatialNeck.{u} C1 C2
  refine ⟨eta, heta, ?_⟩
  intro H phi hphi hpinch ε ε₁ eps qcan hε heps hε₁ hclass t hlast htop p ρ T Qlow Qup L
    hρ hT hTt hL0 hqL hlow hup hL hterm hfine
  apply H.isTracedRegion_of_hasStrongNeckAt hphi hpinch hlast htop hρ hT hTt hε₁ hL0 hlow hup hL
  intro x hx v hav hvt hev B hB
  exact hsup H hε heps hclass v _ hev (hterm v hav hvt hev) (hqL.trans_le hB)
    (hfine x hx v hav hvt hev B hB)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
