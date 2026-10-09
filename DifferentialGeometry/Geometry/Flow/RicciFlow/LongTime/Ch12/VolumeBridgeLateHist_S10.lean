import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeLate_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ENNReal
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO_L {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem stageMetric_castSucc_S10 (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
  unfold ObservedHistory.stageMetric
  rw [Fin.lastCases_castSucc]

/-- Late chain: start at time `T0` inside stage `k0`; only events with `T0 < time i.succ` need the
event input. -/
theorem history_late_chain_S10 (H : ObservedHistory.{u}) {c : ℝ} (hc : 0 < c)
    (hlt : H.time (Fin.last H.eventCount) < H.horizon)
    (hRev : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hRfin : ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.finalSlab hlt).flow.base.metric t) x)
    (T0 : ℝ) (hT0 : T0 < H.horizon) (k0 : Fin (H.eventCount + 1)) (hk0 : H.time k0 ≤ T0)
    (hmax : ∀ k, H.time k ≤ T0 → k ≤ k0)
    (hB : ∀ i : Fin H.eventCount, T0 < H.time i.succ →
      ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric K) :
    (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
        ((H.finalSlab hlt).flow.base.metric H.horizon) univ).toReal / (H.horizon + c) ^ (3 / 2 : ℝ) ≤
      (riemannianVolumeMeasure ThreeModel (H.stage k0).Carrier (H.stageMetric k0 T0) univ).toReal /
        (T0 + c) ^ (3 / 2 : ℝ) := by
  have hT0nn : 0 ≤ T0 := (H.time_nonneg k0).trans hk0
  have hnext : ∀ i : Fin H.eventCount, k0 = i.castSucc → T0 < H.time i.succ := by
    intro i hi
    by_contra hn
    have : i.succ ≤ k0 := hmax _ (not_lt.mp hn)
    rw [hi] at this
    exact absurd this (by simp [Fin.le_def])
  by_cases hl : k0 = Fin.last H.eventCount
  · subst hl
    have h := closed_slab_step_gen_S10 (H.finalSlab hlt) hc (H.time_nonneg _) T0 hk0 hT0
      (hRfin)
    rw [ObservedHistory.stageMetric_last_of_lt (H := H) (h := hlt) T0]
    exact h
  · -- general case
    have hstep0 : ∀ i : Fin H.eventCount, k0 = i.castSucc →
        (riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.initialMetric i.succ) univ).toReal /
            (H.time i.succ + c) ^ (3 / 2 : ℝ) ≤
          (riemannianVolumeMeasure ThreeModel (H.stage i.castSucc).Carrier (H.stageMetric i.castSucc T0) univ).toReal /
            (T0 + c) ^ (3 / 2 : ℝ) := by
      intro i hi
      subst hi
      have hnx := hnext i rfl
      have h := event_step_gen_S10 (H.event i) hc T0 hk0 hnx (H.time_nonneg _) (hRev i) (hB i hnx)
      rw [H.event_output i, stageMetric_castSucc_S10] at *
      exact h
    let Vb : ℝ := (riemannianVolumeMeasure ThreeModel (H.stage k0).Carrier (H.stageMetric k0 T0) univ).toReal /
        (T0 + c) ^ (3 / 2 : ℝ)
    let u : Fin (H.eventCount + 1) → ℝ := fun j =>
      if j ≤ k0 then Vb else
        (riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.initialMetric j) univ).toReal /
          (H.time j + c) ^ (3 / 2 : ℝ)
    have hu : Antitone u := by
      rw [Fin.antitone_iff_succ_le]
      intro i
      by_cases h1 : i.succ ≤ k0
      · have h2 : i.castSucc ≤ k0 := le_trans (Fin.castSucc_le_succ i) h1
        simp [u, h1, h2]
      · by_cases h2 : i.castSucc ≤ k0
        · have hk : k0 = i.castSucc := by
            apply le_antisymm _ h2
            rw [Fin.le_def] at h1 ⊢
            simp only [Fin.val_succ, Fin.val_castSucc] at h1 ⊢
            omega
          have h := hstep0 i hk
          simp only [u, h1, h2, if_true, if_false]
          subst hk
          exact h
        · have h3 : T0 < H.time i.castSucc := by
            by_contra hn
            exact h2 (hmax _ (not_lt.mp hn))
          have hnx : T0 < H.time i.succ := h3.trans (H.time_strictMono (Fin.castSucc_lt_succ))
          have h := event_step_S10 (H.event i) hc (H.time_nonneg _) (hRev i) (hB i hnx)
          rw [H.event_output i, H.event_initial i] at h
          simp only [u, h1, h2, if_false]
          exact h
    have h0 : u (Fin.last H.eventCount) ≤ u 0 := hu (Fin.zero_le _)
    have hz : u 0 = Vb := by simp [u, Fin.zero_le]
    have hfin := closed_slab_step_S10 (H.finalSlab hlt) hc (H.time_nonneg _) hRfin
    rw [H.final_initial hlt] at hfin
    have hlast : ¬ Fin.last H.eventCount ≤ k0 := fun h => hl (le_antisymm (Fin.le_last _) h)
    have hul : u (Fin.last H.eventCount) =
        (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
          (H.initialMetric (Fin.last H.eventCount)) univ).toReal /
          (H.time (Fin.last H.eventCount) + c) ^ (3 / 2 : ℝ) := by simp [u, hlast]
    rw [hz, hul] at h0
    exact hfin.trans h0

end GC.LongTime.Ch12
