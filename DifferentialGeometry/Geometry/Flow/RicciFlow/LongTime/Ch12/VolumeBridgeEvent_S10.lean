import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeSmooth_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {P Q : OrientedThreeStage.{u}}

private local instance sigmaCompactTRO_S10 {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem solution_scalar_eq_S10 {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (t : ℝ) (x : P.Carrier) :
    S.scalar t x = metricScalarAt (S.base.metric t) x := by
  rfl

/-- VB-D step: normalised volume does not increase across one event, given the explicit
event input `hB` (VB-B) and `R ≥ -3/(2(t+c))` on the incoming slab. -/
theorem event_step_S10 {a s : ℝ} (E : MetricCutCapEvent P Q a s) {c : ℝ} (hc : 0 < c)
    (ha : 0 ≤ a)
    (hR : ∀ t ∈ Ioo a s, ∀ x, -(3 / (2 * (t + c))) ≤
      metricScalarAt (E.incoming.flow.base.metric t) x)
    (hB : ∃ K : Set E.incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric K) :
    (riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ).toReal / (s + c) ^ (3 / 2 : ℝ) ≤
      (riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric a) univ).toReal /
        (a + c) ^ (3 / 2 : ℝ) := by
  obtain ⟨K, hK, hKle⟩ := hB
  let S := E.incoming.flow
  have hanti := flowVolume_normalized_antitone_S10 S E.incoming.equation (c := c)
    (by exact convex_Ico a s) (by
      show interior (Ico a s) ⊆ Ioo a s
      rw [interior_Ico])
    (fun t ht => by have := ht.1; linarith)
    (fun t ht x => by rw [solution_scalar_eq_S10]; exact hR t ht x)
  have has : a < s := E.incoming.lt
  have hapos : 0 < a + c := by linarith
  have hspos : 0 < s + c := by linarith
  set B : ℝ := flowVolume_S10 S a * (a + c) ^ (-(3 / 2 : ℝ)) * (s + c) ^ (3 / 2 : ℝ) with hBdef
  have hVa : 0 ≤ flowVolume_S10 S a := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := by positivity
  have hbound : ∀ t ∈ Ioo a s, riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric t) univ ≤
      ENNReal.ofReal B := by
    intro t ht
    have hcar : t ∈ Ico a s := ⟨ht.1.le, ht.2⟩
    have h1 := hanti (show a ∈ Ico a s from ⟨le_rfl, has⟩) hcar ht.1.le
    have htpos : 0 < t + c := by linarith [ht.1]
    have h2 : flowVolume_S10 S t ≤ B := by
      have h3 : flowVolume_S10 S t = flowVolume_S10 S t * (t + c) ^ (-(3 / 2 : ℝ)) * (t + c) ^ (3 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add htpos]; simp
      rw [h3]
      have h4 : (t + c) ^ (3 / 2 : ℝ) ≤ (s + c) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow htpos.le (by linarith [ht.2]) (by norm_num)
      calc _ ≤ flowVolume_S10 S a * (a + c) ^ (-(3 / 2 : ℝ)) * (t + c) ^ (3 / 2 : ℝ) := by
            gcongr
        _ ≤ B := by rw [hBdef]; gcongr
    have hfin : riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric t) univ ≠ ⊤ :=
      (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel) (M := P.Carrier) _).measure_univ_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal h2
  have hLK := E.terminal.volume_compact_le_of_eventually_volume_le hK
    (V := ENNReal.ofReal B) (by
      filter_upwards [Ioo_mem_nhdsLT has] with t ht
      exact hbound t ht)
  have hout := hKle.trans hLK
  have hfin2 : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ ≠ ⊤ :=
    (riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := ThreeModel) (M := Q.Carrier) _).measure_univ_lt_top.ne
  have hout' := (ENNReal.toReal_le_toReal hfin2 ENNReal.ofReal_ne_top).mpr hout
  rw [ENNReal.toReal_ofReal hB0] at hout'
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hspos _)]
  have hrw : (riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric a) univ).toReal /
      (a + c) ^ (3 / 2 : ℝ) * (s + c) ^ (3 / 2 : ℝ) = B := by
    rw [hBdef, Real.rpow_neg hapos.le]
    rfl
  rw [hrw]
  exact hout'

/-- Smooth final slab: normalised volume does not increase. -/
theorem closed_slab_step_S10 {a b : ℝ} (G : P.ClosedSlab a b) {c : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hR : ∀ t ∈ Ioo a b, ∀ x, -(3 / (2 * (t + c))) ≤ metricScalarAt (G.flow.base.metric t) x) :
    (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric b) univ).toReal / (b + c) ^ (3 / 2 : ℝ) ≤
      (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ).toReal /
        (a + c) ^ (3 / 2 : ℝ) := by
  have hanti := flowVolume_normalized_antitone_S10 G.flow G.equation (c := c)
    (by exact convex_Icc a b) (by
      show interior (Icc a b) ⊆ Ioo a b
      rw [interior_Icc])
    (fun t ht => by have := ht.1; linarith)
    (fun t ht x => by rw [solution_scalar_eq_S10]; exact hR t ht x)
  have h := hanti (show a ∈ Icc a b from ⟨le_rfl, G.lt.le⟩) (show b ∈ Icc a b from ⟨G.lt.le, le_rfl⟩) G.lt.le
  have hbp : 0 < b + c := by linarith [G.lt]
  have hap : 0 < a + c := by linarith
  simp only [flowVolume_S10, Real.rpow_neg hbp.le, Real.rpow_neg hap.le] at h
  simpa [div_eq_mul_inv] using h

/-- VB-D assembly on one observed history: with the explicit per-event inputs `hB` (VB-B) and the
scalar lower bound on every smooth interval, the final volume is at most
`vol(g(0)) c^{-3/2} (T+c)^{3/2}`. -/
theorem history_volume_bound_S10 (H : ObservedHistory.{u}) {c : ℝ} (hc : 0 < c)
    (hlt : H.time (Fin.last H.eventCount) < H.horizon)
    (hRev : ∀ i : Fin H.eventCount, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hRfin : ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon, ∀ x,
      -(3 / (2 * (t + c))) ≤ metricScalarAt ((H.finalSlab hlt).flow.base.metric t) x)
    (hB : ∀ i : Fin H.eventCount, ∃ K : Set (H.event i).incoming.terminalRegularOpen, IsCompact K ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric K) :
    (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
        ((H.finalSlab hlt).flow.base.metric H.horizon) univ).toReal ≤
      (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) univ).toReal /
        c ^ (3 / 2 : ℝ) * (H.horizon + c) ^ (3 / 2 : ℝ) := by
  let u : Fin (H.eventCount + 1) → ℝ := fun j =>
    (riemannianVolumeMeasure ThreeModel (H.stage j).Carrier (H.initialMetric j) univ).toReal /
      (H.time j + c) ^ (3 / 2 : ℝ)
  have hu : Antitone u := by
    rw [Fin.antitone_iff_succ_le]
    intro i
    have h := event_step_S10 (H.event i) hc (by
        have := H.time_nonneg i.castSucc; exact this) (hRev i) (hB i)
    have e1 := H.event_output i
    have e2 := H.event_initial i
    simp only [u]
    rw [e1] at h
    rw [e2] at h
    exact h
  have hfin := closed_slab_step_S10 (H.finalSlab hlt) hc (H.time_nonneg _) hRfin
  rw [H.final_initial hlt] at hfin
  have h0 : u (Fin.last H.eventCount) ≤ u 0 := hu (Fin.zero_le _)
  have hz : u 0 = (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) univ).toReal /
      c ^ (3 / 2 : ℝ) := by
    simp [u, H.time_zero]
  have hbp : 0 < (H.horizon + c) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith [H.time_nonneg (Fin.last H.eventCount)]) _
  rw [div_le_iff₀ hbp] at hfin
  rw [← hz]
  calc _ ≤ u (Fin.last H.eventCount) * (H.horizon + c) ^ (3 / 2 : ℝ) := by
        exact hfin
    _ ≤ _ := by gcongr

end GC.LongTime.Ch12
