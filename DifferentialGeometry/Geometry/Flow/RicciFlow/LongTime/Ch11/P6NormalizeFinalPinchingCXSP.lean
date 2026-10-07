import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchRescaleP6X2

set_option autoImplicit false

/-!
# CX-SPINE G4：整史归一化后的 event 与 final-extension 共同 pinching

P6PinchRescaleP6X2 已生产 event slabs 的固定 Φ。本文件从同一初始 HI 和 records
将 HI 传播到最后 stage 的初始 metric，再沿实际 incoming extension 传播。
重标度年龄 a₀/c+t≥1 支付同一个 Φ；Φ 在 history、c、endpoint 和窗口之前固定。
不把 event-only 结论当作 final slab 的供给，也不要求原尺度基点曲率趋无穷。
-/

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 同一个 admissible Φ 同时控制重标度 history 的 events 与任意真实 final extension。 -/
theorem exists_rescaled_history_extension_pinching_CXSP :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (K : RetainedCoreHistory.{u}) (c : ℝ) (hc : 0 < c) (pF : CutoffParameters),
        (∀ i, GeometricCutoffRecord K.toHistory i pF) →
      ∀ (a₀ : ℝ), 0 < a₀ →
        (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x ∧
          -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ (T₀ : ℝ), 1 ≤ T₀ → ∀ i : Fin K.eventCount,
        Perelman.PhiAlmostNonnegative ((K.rescale_P6N c hc).toHistory.event i).incoming.flow
          (Ico ((K.rescale_P6N c hc).time i.castSucc) ((K.rescale_P6N c hc).time i.succ) ∩
            Ici T₀) Phi) ∧
      ∀ {s : ℝ} (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
        G.flow.base.metric (K.time (Fin.last K.eventCount)) =
          K.initialMetric (Fin.last K.eventCount) →
      ∀ (T₀ : ℝ), 1 ≤ T₀ →
        Perelman.PhiAlmostNonnegative (G.rescale c hc).flow
          (Ico (K.time (Fin.last K.eventCount) / c) (s / c) ∩ Ici T₀) Phi := by
  obtain ⟨Phi, hPhi, hphi⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      (a₀ := 1) one_pos
  refine ⟨Phi, hPhi, ?_⟩
  intro K c hc pF records a₀ ha₀ hHI
  constructor
  · intro T₀ hT₀ i
    exact K.toHistory.phiAlmostNonnegative_rescale_P6X2 hphi hc records ha₀ hHI hT₀ i
  · intro s G hinit T₀ hT₀
    have hhistory := K.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records ha₀
      (fun x => (hHI x).1) (fun x => (hHI x).2)
    have hstart : K.time (Fin.last K.eventCount) ∈
        K.toHistory.stageDomain (Fin.last K.eventCount) := by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_last] using
        (show K.time (Fin.last K.eventCount) ∈
          Icc (K.time (Fin.last K.eventCount)) K.horizon from ⟨le_rfl, K.time_le_horizon⟩)
    have hstage (x : (K.stage (Fin.last K.eventCount)).Carrier) :
        InFixedHamiltonIveyRegion (K.initialMetric (Fin.last K.eventCount))
          (a₀ + K.time (Fin.last K.eventCount)) x ∧
        -3 / (a₀ + K.time (Fin.last K.eventCount)) ≤
          metricScalarAt (K.initialMetric (Fin.last K.eventCount)) x := by
      simpa only [K.toHistory.stageMetric_initial] using
        hhistory.1 (Fin.last K.eventCount) (K.time (Fin.last K.eventCount)) hstart x
    have hage : 0 < a₀ + K.time (Fin.last K.eventCount) := by
      linarith [K.toHistory.time_nonneg (Fin.last K.eventCount)]
    have hfuture := G.fixedHamiltonIveyRegion_and_scalar_lower hage
      (fun x => by rw [hinit]; exact (hstage x).1)
      (fun x => by
        change -3 / (a₀ + K.time (Fin.last K.eventCount)) ≤
          metricScalarAt (G.flow.base.metric (K.time (Fin.last K.eventCount))) x
        rw [hinit]
        exact (hstage x).2)
    refine hphi _ _ (G.rescale c hc).flow _ (fun t => a₀ / c + t) ?_ ?_
    · intro t ht
      have hlo : T₀ ≤ t := ht.2
      have hpos : 0 < a₀ / c := div_pos ha₀ hc
      linarith
    · intro t ht x
      rw [OrientedThreeStage.IncomingSlab.rescale_metric,
        inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M hc]
      have hlo : K.time (Fin.last K.eventCount) / c ≤ t := ht.1.1
      have hhi : t < s / c := ht.1.2
      rw [div_le_iff₀ hc] at hlo
      rw [lt_div_iff₀ hc] at hhi
      have hct : c * t ∈ Ico (K.time (Fin.last K.eventCount)) s :=
        ⟨by linarith, by linarith⟩
      have h := (hfuture (c * t) hct x).1
      have heq : a₀ + K.time (Fin.last K.eventCount) + c * t -
          K.time (Fin.last K.eventCount) = c * (a₀ / c + t) := by
        field_simp
        ring
      rw [← heq]
      exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
