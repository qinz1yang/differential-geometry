import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowStandardComparison

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

theorem exists_capWindow_embedding_standard_close (C : ℝ≥0) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (Dw D₂ ε : ℝ), 0 < Dw → Dw < D₂ → 0 < ε →
    ∃ R : ℝ, D₂ + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i b, qcan ≤ Cbirth * ((records i).static b).neck.scale ∧
        1 ≤ a₀ * ((records i).static b).neck.scale) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ w : (H.stage k).Carrier, H.CapWindowPoint records k w t Dw (1 / 2) →
    ∃ (Ξ : standardCapWindow D₂ → (H.stage k).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (i : Fin H.eventCount) (b : (H.toHistory.event i).RetainedBoundaryIndex)
        (Q : StandardSolution) (τw : ℝ), τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
          metricDerivNorm m
            (localPullMetric (scaleMetric ((records i).static b).neck.scale
              ((records i).static b).neck.scale_pos (Gk.flow.base.metric t)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < ε := by
  obtain ⟨Pb, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} (1 / 2) C (by norm_num) (by norm_num)
  refine ⟨Cbirth, hCbirth, ?_⟩
  intro Dw D₂ ε hDw hD₂ hε
  obtain ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, -, hδ₀, hwin⟩ :=
    hbridge D₂ ε ε (hDw.trans hD₂) hε hε 2
  refine ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, ?_⟩
  intro H p₀ δbound ρbound p records hrec hδb hRp hmp hζp qcan a₀ hqcan hHI hlow hbirth
    k s Gk hGk hderiv t hkt hts hcur w hcap
  obtain ⟨j, hl, A, b, x, hanchor, hxD, hage⟩ := hcap
  obtain ⟨hb1, hb2⟩ := hbirth j b
  have hxD' : ‖x.val‖ < D₂ + 1 := by linarith
  obtain ⟨G, L, hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, -, -, hS5, -, -, Q, -, hclose⟩ :=
    hwin H p₀ δbound ρbound records hrec hδb hRp hmp hζp qcan a₀ (1 / 2) hqcan le_rfl hHI hlow
      k s Gk hGk hderiv t hkt hts hcur j hl w A b x hanchor hage hxD' hb1 hb2
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm (1 / 2 : ℝ), ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  refine ⟨fun v => (Ξ v).val.val,
    H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ, z,
    H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
      hΞs.isEmbedding.injective, congrArg Subtype.val hΞmark, by rw [hzx]; exact hxD,
    j, b, Q, T, ⟨hT0, hTθ⟩, ?_⟩
  intro u m hm
  have h := (hclose T hTmem).2 m hm u
  rwa [hST] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
