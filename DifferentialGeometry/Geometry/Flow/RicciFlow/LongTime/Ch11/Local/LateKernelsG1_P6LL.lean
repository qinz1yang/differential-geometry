import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingDepthLate_P6LL

/-!
# G1 汇总 + consumer（O-CH11-P6LATE G1，`_P6LL`）

G1 的三处 `_late` 局部化副本（P6ANCH2 设计段 (ii)）：
* (1) `RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_late_P6LL`
  （`Local/CrossingTracedLate_P6LL`，`hsurvive` 核心）；
* (2) `depthExtendable_add_of_windowAnchorBound_late_P6LL`（`Local/CrossingDepthLate_P6LL`，
  `hextend`）；
* (3) `RetainedCoreHistory.exists_capWindow_embedding_standard_close_late_P6LL`
  （`Local/CapWindowStdCompLate_P6LL`，G2p）；
底层：`Local/CapWindowAgeBoundLate_P6LL`、`Local/TracedOrCapLate_P6LL`（B5 链）。

consumer：原 G2p（full family 形）⇐ (3)（`T₀ = 0`、`recordsF = records`、late 展开形 CWP ⇐
`CapWindowPoint`），即 late 形严格推广 full 形。
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

/-- consumer：`CapWindowSliceComparison:17` 的原陈述（full family）由 (3) 的 late 版给出。 -/
example (C : ℝ≥0) :
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
  obtain ⟨Cbirth, hCb, hB⟩ := exists_capWindow_embedding_standard_close_late_P6LL.{u} C
  refine ⟨Cbirth, hCb, fun Dw D₂ ε hDw hD₂ hε => ?_⟩
  obtain ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, hB⟩ := hB Dw D₂ ε hDw hD₂ hε
  refine ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, ?_⟩
  intro H p₀ δbound ρbound p records hrec hδb hRp hmp hζp qcan a₀ hqcan hHI hlow hbirth
    k s Gk hGk hderiv t hkt hts hcur w hcap
  obtain ⟨-, hrad, hord, hacc, -, hcan, hdel, -⟩ := hrec
  obtain ⟨j, hl, A, b, x, h1, h2, h3⟩ := hcap
  obtain ⟨Ξ, hΞ, z₀, hinj, hz, hzn, i, -, b', Q, τw, hτ, hclose⟩ :=
    hB H (T₀ := 0) (fun i _ => records i) (fun i _ b => hcan i b) (hrad ▸ hRp) (hord ▸ hmp)
      (hacc ▸ hζp) records δbound (fun i _ => hdel i) hδb qcan a₀ hqcan hHI hlow
      (fun i _ b => hbirth i b) k s Gk hGk hderiv t hkt hts hcur w
      ⟨j, H.toHistory.time_nonneg _, hl, A, b, x, h1, h2, h3⟩
  exact ⟨Ξ, hΞ, z₀, hinj, hz, hzn, i, b', Q, τw, hτ, hclose⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
