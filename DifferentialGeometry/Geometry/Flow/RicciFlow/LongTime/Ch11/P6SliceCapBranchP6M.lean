import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSliceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

/-!
# 窗口切片二分的 cap-window 分支（O-CH11-P6ANCH G2p，后缀 `_P6M`）

G2 / G2v / G2w 的切片二分前提的第二条（CWP 点有标准帽嵌入）在 event slab 切片上由树内
`RetainedCoreHistory.exists_capWindow_embedding_standard_close`（`ST/CapWindowSliceComparison:17`）给出：
取 `CWP w := K.CapWindowPoint records e.castSucc w v Dw (1/2)`、切片度量
`K.toHistory.stageMetric e.castSucc v`（= incoming slab `e` 的度量，`stageMetric_castSucc_apply`），
`lam :=` record 的 neck scale。数据前提（canonical family、参数小性、初始 Hamilton–Ivey、birth 比较、
slab 导数界）与树内引理逐字。剩下的非 CWP 分支（SLT 窗口版在 `(v, w)`）仍显式。
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

/-- **`_P6M`（切片二分 CWP 分支，event slab 切片形）**：树内 cap-window 嵌入引理的切片度量改写版。 -/
theorem RetainedCoreHistory.capWindow_branch_of_records_P6M (C : ℝ≥0) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (Dw D₂ η : ℝ), 0 < Dw → Dw < D₂ → 0 < η →
    ∃ Rr : ℝ, D₂ + 1 < Rr ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ 0 < δ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
      K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → Rr ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i b, qcan ≤ Cbirth * ((records i).static b).neck.scale ∧
        1 ≤ a₀ * ((records i).static b).neck.scale) →
    ∀ (e : Fin K.eventCount), K.EventSlabsDerivative C qcan e.castSucc →
    ∀ v : ℝ, K.time e.castSucc < v → v < K.time e.succ →
      (K.toHistory.event e).incoming.DerivativeBoundBefore C qcan v →
    ∀ w : (K.stage e.castSucc).Carrier, K.CapWindowPoint records e.castSucc w v Dw (1 / 2) →
    ∃ (Ξ : standardCapWindow D₂ → (K.stage e.castSucc).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
        τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
          metricDerivNorm m (localPullMetric (scaleMetric lam hlam
              (K.toHistory.stageMetric e.castSucc v)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η := by
  obtain ⟨Cbirth, hCbirth, hP⟩ :=
    RetainedCoreHistory.exists_capWindow_embedding_standard_close.{u} C
  refine ⟨Cbirth, hCbirth, fun Dw D₂ η hDw hD₂ hη => ?_⟩
  obtain ⟨Rr, hRr, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, hP'⟩ := hP Dw D₂ η hDw hD₂ hη
  refine ⟨Rr, hRr, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, ?_⟩
  intro K p₀ δb ρb p records hrec hδ hR hm hζ qcan a₀ hq hHI hlow hbirth e hslab v hv1 hv2 hder
    w hcw
  have h := hP' K p₀ δb ρb records hrec hδ hR hm hζ qcan a₀ hq hHI hlow hbirth e.castSucc
    (K.time e.succ) (K.toHistory.event e).incoming (K.event_initial e) hslab v hv1 hv2 hder w hcw
  obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, b, Q, τw, hτw, hcl⟩ := h
  rw [ObservedHistory.stageMetric_castSucc_apply]
  exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩

/-- consumer（常数层）：CWP 分支的常数 `Cbirth`、`Rr > D₂ + 1` 在 history 之前取（与 G2 / G2w 的
`D₂ ≥ Dcap + 1 + …` 同序）。 -/
example (C : ℝ≥0) : ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (Dw D₂ η : ℝ), 0 < Dw → Dw < D₂ → 0 < η → ∃ Rr : ℝ, D₂ + 1 < Rr := by
  obtain ⟨Cb, hCb, h⟩ := RetainedCoreHistory.capWindow_branch_of_records_P6M.{0} C
  exact ⟨Cb, hCb, fun Dw D₂ η h1 h2 h3 => (h Dw D₂ η h1 h2 h3).imp fun _ hR => hR.1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
