import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNRC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSepC11SP

/-!
# O-CH11-NATIVE-SEP G4：NR 两两核的 SEP 接线（INTEGRATION，后缀 `_C11SP`，无新 binder）

`nonResurgery_pair_of_tube_sep_C11SP` = NATIVE-NR G3b `nonResurgery_pair_of_tube_C11SP` 去掉 `hSEP`：
`hSEP := fun _ => sep_of_records_C11SP …`（G3），`Dx := D + 1`（`‖x‖ < D + 1 < R ≤ modelRadius`），
`modelAccuracy ≤ ζ₀ ≤ 1/2`、`2 ≤ 4 ≤ m₀ ≤ modelOrder`。新增前提 = SEP′ 的陈述补全：(iii) `16·(B·θ) ≤ 1`、
(i) `T(e₂⁺) − T(e₁⁺) ≤ θ/Q`、(ii) `e₂` 的 record δ 小（`Csep` = SEP′ 的绝对常数，提到最前 `∃ Csep`）。
剩余显式前提 = 合同 X（开 tube `W` + 局部 Dt：`hW`/`htube`/`hderivW`/`hfinalW`，已登记）⇒ **PROVISIONAL[X]**。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

/-- **G4（PROVISIONAL[X]）**：NR 两两核，`hSEP` 已由 SEP′ 填掉；前提多 SEP′ 的陈述补全 (i)(ii)(iii)。 -/
theorem nonResurgery_pair_of_tube_sep_C11SP
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ Csep : ℝ, 0 < Csep ∧
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧ ∀ C : ℝ≥0,
    ∀ (D ε η : ℝ) (_hD : 0 < D), 0 < ε → 0 < η → ∀ _N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ B Q θ : ℝ), 0 < qcan → 0 < Q → 0 ≤ θ → 4 * (B * θ) ≤ Θ →
      16 * (B * θ) ≤ 1 →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (e₁ e₂ : Fin H.eventCount) (hl : e₁.succ ≤ e₂.castSucc)
      (t : ℝ) (_ht : t ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ))
      (y : (H.stage e₂.castSucc).Carrier) (A : BackwardPointTrace H.toHistory e₁.succ e₂.castSucc
          hl y)
      (b : (H.toHistory.event e₁).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point e₁.succ le_rfl hl = ((records e₁).static b).window x →
      t - H.time e₁.succ ≤ θ / Q →
      ((records e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records e₁).static b).neck.scale →
      1 ≤ a₀ * ((records e₁).static b).neck.scale →
    (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      p.delta (H.time i.succ) ≤ δ₀) →
    H.time e₂.succ - H.time e₁.succ ≤ θ / Q →
    (∀ α, (records e₂).delta α *
      (8 * Real.sqrt (5 * Csep) * (D + 1) + 40000 + 2 * p.recenterConstant) ≤ 1) →
    ∀ (W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier), (∀ i, IsOpen (W i)) →
      (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
        ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H.toHistory e₁.succ i hf x'),
          A'.point e₁.succ le_rfl hf ∈ ((records e₁).static b).window '' {z | ‖z.val‖ < R + 1} →
            x' ∈ W i) →
      (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
        ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
        ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
          qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2) →
      (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc → ∀ τ ∈ Ioo (H.time e₂.castSucc) t,
        qcan < (H.toHistory.event e₂).incoming.flow.scalar τ x' →
        |derivWithin (fun v => (H.toHistory.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
          C * (H.toHistory.event e₂).incoming.flow.scalar τ x' ^ 2) →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.toHistory.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.toHistory.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂) := by
  obtain ⟨Csep, hCsep, hsep⟩ := GeometricCutoffRecord.sep_of_records_C11SP.{u}
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hnr⟩ :=
    nonResurgery_pair_of_tube_C11SP.{u} Θ hΘ hΘ1
  refine ⟨Csep, hCsep, P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro C D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hnr⟩ := hnr C D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p records hcanonical hRp hmp hζp qcan a₀ B Q θ hqcan hQ hθ hBθ hB16 hHI hlow
    e₁ e₂ hl t ht y A b x hanchor hage hscale hxD hbirth haq hδloc hT2 hδ2 W hW htube hderivW
    hfinalW
  have hm2 : 2 ≤ p.modelOrder := by omega
  exact hnr H records hcanonical hRp hmp hζp qcan a₀ B Q θ hqcan hQ hθ hBθ hHI hlow
    e₁ e₂ hl t ht y A b x hanchor hage hscale hxD hbirth haq hδloc W hW htube hderivW hfinalW
    (fun _ => hsep (H := H.toHistory) records hcanonical (hζp.trans hζhalf) hm2 B Q θ (D + 1) hQ
      hθ hB16 e₁ e₂ hl y A b x hanchor hxD (hDR.trans_le hRp).le hT2 hδ2)

/-- **consumer**：`W := univ`（全局 Dt）时 G4 给出不带 `hSEP`、不带 tube 的 NR 两两核——合同 X 是唯一剩余 binder 组。 -/
example
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ Csep : ℝ, 0 < Csep ∧
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧ ∀ C : ℝ≥0,
    ∀ (D ε η : ℝ) (_hD : 0 < D), 0 < ε → 0 < η → ∀ _N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ B Q θ : ℝ), 0 < qcan → 0 < Q → 0 ≤ θ → 4 * (B * θ) ≤ Θ →
      16 * (B * θ) ≤ 1 →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (e₁ e₂ : Fin H.eventCount) (hl : e₁.succ ≤ e₂.castSucc)
      (t : ℝ) (_ht : t ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ))
      (y : (H.stage e₂.castSucc).Carrier) (A : BackwardPointTrace H.toHistory e₁.succ e₂.castSucc
          hl y)
      (b : (H.toHistory.event e₁).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point e₁.succ le_rfl hl = ((records e₁).static b).window x →
      t - H.time e₁.succ ≤ θ / Q →
      ((records e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records e₁).static b).neck.scale →
      1 ≤ a₀ * ((records e₁).static b).neck.scale →
    (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      p.delta (H.time i.succ) ≤ δ₀) →
    H.time e₂.succ - H.time e₁.succ ≤ θ / Q →
    (∀ α, (records e₂).delta α *
      (8 * Real.sqrt (5 * Csep) * (D + 1) + 40000 + 2 * p.recenterConstant) ≤ 1) →
      (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
        ∀ x' : (H.stage i.castSucc).Carrier,
        ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
          qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2) →
      (∀ x' : (H.stage e₂.castSucc).Carrier, ∀ τ ∈ Ioo (H.time e₂.castSucc) t,
        qcan < (H.toHistory.event e₂).incoming.flow.scalar τ x' →
        |derivWithin (fun v => (H.toHistory.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
          C * (H.toHistory.event e₂).incoming.flow.scalar τ x' ^ 2) →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.toHistory.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.toHistory.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂) := by
  obtain ⟨Csep, hCsep, P, Creset, Cbirth, hP, hCreset, hCbirth, h⟩ :=
    nonResurgery_pair_of_tube_sep_C11SP.{u} Θ hΘ hΘ1
  refine ⟨Csep, hCsep, P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro C D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, h⟩ := h C D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p records hcanonical hRp hmp hζp qcan a₀ B Q θ hqcan hQ hθ hBθ hB16 hHI hlow
    e₁ e₂ hl t ht y A b x hanchor hage hscale hxD hbirth haq hδloc hT2 hδ2 hderiv hfinal
  exact h H records hcanonical hRp hmp hζp qcan a₀ B Q θ hqcan hQ hθ hBθ hB16 hHI hlow
    e₁ e₂ hl t ht y A b x hanchor hage hscale hxD hbirth haq hδloc hT2 hδ2 (fun _ => univ)
    (fun _ => isOpen_univ) (fun _ _ _ _ _ _ => mem_univ _)
    (fun i h1 h2 x' _ τ hτ hR => hderiv i h1 h2 x' τ hτ hR) (fun x' _ τ hτ hR => hfinal x' τ hτ hR)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
