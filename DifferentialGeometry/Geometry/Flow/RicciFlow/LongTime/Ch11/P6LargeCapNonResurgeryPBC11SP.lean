import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapNonResurgeryC11SP

set_option autoImplicit false

/-!
# CC′ ⇐ NR′（PB 形；O-CH11-NATIVE-SEP G4b，后缀 `_C11SP`）

lead 03:4x 裁定 (a)：NR/CC 合同在 `ε₀ θ̄` 同层加 `(Rmod, mmod)`（R-C11-20 Q3：不交换量词；NR consumer 的
`N` 固定 ⇒ 有限 `(R*, m*)`），`pBase` 另需 `Rmod ≤ modelRadius`、`mmod ≤ modelOrder`（同一 `pBase`）。
`largeCap_crossing_count_of_nonResurgery_PB_C11SP` = NATIVE-CC
`largeCap_crossing_count_of_nonResurgery_C11SP` 的 PB 孪生（证明逐字：两两相等计数，`n₀ = 1`；
新前提只透传）。CC′ 对冻结 CC 的差 = provider 义务 **PB**
（request-driven：`modelRadius ≥ Rmod`、`modelOrder ≥ mmod`）；PB 需证明的 provider 孪生
（HpbaseTwoLevel v8 + `mmod` 导出）尚未证。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G4b（PROVED 接线；输入合同 NR′ = PB 形）**：CC′ ⇐ NR′，`n₀ = 1`。 -/
theorem largeCap_crossing_count_of_nonResurgery_PB_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rmod : ℝ) (mmod : ℕ)
    (hNR : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (hf₂ : H.activeStage a ≤ e₂.castSucc)
        (hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
        (∃ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records n e₁).static b).window z =
            A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ ∧
          ((records n e₁).static b).neck.scale ≤ 4 * (B * Q)) →
      ∀ (b : (H.event e₂).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₂).static b).neck.scale ≤ 4 * (B * Q) →
        ((records n e₂).static b).window z ≠
          A.point e₂.succ (hf₂.trans e₂.castSucc_lt_succ.le) hl₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        Set.ncard {e : Fin H.eventCount |
          ∃ (hf : H.activeStage a ≤ e.castSucc)
            (hl : e.succ ≤ H.activeStage t)
            (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀ := by
  obtain ⟨ε₀, hε₀, θbar, hθbar, hNR⟩ := hNR
  refine ⟨ε₀, hε₀, θbar, 1, hθbar, ?_⟩
  intro pBase Γf S F hT q hdiag hacc hrad hord hRm hmm params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  have hm := hNR S F hT q hdiag hacc hrad hord hRm hmm params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  obtain ⟨T₀, hT₀, hmain⟩ := hm
  refine ⟨T₀, hT₀, ?_⟩
  intro n θ hθ hθB H t ht Q hQ a hat hwin y A hRA
  have hNRA := hmain n θ hθ hθB t ht Q hQ a hat hwin y A hRA
  refine (Set.ncard_le_one (Set.toFinite _)).mpr ?_
  intro e₁ he₁ e₂ he₂
  obtain ⟨hf₁, hl₁, b₁, z₁, h11, h12, h13, h14⟩ := he₁
  obtain ⟨hf₂, hl₂, b₂, z₂, h21, h22, h23, h24⟩ := he₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hNRA e₁ e₂ hf₁ hl₁ hf₂ hl₂ hlt ⟨b₁, z₁, h11, h12, h13, h14⟩ b₂ z₂ h21 h22 h24 h23
  · exact hNRA e₂ e₁ hf₂ hl₂ hf₁ hl₁ hlt ⟨b₂, z₂, h21, h22, h23, h24⟩ b₁ z₁ h11 h12 h14 h13

/-- **consumer**：`(Rmod, mmod)` 落在冻结门槛内（`Rmod ≤ capWindowRadius_C11E + 1`、`mmod ≤ 2`）时 CC′ 退化为冻结 CC
（PB 差为零）——G4b 结论真正被使用的方向；一般 `(R*, m*)` 下差 = provider 义务 PB。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (Rmod : ℝ) (mmod : ℕ)
    (hR : Rmod ≤ capWindowRadius_C11E + 1) (hm : mmod ≤ 2)
    (hNR : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (hf₂ : H.activeStage a ≤ e₂.castSucc)
        (hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
        (∃ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records n e₁).static b).window z =
            A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ ∧
          ((records n e₁).static b).neck.scale ≤ 4 * (B * Q)) →
      ∀ (b : (H.event e₂).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₂).static b).neck.scale ≤ 4 * (B * Q) →
        ((records n e₂).static b).window z ≠
          A.point e₂.succ (hf₂.trans e₂.castSucc_lt_succ.le) hl₂)
    :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ (θbar : ℝ) (n₀ : ℕ), 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        Set.ncard {e : Fin H.eventCount |
          ∃ (hf : H.activeStage a ≤ e.castSucc)
            (hl : e.succ ≤ H.activeStage t)
            (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀
 := by
  obtain ⟨ε₀, hε₀, θbar, n₀, hθbar, h⟩ :=
    largeCap_crossing_count_of_nonResurgery_PB_C11SP P g Rmod mmod hNR
  exact ⟨ε₀, hε₀, θbar, n₀, hθbar, fun S F hT q hdiag hacc hrad hord =>
    h S F hT q hdiag hacc hrad hord (hR.trans hrad) (hm.trans hord)⟩

end GC.LongTime.Ch11
