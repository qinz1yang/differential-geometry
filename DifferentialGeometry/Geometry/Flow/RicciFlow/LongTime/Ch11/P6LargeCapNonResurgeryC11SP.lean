import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapCrossingC11SP

set_option autoImplicit false

/-!
# CC ⇐ NR（新生大 cap 的 non-resurgery；O-CH11-NATIVE-CC G2，后缀 `_C11SP`）

**NR（合同，binder `hNR`）**：同一窗 `[t − θ/Q, t]`（`θ·B ≤ θ̄`）内同一条 trace `A`（scalar `≤ 2BQ`）、
两个 crossed event `e₁ < e₂`：若 `A` 在 `e₁⁺` 落在 `e₁` 某大 cap（`neck.scale ≤ 4BQ`）的 buffer
`transitionEnd < ‖z‖ ≤ transitionEnd + 10`，则 `A` 在 `e₂⁺` 不落在 `e₂` 任何大 cap 的 buffer。
量词骨架与 CC 统一形完全相同（`ε₀, θ̄` 在 S 前；records/params 合取 = G21；`∀ B` 后 `∃ T₀`）。

**定理 `largeCap_crossing_count_of_nonResurgery_C11SP`（PROVED）**：NR ⇒ CC，`n₀ = 1`
（计数集两两相等：两个不同元素按 `Fin` 序比较，较早者给出 NR 的前件，较晚者违反结论）。

**NR 的数学来源**（不在树内）：Perelman II Lemma 4.5 / Kleiner–Lott Lemma 74 的局部零阶版——新生
cap 在归一化时间 `≤ 4θ̄ < 1` 内要么整块被移除、要么 unscathed 且贴近 standard solution。trace 存活排除前者；
后者下 `e₂` 的 δ-neck（长 `≫ D·h`）放不进 cap₁ 的 window。树内最近的 producer 是
`StandardCap/WindowPersistence:1029`，它要求全局 Dt；缺口的精确形见
`build-logs/resume/state-O-CH11-NATIVE-CC.md` §G3。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2（PROVED）**：CC ⇐ NR，`n₀ = 1`。 -/
theorem largeCap_crossing_count_of_nonResurgery_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hNR : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
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
  intro pBase Γf S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  have hm := hNR S F hT q hdiag hacc hrad hord params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
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

/-- **G2 consumer**：NR ⇒（G2）CC ⇒（G1）Window 孪生第二行，因子 `C_buf^{2}`（`n₀ = 1`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hNR : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
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
      ∀ (y x : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y)
        (A' : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) x),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A'.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
        params.modelAccuracy ≤ 1 / 2 → StandardCap.transitionEnd + 10 < params.modelRadius →
        (∀ (e : Fin H.eventCount) (b b' : (H.event e).RetainedBoundaryIndex),
          b ≠ b' → ∀ y z : standardCapWindow params.modelRadius,
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
            ((records n e).static b).window y ≠ ((records n e).static b').window z) →
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {X : ℝ≥0∞},
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t),
          (∀ b, A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records n e).static b).window ''
              {y : standardCapWindow params.modelRadius |
                ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            ((records n e).static b).window z =
              A'.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∧
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)) →
        (∀ (v w : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) (haw : a ≤ w)
          (hwt : w ≤ t), v ≤ w → H.activeStage v = H.activeStage w →
          (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
            A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
          A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
            A.pairEDist_CXSP (hat := hat) A' w haw hwt + ENNReal.ofReal (Λ * ((w : ℝ) - v))) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t), v < s →
          A.pairEDist_CXSP (hat := hat) A' s has hst < X) →
        A.pairEDist_CXSP (hat := hat) A' v hav hvt ≤
          ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
              ((params.modelRadius - (StandardCap.transitionEnd + 10)) /
                (StandardCap.transitionEnd + 11) ^ 2)))
              (4 * (StandardCap.transitionEnd + 11) *
                (StandardCap.transitionEnd + 13))) ^ (2 * n₀) *
            (A.pairEDist_CXSP (hat := hat) A' t hat le_rfl +
              ENNReal.ofReal (Λ * ((t : ℝ) - v))) :=
  pairEDist_window_of_CC_C11SP P g (largeCap_crossing_count_of_nonResurgery_C11SP P g hNR)

end GC.LongTime.Ch11
