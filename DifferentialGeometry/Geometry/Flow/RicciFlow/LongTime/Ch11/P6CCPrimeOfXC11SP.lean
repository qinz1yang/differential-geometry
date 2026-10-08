import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NRPrimeTowerC11SP

set_option autoImplicit false

/-!
# CC′ ⇐ X：`CCprime_of_X_C11SP`（O-CH11-NRPRIME-WIRE G2，后缀 `_C11SP`，INTEGRATION）

`largeCap_crossing_count_of_nonResurgery_PB_C11SP`（CC′ ⇐ NR′，PROVED 接线）∘ G1 `hNRprime_of_X_C11SP`
（NR′ ⇐ Xtower）。结论 CC′ = PB 定理结论**逐字**；前提 Xtower = G1 的 Xtower **逐字**（生成器
`build-logs/scratch/O-CH11-NRPRIME-WIRE/gen/gen_g2.py` 断言）⇒ **PROVISIONAL[X]**。
CC′ 与冻结 CC（WIRE7 `hCC`）恰差一行 PB 前提 `Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →`
（provider 义务，HPBASE-V8）；consumer：PB 在冻结门槛内平凡成立时 CC′ ⇒ 冻结 CC。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2（PROVISIONAL[X]）**：`Xtower → CC′(Rmod, mmod)`（CC′ = PB 定理结论逐字）。 -/
theorem CCprime_of_X_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ C : ℝ≥0, ∃ (Rmod : ℝ) (mmod : ℕ) (εX : ℝ), 0 < εX ∧
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εX → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
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
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ 1 / 16 →
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
        (hl₁ : e₁.succ ≤ H.activeStage t) (_hf₂ : H.activeStage a ≤ e₂.castSucc)
        (_hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
      ∀ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₁).static b).window z =
          A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ →
        ((records n e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ∃ W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier, (∀ i, IsOpen (W i)) ∧
        (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
          ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H e₁.succ i hf x'),
            A'.point e₁.succ le_rfl hf ∈
              ((records n e₁).static b).window '' {z | ‖z.val‖ < Rmod + 1} →
              x' ∈ W i) ∧
        (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
          ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
          ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
            Cbirth * ((records n e₁).static b).neck.scale < (H.event i).incoming.flow.scalar τ x' →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
              C * (H.event i).incoming.flow.scalar τ x' ^ 2) ∧
        (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc →
          ∀ τ ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ),
          Cbirth * ((records n e₁).static b).neck.scale < (H.event e₂).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2)) →
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
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀) := by
  obtain ⟨Cbirth, hCbirth, h⟩ := hNRprime_of_X_C11SP.{u} P g
  refine ⟨Cbirth, hCbirth, fun C => ?_⟩
  obtain ⟨Rmod, mmod, εX, hεX, hXN⟩ := h C
  exact ⟨Rmod, mmod, εX, hεX, fun hX =>
    largeCap_crossing_count_of_nonResurgery_PB_C11SP P g Rmod mmod (hXN hX)⟩

/-- **consumer**：PB 在冻结门槛内平凡成立（`Rmod ≤ capWindowRadius_C11E + 1`、`mmod ≤ 2`）时，
G2 的 CC′ 直接给出冻结 CC（WIRE7 `hCC` 逐字）；一般 `(Rmod, mmod)` 下差额 = provider 义务 PB。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ C : ℝ≥0, ∃ (Rmod : ℝ) (mmod : ℕ) (εX : ℝ), 0 < εX ∧
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εX → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
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
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ 1 / 16 →
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
        (hl₁ : e₁.succ ≤ H.activeStage t) (_hf₂ : H.activeStage a ≤ e₂.castSucc)
        (_hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
      ∀ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₁).static b).window z =
          A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ →
        ((records n e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ∃ W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier, (∀ i, IsOpen (W i)) ∧
        (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
          ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H e₁.succ i hf x'),
            A'.point e₁.succ le_rfl hf ∈
              ((records n e₁).static b).window '' {z | ‖z.val‖ < Rmod + 1} →
              x' ∈ W i) ∧
        (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
          ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
          ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
            Cbirth * ((records n e₁).static b).neck.scale < (H.event i).incoming.flow.scalar τ x' →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
              C * (H.event i).incoming.flow.scalar τ x' ^ 2) ∧
        (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc →
          ∀ τ ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ),
          Cbirth * ((records n e₁).static b).neck.scale < (H.event e₂).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2)) →
    Rmod ≤ capWindowRadius_C11E + 1 → mmod ≤ 2 →
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
            ((records n e).static b).neck.scale ≤ 4 * (B * Q)} ≤ n₀) := by
  obtain ⟨Cbirth, hCbirth, h⟩ := CCprime_of_X_C11SP.{u} P g
  refine ⟨Cbirth, hCbirth, fun C => ?_⟩
  obtain ⟨Rmod, mmod, εX, hεX, hXC⟩ := h C
  refine ⟨Rmod, mmod, εX, hεX, fun hX hR hm => ?_⟩
  obtain ⟨ε₀, hε₀, θbar, n₀, hθbar, hcc⟩ := hXC hX
  exact ⟨ε₀, hε₀, θbar, n₀, hθbar, fun S F hT q hdiag hacc hrad hord =>
    hcc S F hT q hdiag hacc hrad hord (hR.trans hrad) (hm.trans hord)⟩

end GC.LongTime.Ch11
