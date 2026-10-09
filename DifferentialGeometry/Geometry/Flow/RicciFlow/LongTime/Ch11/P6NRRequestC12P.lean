import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpbaseRequestC12P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNRSepC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapNonResurgeryC11SP

/-!
# NR′ 接 request-driven provider；CC 的 `(Rn, mn)` 孪生（车道 C12-3，后缀 `_C12P`）

**`N` 是否固定（D-20-9 动作项）**：CC 的 NR 合同（`largeCap_crossing_count_of_nonResurgery_C11SP` 的
`hNR`）**不含 `N`**；NR 两两核 `nonResurgery_pair_of_tube_C11SP` 的 `∀ N ∃ R m₀` 里 `N` 只出现在
`hSEP` 的前件（标准解比较的导数阶），结论与 `N` 无关；SEP 接线版 `nonResurgery_pair_of_tube_sep_C11SP`
写成 `∀ _N`（未用）。故一次 NR 调用只需一组固定 `(D, ε, η, N)`，所需 `(R*, m*)` 有限。本文件取
`D := transitionEnd + 10`（buffer 点 `‖x‖ ≤ transitionEnd + 10 < D + 1`）、`ε = η = 1`、`N = 0`。
`(R*, m*)` 仍依赖 Dt 常数 `C`（合同 X），后者可依赖 `Γf`，所以请求放在 `∃ Γ Γf` 之后。
* `nrPair_request_C12P`：v8 provider（`hpbaseTwoLevel_v8_cap_C12P`）+ SEP 接线版 NR 两两核 ⇒ 同一 `pB`
  同时给 A12′ `hmake` 的冻结合取、hSL1 / CC 调用约束、NR 的 `R ≤ radius`、`m₀ ≤ order`、`acc ≤ ζ₀`，
  以及对所有 `params`（radius / order / accuracy 与 `pB` 相同，= CC 合同的 G21 合取）的 NR 两两核
  结论（剩余前提 = 合同 X + SEP′ 陈述补全，原样保留）。
* `largeCap_crossing_count_of_nonResurgery_v8_C12P`：CC ⇐ NR 的孪生，NR′ / CC′ 的 `∀ pBase` 调用约束
  多 `Rn Γf ≤ pBase.modelRadius → mn Γf ≤ pBase.modelOrder`（`Rn mn : ClosedBirthConstants → _` 在
  `∀ pBase Γf` 前存在）；证明逐字。
* `ccPrime_premises_request_C12P`：给定 `(ε₀, Rn, mn)`，v8 provider 的同一 `pB` 满足 CC′ 的全部参数前提。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **NR′ request（PROVISIONAL[X]，由 NR 两两核继承）**：`(R, m₀, ζ₀)` 在 `Γf` 与 `C` 之后求出，
再向 v8 provider 请求 `(R, m₀)`、`εReserve ≤ ζ₀`；同一 `pB` 付 A12′ `hmake`、hSL1 / CC 调用约束与 NR
的三条参数前提。 -/
theorem nrPair_request_C12P (P : OrientedThreeStage.{u}) (g : P.Metric) (Θ : ℝ) (hΘ : 0 < Θ)
    (hΘ1 : Θ < 1) :
    ∃ Csep : ℝ, 0 < Csep ∧ ∃ Pc Creset Cbirth : ℝ, 0 < Pc ∧ 0 < Creset ∧ 0 < Cbirth ∧
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
    Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ epsW_CXOU2.{u} ∧
    Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ epsW_CXOU2.{u} ∧
    ∀ C : ℝ≥0,
    ∃ R : ℝ, StandardCap.transitionEnd + 10 + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ εReserve : ℝ, 0 < εReserve → εReserve ≤ ζ₀ →
    ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
      (prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j) ∧
      (pB.modelAccuracy ≤ εReserve ∧ capWindowRadius_C11E + 1 ≤ pB.modelRadius ∧
        2 ≤ pB.modelOrder) ∧
      R ≤ pB.modelRadius ∧ m₀ ≤ pB.modelOrder ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      p.modelRadius = pB.modelRadius → p.modelOrder = pB.modelOrder →
      p.modelAccuracy = pB.modelAccuracy →
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
      ‖x.val‖ < StandardCap.transitionEnd + 10 + 1 →
      qcan ≤ Cbirth * ((records e₁).static b).neck.scale →
      1 ≤ a₀ * ((records e₁).static b).neck.scale →
    (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      p.delta (H.time i.succ) ≤ δ₀) →
    H.time e₂.succ - H.time e₁.succ ≤ θ / Q →
    (∀ α, (records e₂).delta α *
      (8 * Real.sqrt (5 * Csep) * (StandardCap.transitionEnd + 10 + 1) + 40000 +
        2 * p.recenterConstant) ≤ 1) →
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
  obtain ⟨Csep, hCsep, Pc, Creset, Cbirth, hPc, hCreset, hCbirth, hnr⟩ :=
    RetainedCoreHistory.nonResurgery_pair_of_tube_sep_C11SP.{u} Θ hΘ hΘ1
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := hpbaseTwoLevel_v8_cap_C12P.{u} P g
  refine ⟨Csep, hCsep, Pc, Creset, Cbirth, hPc, hCreset, hCbirth, Cdist, Γ, Γf, hfine, h1, h2, h3,
    h4, fun C => ?_⟩
  have hD : 0 < StandardCap.transitionEnd + 10 := by
    have hte := StandardCap.transitionEnd_pos
    linarith
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hcore⟩ :=
    hnr C (StandardCap.transitionEnd + 10) 1 1 hD one_pos one_pos 0
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, fun εReserve hεReserve hεζ => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, hR, hm, hcollar, hstep⟩ :=
    hmake R m₀ εReserve hεReserve
  have hb := pBase_bounds_of_reserve_C11W6 hbase hres
  refine ⟨pB, prepared, ⟨hbase, hdist, hres, hcollar, hstep⟩, hb, hR, hm, ?_⟩
  intro H p records hcan hr ho ha
  exact hcore H records hcan (hR.trans_eq hr.symm) (hm.trans_eq ho.symm)
    ((ha.trans_le hb.1).trans hεζ)

/-! ## CC′ ⇐ NR′（`(Rn, mn)` 调用约束孪生） -/

/-- **CC′ ⇐ NR′（PROVED，条件归约）**：`largeCap_crossing_count_of_nonResurgery_C11SP` 逐字，只在
`hNR` 与结论的 `∀ pBase` 调用约束里加 `Rn Γf ≤ pBase.modelRadius → mn Γf ≤ pBase.modelOrder`
（`∃ Rn mn` 紧接 `θbar`）。 -/
theorem largeCap_crossing_count_of_nonResurgery_v8_C12P (P : OrientedThreeStage.{u})
    (g : P.Metric)
    (hNR : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
      ∃ (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ),
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rn Γf ≤ pBase.modelRadius → mn Γf ≤ pBase.modelOrder →
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
    ∃ (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ),
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rn Γf ≤ pBase.modelRadius → mn Γf ≤ pBase.modelOrder →
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
  obtain ⟨ε₀, hε₀, θbar, hθbar, Rn, mn, hNR⟩ := hNR
  refine ⟨ε₀, hε₀, θbar, 1, hθbar, Rn, mn, ?_⟩
  intro pBase Γf S F hT q hdiag hacc hrad hord hRn hmn params records h1 h2 h3 h4 h5 h6 h7
    h8 B hB
  have hm := hNR S F hT q hdiag hacc hrad hord hRn hmn params records h1 h2 h3 h4 h5 h6 h7
    h8 B hB
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
/-- **CC′ 的参数前提由 v8 provider 的同一 `pB` 付**：给定 NR′ / CC′ 的 `(ε₀, Rn, mn)`，在 `Γf` 处请求
`(Rn Γf, mn Γf)`、`εReserve ≤ ε₀`；同一 `pB` 给 A12′ `hmake` 的冻结合取与 CC′ 的五条参数前提。 -/
theorem ccPrime_premises_request_C12P (P : OrientedThreeStage.{u}) (g : P.Metric) (ε₀ : ℝ)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ) :
    ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
    Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ epsW_CXOU2.{u} ∧
    Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ epsW_CXOU2.{u} ∧
    ∀ εReserve : ℝ, 0 < εReserve → εReserve ≤ ε₀ →
    ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
      (prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
        prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
        collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
        ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j) ∧
      pB.modelAccuracy ≤ ε₀ ∧ capWindowRadius_C11E + 1 ≤ pB.modelRadius ∧
      2 ≤ pB.modelOrder ∧ Rn Γf ≤ pB.modelRadius ∧ mn Γf ≤ pB.modelOrder := by
  obtain ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, hmake⟩ := hpbaseTwoLevel_v8_cap_C12P.{u} P g
  refine ⟨Cdist, Γ, Γf, hfine, h1, h2, h3, h4, fun εReserve hεReserve hε₀ => ?_⟩
  obtain ⟨pB, prepared, hbase, hdist, hres, hR, hm, hcollar, hstep⟩ :=
    hmake (Rn Γf) (mn Γf) εReserve hεReserve
  obtain ⟨hacc, hrad, hord⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  exact ⟨pB, prepared, ⟨hbase, hdist, hres, hcollar, hstep⟩, hacc.trans hε₀, hrad, hord, hR, hm⟩

/-- consumer：NR′ 请求在 `Γf` 之后（Dt 常数取 `C := Γf.Ctime`，`(R, m₀, ζ₀)` 随之求出）、
`εReserve ≤ ζ₀`：同一 `pB` 上 NR 的三条参数前提成立（`params`
与 `pB` 同 radius / order / accuracy，即 CC 合同里的 G21 合取）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ Γf : ClosedBirthConstants, Γf.epsilon ≤ epsW_CXOU2.{u} ∧ ∃ (R ζ₀ : ℝ) (m₀ : ℕ),
      ∀ εReserve : ℝ, 0 < εReserve → εReserve ≤ ζ₀ →
      ∃ (pB : CutoffParameters) (_ : ClosedBirthPreparedClass pB Γf P g 1),
        ∀ params : CutoffParameters, params.modelRadius = pB.modelRadius →
          params.modelOrder = pB.modelOrder → params.modelAccuracy = pB.modelAccuracy →
          R ≤ params.modelRadius ∧ m₀ ≤ params.modelOrder ∧ params.modelAccuracy ≤ ζ₀ ∧
          capWindowRadius_C11E + 1 ≤ params.modelRadius ∧ 2 ≤ params.modelOrder := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, Γf, _, _, _, _, hW, hreq₀⟩ :=
    nrPair_request_C12P.{u} P g Θ hΘ hΘ1
  refine ⟨Γf, hW, ?_⟩
  obtain ⟨R, _, m₀, _, ζ₀, _, _, _, _, hreq⟩ := hreq₀ Γf.Ctime
  refine ⟨R, ζ₀, m₀, fun εReserve hε hεζ => ?_⟩
  obtain ⟨pB, prepared, -, ⟨hacc, hrad, hord⟩, hR, hm, -⟩ := hreq εReserve hε hεζ
  exact ⟨pB, prepared, fun params hr ho ha => ⟨hR.trans_eq hr.symm, hm.trans_eq ho.symm,
    (ha.trans_le hacc).trans hεζ, hrad.trans_eq hr.symm, hord.trans_eq ho.symm⟩⟩

end GC.LongTime.Ch11
