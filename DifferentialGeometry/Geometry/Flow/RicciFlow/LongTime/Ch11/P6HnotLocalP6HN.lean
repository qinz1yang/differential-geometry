import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowDtP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NotKResidualP6R2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDNotKEvP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E

/-!
# `hnotK`（年龄序列 θ n 形）的 (CWW) 时间半 ⇐ cap-window 局部 Dt（O-CH11-HNOT-LOCALDT G2，后缀 `_P6HN`）

`hnotK_of_capWindowWitness_P6R2`（`P6NotKResidualP6R2:107`）的时间半在选出点 `(t n, yG n)` **本点**用
全局 `hslabK : EventSlabsDerivative Ctime (Q n) (Fin.last _)`（含 `t n` 及之后）。本文件：
* **主形 `hnotK_of_capWindowWitness_theta_P6HN`（PROVED 组合）**：时间半改由 G1
  `capWindow_trace_localDt_P6HN` 在 cap 配置 `(i, A, b, x)` 上生产，常数 `Ctime₀` 在一切之前取定
  （`Ctime₀ ≤ Ctime'`）；导数前提只剩**严格在 `t n` 之前**的两条既有结构 Prop：
  `(K n).EventSlabsDerivative C (Q n) (j n).castSucc`（slab `j' < j n`）与
  `((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (Q n) (t n)`（slab `j n` 的
  `Ioo (time (j n)⁻) (t n)`）。年龄上界 `θ n < 1`（序列；`θ n ≡ θ₀` = SLICE-BCBD G3 / G5 槽形，
  `θ n = 1 − 1/(n+2)` = P6R2 (CWW) 形），窗口 `‖x‖ < n + 2`。
* (CWW) `θ n = 1 − 1/(n+2)` 形同样由主形付：G1 的 `Ctime₀` 对 `θcap → 1` 一致，`θ n` 只进 diagonal
  序列 `Cb n`（birth 尺度）与 persistence 参数；(CWW) witness `hcww` 本身仍是 P6R2 的 binder，不在本文件。
* **缺口见证 `hnotK_of_ceilcap_P6HN`（BLOCKED[profile 跳比条款]）**：tower 帧 `K n = F.tower.history n`，
  两条前缀 Dt 前提由 `TimeDerivativeSupply_C11E F q.neckRadius C` + `AntitoneOn q.neckRadius` 付清
  （阈值 `Q n := (ρ(t n)²)⁻¹`）；剩下的尺度关系以内联 **(SEP-ρ)** 出现：cap 配置上
  `(n+1)·(ρ(t n)²)⁻¹ ≤ scale`（⇒ eventually `hceilcap` 与 `1 ≤ a₀·scale`），结论 `∀ᶠ n` 形 `hnotK`。
* `sepRho_of_ratio_P6HN`：profile 跳比 `ρ(tᵢ) ≤ Λ·ρ(t)` + `δ(tᵢ)⁴·2Λ²·(n+1) ≤ 1` ⇒ (SEP-ρ)。
* `static_scale_gt_birth_P6HN`：锐形 birth 关系 `(2·δ(tᵢ)⁴·ρ(tᵢ)²)⁻¹ < scale`（record 字段
  `nominal_small` + `scale_eq` + `recenter_scale_comparison`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-- 点态 stage 形导数界（`_P6HN`）：incoming slab 上 `(v, zG)` 处的界 ⇒ `m = j.castSucc` 的
`stageMetric` 形（`HEq z zG`）。 -/
theorem stageDerivative_at_of_incoming_P6HN (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ) (z : (K.stage m).Carrier)
    (zG : (K.stage j.castSucc).Carrier) (hz : HEq z zG) {Ct : ℝ}
    (h : |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s zG) (Iic v) v| ≤
      Ct * (K.toHistory.event j).incoming.flow.scalar v zG ^ 2) :
    |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) z) (Iic v) v| ≤
      Ct * metricScalarAt (K.toHistory.stageMetric m v) z ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hz
  have hfun : ∀ t, metricScalarAt (K.toHistory.stageMetric j.castSucc t) z =
      (K.toHistory.event j).incoming.flow.scalar t z := fun t => by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    rfl
  simp only [hfun]
  exact h

/-- **G2 主形（`_P6HN`，PROVED 组合）**：`hnotK`（年龄 `θ n`，`‖x‖ < n + 2`）⇐ (CWW) witness + `hsel` +
**前缀** Dt（`EventSlabsDerivative` 到 `(j n).castSucc`、`DerivativeBoundBefore (t n)`）+ diagonal 参数。
时间半由 G1 `capWindow_trace_localDt_P6HN` 生产（`Ctime₀ ≤ Ctime'`）；不用 `t n` 处 / 之后的导数界。 -/
theorem hnotK_of_capWindowWitness_theta_P6HN :
    ∃ Ctime₀ : ℝ≥0, 0 < Ctime₀ ∧ ∀ (C : ℝ≥0) {θ : ℕ → ℝ}, (∀ n, θ n < 1) →
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n) ∧ (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧
      (∀ n, 0 < δ₀ n) ∧
    ∀ {ε C1' C2' : ℝ} {Ctime' : ℝ≥0}, Ctime₀ ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n, (K n).EventSlabsDerivative C (Q n) (j n).castSucc) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (Q n) (t n)) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
    ∀ {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
      {Kh : ℕ → ObservedHistory.{u}}, Kh = (fun n => (K n).toHistory) →
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier),
      (∀ n, (σ n : ℝ) = t n) → (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      (∀ n, (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ε C1' C2' (y n), W.capTubeHasNeckChart ε) →
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ctime₀, hC₀, hall⟩ := capWindow_trace_localDt_P6HN.{u}
  refine ⟨Ctime₀, hC₀, fun C θ hθ => ?_⟩
  choose Cb hCb hD using fun n : ℕ => hall C (θ n) (hθ n)
  choose Rn m₀ hRn ζ δ₀ hζ hδ h4 using fun n : ℕ => hD n ((n : ℝ) + 1) (by positivity)
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hRn, hζ, hδ, ?_⟩
  intro ε C1' C2' Ctime' hCt K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc
    hrad hord hQ hder hcur hbirth hbirthA yG Kh hKh σ y hσ hyG hsel hcww
  subst hKh
  intro n hC
  apply hsel n
  refine ⟨hcww n hC, fun _ _ => ?_⟩
  obtain ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩ := hC
  have hjt' : (K n).time (j n).castSucc < (σ n : ℝ) := by
    rw [hσ n]
    exact hjt n
  have htj' : (σ n : ℝ) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) hjt'.le htj'
  have hDt := (h4 n (K n) (recordsK n) (hcanK n) (hrad n) (hord n) (hacc n) (recordsF n) (δ₀ n)
    (hδF n) le_rfl (Q n) a₀ (hQ n) (fun x => (hHI n x).1) (fun x => (hHI n x).2)
    (j n).castSucc ((K n).time (j n).succ) ((K n).toHistory.event (j n)).incoming
    ((K n).event_initial (j n)) (hder n) (t n) (hjt n) (htj n) (hcur n) i hi hl (yG n) A b x hx
    hage hxn (hbirth n i hi b hl hage) (hbirthA n i hi b hl hage)).1
  have hDt' : |derivWithin (fun s => ((K n).toHistory.event (j n)).incoming.flow.scalar s (yG n))
      (Iic (σ n : ℝ)) (σ n : ℝ)| ≤ (Ctime' : ℝ) *
        ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n) ^ 2 := by
    rw [hσ n]
    exact hDt.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _))
  exact (K n).stageDerivative_at_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n) (hyG n) hDt'

end RetainedCoreHistory

/-- `ρ` antitone、`0 ≤ v ≤ t` ⇒ `(ρ v²)⁻¹ ≤ (ρ t²)⁻¹`（`_P6HN`）。 -/
theorem inv_sq_neckRadius_le_P6HN {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) :
    (q.neckRadius v ^ 2)⁻¹ ≤ (q.neckRadius t ^ 2)⁻¹ := by
  have ht : 0 < q.neckRadius t := q.neckRadius_pos t (hv.trans hvt)
  have h := hanti (mem_Ici.mpr hv) (mem_Ici.mpr (hv.trans hvt)) hvt
  exact inv_anti₀ (pow_pos ht 2) (pow_le_pow_left₀ ht.le h 2)

/-- **前缀 Dt ⇐ profile 供给（`_P6HN`，PROVED）**：tower 帧 `F.tower.history n`、阈值 `(ρ(t)²)⁻¹`，
`TimeDerivativeSupply_C11E F q.neckRadius C` 的 event-slab 子句 + `AntitoneOn q.neckRadius` 给出
`EventSlabsDerivative C (ρ(t)²)⁻¹ j.castSucc` 与 slab `j` 的 `DerivativeBoundBefore C (ρ(t)²)⁻¹ t`。 -/
theorem prefixDt_of_timeDerivativeSupply_P6HN {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {C : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (n : ℕ) (j : Fin (F.tower.history n).eventCount)
    {t : ℝ} (hjt : (F.tower.history n).time j.castSucc < t)
    (htj : t ≤ (F.tower.history n).time j.succ) :
    (F.tower.history n).EventSlabsDerivative C ((q.neckRadius t ^ 2)⁻¹) j.castSucc ∧
      ((F.tower.history n).toHistory.event j).incoming.DerivativeBoundBefore C
        ((q.neckRadius t ^ 2)⁻¹) t := by
  constructor
  · intro j' hj' y v hv hR
    have hle : j'.succ ≤ j.castSucc := Fin.castSucc_lt_iff_succ_le.mp hj'
    have hv0 : 0 ≤ v :=
      ((F.tower.history n).toHistory.time_nonneg j'.castSucc).trans hv.1.le
    have hvt : v ≤ t :=
      (hv.2.le.trans ((F.tower.history n).time_strictMono.monotone hle)).trans hjt.le
    exact hTD.1 n j' y v hv ((inv_sq_neckRadius_le_P6HN hanti hv0 hvt).trans_lt hR)
  · intro y v hv hR
    have hv0 : 0 ≤ v :=
      ((F.tower.history n).toHistory.time_nonneg j.castSucc).trans hv.1.le
    exact hTD.1 n j y v ⟨hv.1, hv.2.trans_le htj⟩
      ((inv_sq_neckRadius_le_P6HN hanti hv0 hv.2.le).trans_lt hR)

/-- **缺口见证（`_P6HN`，BLOCKED[profile 跳比条款]）**：tower 帧 `K n = F.tower.history n`、固定 `θ₀ < 1`。
G2 主形的两条前缀 Dt 前提由 `prefixDt_of_timeDerivativeSupply_P6HN` 付清（`Q n := (ρ(t n)²)⁻¹`），结论
`hnotK`（`∀ᶠ n`，θ₀ 形 = SLICE-BCBD G5 槽）不带任何 Dt binder。唯一的尺度前提是内联的 **(SEP-ρ)**（eventually）：cap 配置
（`i.succ ≤ (j n).castSucc`、age `≤ θ₀/scale`）上 `(n+1)·(ρ(t n)²)⁻¹ ≤ scale`（= 统一 (SEP-ρ⁺) 右支
经 `le_max_right`）；它 eventually 蕴含
`(ρ(t n)²)⁻¹ ≤ Cbirth·scale`（`n + 1 ≥ Cbirth⁻¹`）与 `1 ≤ a₀·scale`（`n + 1 ≥ ρ(0)²/a₀`，`ρ` antitone）。
树内 `AnalyticSurgeryProfile` 只有 `radius_antitone`，推不出 (SEP-ρ)（缺跳比条款，见 `sepRho_of_ratio_P6HN`）。 -/
theorem hnotK_of_ceilcap_P6HN :
    ∃ Ctime₀ : ℝ≥0, 0 < Ctime₀ ∧ ∀ (C : ℝ≥0) {θ₀ : ℝ}, θ₀ < 1 →
    ∃ (Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n, 0 < δ₀ n) ∧
    ∀ {ε C1' C2' : ℝ} {Ctime' : ℝ≥0}, Ctime₀ ≤ Ctime' →
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters},
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C →
      AntitoneOn q.neckRadius (Ici 0) →
    ∀ {j : ∀ n, Fin (F.tower.history n).eventCount} {t : ℕ → ℝ},
      (∀ n, (F.tower.history n).time (j n).castSucc < t n) →
      (∀ n, t n < (F.tower.history n).time (j n).succ) →
    ∀ {T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (F.tower.history n).eventCount),
        T₀ n ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (F.tower.history n).eventCount), T₀ n ≤ (F.tower.history n).time i.succ →
        (pF n).delta ((F.tower.history n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ᶠ n in atTop, ∀ i hi b, i.succ ≤ (j n).castSucc →
        t n - (F.tower.history n).time i.succ ≤
          θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        ((n : ℝ) + 1) * (q.neckRadius (t n) ^ 2)⁻¹ ≤ ((recordsK n i hi).static b).neck.scale) →
    ∀ {yG : ∀ n, ((F.tower.history n).stage (j n).castSucc).Carrier}
      (σ : ∀ n, Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (y : ∀ n, ((F.tower.history n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (σ n : ℝ) = t n) → (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime'
        (σ n) (y n)) →
      (∀ n, (∃ (i : Fin (F.tower.history n).eventCount)
        (hi : T₀ n ≤ (F.tower.history n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (F.tower.history n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (F.tower.history n).time i.succ ≤
            θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ∃ W : SpatialCanonicalWitness ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage (σ n)) (σ n)) ε C1' C2' (y n),
          W.capTubeHasNeckChart ε) →
    ∀ᶠ n in atTop, ¬ ∃ (i : Fin (F.tower.history n).eventCount)
        (hi : T₀ n ≤ (F.tower.history n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (F.tower.history n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (F.tower.history n).time i.succ ≤
            θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ctime₀, hC₀, hall⟩ := RetainedCoreHistory.capWindow_trace_localDt_P6HN.{u}
  refine ⟨Ctime₀, hC₀, fun C θ₀ hθ₀ => ?_⟩
  obtain ⟨Cb, hCb, hD⟩ := hall C θ₀ hθ₀
  choose Rn m₀ hRn ζ δ₀ hζ hδ h4 using fun n : ℕ => hD ((n : ℝ) + 1) (by positivity)
  refine ⟨Rn, ζ, δ₀, m₀, hRn, hζ, hδ, ?_⟩
  intro ε C1' C2' Ctime' hCt P g F q hTD hanti j t hjt htj T₀ p pF recordsK recordsF a₀ ha₀
    hHI hcanK hδF hacc hrad hord hsep yG σ y hσ hyG hsel hcww
  obtain ⟨N, hN⟩ := exists_nat_ge (max Cb⁻¹ (q.neckRadius 0 ^ 2 / a₀))
  filter_upwards [eventually_ge_atTop N, hsep] with n hn hsepn
  intro hC
  apply hsel n
  refine ⟨hcww n hC, fun _ _ => ?_⟩
  obtain ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩ := hC
  have hs := hsepn i hi b hl hage
  set S := ((recordsK n i hi).static b).neck.scale with hSdef
  have ht0 : 0 ≤ t n := ((F.tower.history n).toHistory.time_nonneg _).trans (hjt n).le
  have hρ0 : 0 < q.neckRadius (t n) := q.neckRadius_pos _ ht0
  have hn1 : max Cb⁻¹ (q.neckRadius 0 ^ 2 / a₀) ≤ (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hinv0 : 0 ≤ (q.neckRadius (t n) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hceil : (q.neckRadius (t n) ^ 2)⁻¹ ≤ Cb * S := by
    have h1 : 1 ≤ Cb * ((n : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hn1) hCb.le
      rwa [mul_inv_cancel₀ hCb.ne'] at h
    calc (q.neckRadius (t n) ^ 2)⁻¹ ≤ Cb * ((n : ℝ) + 1) * (q.neckRadius (t n) ^ 2)⁻¹ :=
          le_mul_of_one_le_left hinv0 h1
      _ = Cb * (((n : ℝ) + 1) * (q.neckRadius (t n) ^ 2)⁻¹) := by ring
      _ ≤ Cb * S := mul_le_mul_of_nonneg_left hs hCb.le
  have hbA : 1 ≤ a₀ * S := by
    have hρ00 : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
    have hinv : (q.neckRadius 0 ^ 2)⁻¹ ≤ (q.neckRadius (t n) ^ 2)⁻¹ :=
      inv_sq_neckRadius_le_P6HN hanti le_rfl ht0
    have h2 : q.neckRadius 0 ^ 2 / a₀ * (q.neckRadius 0 ^ 2)⁻¹ ≤
        ((n : ℝ) + 1) * (q.neckRadius (t n) ^ 2)⁻¹ :=
      mul_le_mul ((le_max_right _ _).trans hn1) hinv (inv_nonneg.mpr (sq_nonneg _))
        (by positivity)
    have h3 : q.neckRadius 0 ^ 2 / a₀ * (q.neckRadius 0 ^ 2)⁻¹ = a₀⁻¹ := by
      field_simp
    have h4' : a₀⁻¹ ≤ S := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4' ha₀.le
    rwa [mul_inv_cancel₀ ha₀.ne'] at h5
  have hpre := prefixDt_of_timeDerivativeSupply_P6HN hTD hanti n (j n) (hjt n) (htj n).le
  have hjt' : (F.tower.history n).time (j n).castSucc < (σ n : ℝ) := by
    rw [hσ n]
    exact hjt n
  have htj' : (σ n : ℝ) < (F.tower.history n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact : (F.tower.history n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (F.tower.history n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) hjt'.le htj'
  have hDt := (h4 n (F.tower.history n) (recordsK n) (hcanK n) (hrad n) (hord n) (hacc n)
    (recordsF n) (δ₀ n) (hδF n) le_rfl _ a₀ (inv_pos.mpr (pow_pos hρ0 2))
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) (j n).castSucc
    ((F.tower.history n).time (j n).succ) ((F.tower.history n).toHistory.event (j n)).incoming
    ((F.tower.history n).event_initial (j n)) hpre.1 (t n) (hjt n) (htj n) hpre.2 i hi hl (yG n)
    A b x hx hage hxn hceil hbA).1
  have hDt' : |derivWithin
      (fun s => ((F.tower.history n).toHistory.event (j n)).incoming.flow.scalar s (yG n))
      (Iic (σ n : ℝ)) (σ n : ℝ)| ≤ (Ctime' : ℝ) *
        ((F.tower.history n).toHistory.event (j n)).incoming.flow.scalar (σ n : ℝ) (yG n) ^ 2 := by
    rw [hσ n]
    exact hDt.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _))
  exact (F.tower.history n).stageDerivative_at_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n)
    (hyG n) hDt'

/-- **锐形 birth 关系（`_P6HN`，PROVED）**：record 字段 `nominal_small`（`r < δ(tᵢ)²·ρ(tᵢ)`）、`scale_eq`
（`N = r⁻²`）、`recenter_scale_comparison`（`recenterConstant·δ(tᵢ) ≤ 1/2` 时 `S ≥ N/2`）⇒
`(2·(δ(tᵢ)²·ρ(tᵢ))²)⁻¹ < S`。树内 `inv_two_mul_sq_lt_static_scale` 只给弱化形 `(2ρ₀²)⁻¹ < S`。 -/
theorem static_scale_gt_birth_P6HN {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2) :
    (2 * (p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2)⁻¹ <
      (R.static b).neck.scale := by
  have ht : 0 ≤ H.time i.succ := H.time_nonneg i.succ
  have hδpos := p.delta_pos _ ht
  have hρpos := p.neckRadius_pos _ ht
  have hn := R.nominal_small ⟨b.1.1⟩
  have hnpos := R.nominal_pos ⟨b.1.1⟩
  have hcmp := R.recenter_scale_comparison b
  have hsc := R.scale_eq b.1.1
  have hdα := R.delta_le b.1.1
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  set r := R.nominalRadius ⟨b.1.1⟩ with hrdef
  set N := (R.neck b.1.1).scale with hNdef
  set S := (R.static b).neck.scale with hSdef
  set ρ' := p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  have hNlow : (ρ' ^ 2)⁻¹ < N := by
    rw [hsc]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (by nlinarith)
  have hNpos : 0 < N := lt_trans (by positivity) hNlow
  have hΛδα : p.recenterConstant * R.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hdα (by linarith)).trans hΛδ
  have hhalf : 1 / 2 ≤ S / N := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  have hS : N / 2 ≤ S := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * ρ' ^ 2)⁻¹ = (ρ' ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  rw [h2]
  linarith

/-- **跳比 ⇒ `hceilcap`（`_P6HN`，PROVED）**：若 profile 半径在 cap 出生时刻 `tᵢ` 与观测时刻之间满足
`ρ(tᵢ) ≤ Λ·ρₜ`，且 `δ(tᵢ)⁴ ≤ Cb/(2Λ²)`，则天花板 `(ρₜ²)⁻¹ ≤ Cb·scale`。所缺 profile 条款（BLOCKED，
C12 候选）恰是 `ρ(tᵢ) ≤ Λ·ρ(t)`（`tᵢ ≤ t ≤ tᵢ + θ₀/scale`）。 -/
theorem ceilcap_of_ratio_P6HN {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {Λ Cb ρt : ℝ} (hΛ : 0 < Λ) (hCb : 0 < Cb) (hρt : 0 < ρt)
    (hratio : p.neckRadius (H.time i.succ) ≤ Λ * ρt)
    (hδ : p.delta (H.time i.succ) ^ 4 ≤ Cb / (2 * Λ ^ 2)) :
    (ρt ^ 2)⁻¹ ≤ Cb * (R.static b).neck.scale := by
  have hS := static_scale_gt_birth_P6HN R b hΛδ
  have ht : 0 ≤ H.time i.succ := H.time_nonneg i.succ
  have hρi := p.neckRadius_pos _ ht
  have hδpos := p.delta_pos _ ht
  set d := p.delta (H.time i.succ) with hd
  set ρi := p.neckRadius (H.time i.succ) with hρidef
  set X := 2 * (d ^ 2 * ρi) ^ 2 with hXdef
  have hXpos : 0 < X := by positivity
  have hδ' : d ^ 4 * (2 * Λ ^ 2) ≤ Cb := by rwa [le_div_iff₀ (by positivity)] at hδ
  have hsq : ρi ^ 2 ≤ Λ ^ 2 * ρt ^ 2 := by
    have := pow_le_pow_left₀ hρi.le hratio 2
    nlinarith [this]
  have hX : X ≤ Cb * ρt ^ 2 := by
    have h1 : X = 2 * d ^ 4 * ρi ^ 2 := by rw [hXdef]; ring
    rw [h1]
    have h2 : 2 * d ^ 4 * ρi ^ 2 ≤ 2 * d ^ 4 * (Λ ^ 2 * ρt ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith [h2, hδ', sq_nonneg ρt]
  have hinv : (Cb * ρt ^ 2)⁻¹ ≤ X⁻¹ := inv_anti₀ hXpos hX
  have hid : Cb * (Cb * ρt ^ 2)⁻¹ = (ρt ^ 2)⁻¹ := by
    field_simp
  calc (ρt ^ 2)⁻¹ = Cb * (Cb * ρt ^ 2)⁻¹ := hid.symm
    _ ≤ Cb * X⁻¹ := mul_le_mul_of_nonneg_left hinv hCb.le
    _ ≤ Cb * (R.static b).neck.scale := mul_le_mul_of_nonneg_left hS.le hCb.le

/-- **跳比 ⇒ (SEP-ρ)（`_P6HN`，PROVED）**：`ceilcap_of_ratio_P6HN` 取 `Cb := 1/(n+1)`：profile 跳比
`ρ(tᵢ) ≤ Λ·ρₜ` 与 `δ(tᵢ)⁴·(2Λ²·(n+1)) ≤ 1`（`δ_n → 0`）⇒ `(n+1)·(ρₜ²)⁻¹ ≤ scale`。 -/
theorem sepRho_of_ratio_P6HN {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {Λ ρt : ℝ} (n : ℕ) (hΛ : 0 < Λ) (hρt : 0 < ρt)
    (hratio : p.neckRadius (H.time i.succ) ≤ Λ * ρt)
    (hδ : p.delta (H.time i.succ) ^ 4 * (2 * Λ ^ 2 * ((n : ℝ) + 1)) ≤ 1) :
    ((n : ℝ) + 1) * (ρt ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hδ' : p.delta (H.time i.succ) ^ 4 ≤ ((n : ℝ) + 1)⁻¹ / (2 * Λ ^ 2) := by
    rw [le_div_iff₀ (by positivity), ← one_div, le_div_iff₀ hn]
    linarith
  have h := ceilcap_of_ratio_P6HN R b hΛδ hΛ (inv_pos.mpr hn) hρt hratio hδ'
  have h2 := mul_le_mul_of_nonneg_left h hn.le
  rwa [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h2

/-- consumer（`_P6HN`）：G2 主形在 `θ := fun _ => θ₀` 处的结论（`∀ n`）喂 SLICE-BCBD G5
`sliceBCBD_kernel_fresh_theta_ev_P6SB` 的 `hnotK` 槽（`∀ᶠ n`，θ₀ 形，`‖x‖ < n + 2`）。 -/
example {θ₀ : ℝ} {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {t T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hnot : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          (fun _ : ℕ => θ₀) n * (((recordsK n i hi).static b).neck.scale)⁻¹) :
    ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ :=
  Filter.Eventually.of_forall hnot

/-- consumer（`_P6HN`）：G2 主形在 `θ := fun n => 1 − 1/(n+2)` 处的结论逐字 = (CWW)
`hnotK_of_capWindowWitness_P6R2` 的结论（即 closed 主形 `hnotK` binder）。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {t T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hnot : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ (fun m : ℕ => 1 - 1 / ((m : ℝ) + 2)) n *
          (((recordsK n i hi).static b).neck.scale)⁻¹) :
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ :=
  hnot

/-- consumer（`_P6HN`）：`θ n = 1 − 1/(n+2) < 1`，G2 主形的年龄前提可取 (CWW) 对角序列。 -/
example : ∀ n : ℕ, (fun m : ℕ => 1 - 1 / ((m : ℝ) + 2)) n < 1 := fun n => by
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  change 1 - 1 / ((n : ℝ) + 2) < 1
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
