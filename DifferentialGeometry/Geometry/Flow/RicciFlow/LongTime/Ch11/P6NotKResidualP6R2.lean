import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

/-!
# `hnotK`（= `hcwp` 的主形入口）的残余义务（O-CH11-P6REST2 G3，后缀 `_P6R2`）

closed 主形 `false_of_selection_eventSlab_late_closed_Cg_P6S3` 的 `hnotK`：`∀ n`，选出点 `yG n` 不是
late cap-window 点（`‖x‖ < n+2`，年龄 `≤ (1 − 1/(n+2))/scale`）。两种最小合同（显式 binder，不包装成
producer；设计文档 §5）：

* **(CWS) + (SEP′)**（建议）：`hnotK_of_capWindowScalar_P6R2`。(CWS) late cap-window 点在 `t n` 的标量
  下界 `η·scale ≤ R(t n, z)`（`η` 对 `n`、窗口半径、年龄一致）；(SEP′) 新近 record（`t − tᵢ ≤ scale⁻¹`）
  `R n < η·scale`。反证 `R n = R(t n, yG n) ≥ η·scale > R n`，**不需要 witness**；(SEP′) 与 `hdistQ`
  的 (SEP) 同源（新近手术尺度 ≫ 选出点曲率）。
* **(CWW)** + 时间半：`hnotK_of_capWindowWitness_P6R2`。(CWW) cap-window ⇒ `SpatialCanonicalWitness`
  （常数 `(ε, C1', C2')` 在 `n` 之前给定 ⇒ 对 `Dw = n+2 → ∞`、`θ = 1 − 1/(n+2) → 1` 一致；树内
  `exists_capWindowPoint_nonNeck_spatialCanonicalWitness` 的 `Cs` 依赖 `Dw`，故是真实义务）；时间半
  `|∂ₜR| ≤ Ctime' R²` 由 `hslabK` + `hqR` + `Ctime ≤ Ctime'` 生产；`hsel` 收尾。
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

/-- **`hnotK` ⇐ (CWS) + (SEP′)（`_P6R2`）**：结论逐字 = closed 主形 `hnotK` binder。 -/
theorem hnotK_of_capWindowScalar_P6R2 {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {R : ℕ → ℝ}
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) {η : ℝ}
    (hcws : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
      ‖x.val‖ < ((n : ℝ) + 1) + 1 →
      t n - (K n).time i.succ ≤
        (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      η * ((recordsK n i hi).static b).neck.scale ≤
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z)
    (hsep : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale) :
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  rintro n ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩
  have h1 := hcws n i hi hl (yG n) A b x hx hxn hage
  have hs : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hsinv : 0 < (((recordsK n i hi).static b).neck.scale)⁻¹ := inv_pos.mpr hs
  have hn2 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
  have hage' : t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    refine hage.trans ?_
    nlinarith
  have h2 := hsep n i hi b hl hage'
  rw [hRn n] at h2
  linarith

/-- slab 内 stage 形导数界（`_P6R2`；P6R WIP 同名引理的独立重证）：event slab `j` 的 incoming
导数界（阈值 `q`）⇒ `m = j.castSucc` 上的 `stageMetric` 形导数界。 -/
theorem stageDerivative_of_incoming_P6R2 (K : RetainedCoreHistory.{u}) {q : ℝ}
    {Ctime : ℝ≥0} (j : Fin K.eventCount)
    (h1 : ∀ (y : (K.stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo (K.time j.castSucc) (K.time j.succ) →
      q < (K.toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (K.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        Ctime * (K.toHistory.event j).incoming.flow.scalar t y ^ 2)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (hlo : K.time j.castSucc < v) (hv2 : v < K.time j.succ) (z : (K.stage m).Carrier)
    (hR : q < metricScalarAt (K.toHistory.stageMetric m v) z) :
    |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) z) (Iic v) v| ≤
      Ctime * metricScalarAt (K.toHistory.stageMetric m v) z ^ 2 := by
  subst hm
  have hfun : ∀ t, metricScalarAt (K.toHistory.stageMetric j.castSucc t) z =
      (K.toHistory.event j).incoming.flow.scalar t z := fun t => by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    rfl
  simp only [hfun] at hR ⊢
  exact h1 z v ⟨hlo, hv2⟩ hR

/-- **`hnotK` ⇐ (CWW) + 时间半 + `hsel`（`_P6R2`）**：结论逐字 = closed 主形 `hnotK` binder。(CWW)
`hcww`：late cap-window 配置 ⇒ `(σ n, y n)` 处的 spatial canonical witness（常数 `ε C1' C2'`）。 -/
theorem hnotK_of_capWindowWitness_P6R2 {ε C1' C2' : ℝ} {Ctime Ctime' : ℝ≥0}
    (hCt : Ctime ≤ Ctime') {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) {Q T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {Kh : ℕ → ObservedHistory.{u}} (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n))
    (hcww : ∀ n, (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ε C1' C2' (y n), W.capTubeHasNeckChart ε) :
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  subst hKh
  intro n hC
  apply hsel n
  have hjt' : (K n).time (j n).castSucc < (σ n : ℝ) := by
    rw [hσ n]
    exact hjt n
  have htj' : (σ n : ℝ) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) hjt'.le htj'
  have hQ : Q n < metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) := by
    rw [(K n).scalar_of_incoming_P6X (j n) hact.symm (σ n) (yG n) (y n) (hyG n), hσ n]
    exact lt_of_le_of_lt (le_max_right _ _) (hqR n)
  have h1 : ∀ (z : ((K n).stage (j n).castSucc).Carrier) (s : ℝ),
      s ∈ Ioo ((K n).time (j n).castSucc) ((K n).time (j n).succ) →
      Q n < ((K n).toHistory.event (j n)).incoming.flow.scalar s z →
      |derivWithin (fun v => ((K n).toHistory.event (j n)).incoming.flow.scalar v z) (Iic s) s| ≤
        (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar s z ^ 2 :=
    fun z s hs hR => (hslabK n (j n) (Fin.castSucc_lt_last (j n)) z s hs hR).trans
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCt) (sq_nonneg _))
  refine ⟨hcww n hC, fun _ _ => ?_⟩
  exact (K n).stageDerivative_of_incoming_P6R2 (j n) h1 hact.symm (σ n) hjt' htj' (y n) hQ

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
