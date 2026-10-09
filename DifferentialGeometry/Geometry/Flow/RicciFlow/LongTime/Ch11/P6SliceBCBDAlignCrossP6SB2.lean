import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDCeilP6SB

/-!
# R4 中心对齐 ② 的可比性由 crossing 连续性付（O-CH11-SLICE-BCBD2 G3x，后缀 `_P6SB2`）

KAPPA-ADAPT R4 的 driver 中心是 `(tt, y′)`：`y′ ≍ p′`，`p′` 是塔中心 `y ≍ q`（`σ = time i⁺`）的
RegularCrossing 前像，`tt ↑ time i⁺`；driver 尺度 `R_k = R(σ, y) = R_out(q)`
（`hkappaC_tower_of_fresh_P6KA` 的 `R k = R(σ k, y k)`，`σ k = time (i k).succ`）。故 driver `R ≠ R(ys)`，
G3 的 ① 不直接适用，需要 ② 的中心可比性 `R(tt, y′) ≤ C·R_k`。本文件用 terminal 连续性 + crossing
标量相等付它（不用 isTracedRegion）：
* `ObservedHistory.eventually_centerScalar_lt_of_regularCrossing_P6SB2`（PROVED）：
  `RegularCrossing p′ q`、`R_out(q) < C` ⇒ `∀ᶠ t ∈ 𝓝[<] time i⁺`，`stageAt t` 中与 `p′` HEq 的点标量 `< C`
  （`TerminalLimitMetric.tendsto_metricScalarAt` + `RegularCrossing.scalar_eq`）；
* `ObservedHistory.towerScale_eq_output_P6SB2`（PROVED）：`σ = time i⁺`、`y ≍ q` ⇒ `R(σ, y) = R_out(q)`；
* `ObservedHistory.hanchor0_driver_of_kernel_comparable_P6SB2`（PROVED）：② 的一般形（可比性 `hle` 为输入，
  常数 `C > 0` 任意）；
* consumer `ObservedHistory.exists_badTime_comparable_P6SB2`（PROVED）：R4 第 1 步的选点——坏时刻
  `∃ᶠ t ∈ 𝓝[<] time i⁺` 可取在可比性集合内（`Frequently.and_eventually`），于是 ② 的 `hle` 以 `C = 2` 成立。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- `stage i⁻` 的点（经 HEq）在 `stageMetric i⁻ v` 下的标量 = event `i` incoming 度量下的标量（`_P6SB2`）。 -/
theorem scalar_stage_castSucc_of_heq_P6SB2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : i.castSucc = m) (v : ℝ)
    (p' : (H.stage i.castSucc).Carrier) (x : (H.stage m).Carrier) (hx : HEq x p') :
    metricScalarAt (H.stageMetric m v) x =
      metricScalarAt ((H.event i).incoming.flow.base.metric v) p' := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [stageMetric_castSucc_apply]

/-- **crossing 中心标量的 terminal 连续性（`_P6SB2`，PROVED）**：`RegularCrossing p′ q`、`R_out(q) < C` ⇒
`t ↑ time i⁺` 时（`∀ᶠ t ∈ 𝓝[<] time i⁺`），`stageAt t` 中与 `p′` HEq 的点标量 `< C`。 -/
theorem eventually_centerScalar_lt_of_regularCrossing_P6SB2 (H : ObservedHistory.{u})
    (i : Fin H.eventCount) {p' : (H.stage i.castSucc).Carrier} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p' q) {C : ℝ}
    (hC : metricScalarAt (H.event i).outputMetric q < C) :
    ∀ᶠ t in 𝓝[<] H.time i.succ, ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t →
      ∀ y' : (H.stageAt tt).Carrier, HEq y' p' →
        metricScalarAt (H.stageMetric (H.activeStage tt) tt) y' < C := by
  have hp : p' ∈ (H.event i).incoming.terminalRegularOpen :=
    hcross.mem_terminalRegularRegion (H.event i)
  have h := (H.event i).terminal.tendsto_metricScalarAt ⟨p', hp⟩
  rw [MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) (p := ⟨p', hp⟩) hcross] at h
  have hev := h.eventually (gt_mem_nhds hC)
  have hIoo : Ioo (H.time i.castSucc) (H.time i.succ) ∈ 𝓝[<] H.time i.succ :=
    Ioo_mem_nhdsLT (H.time_strictMono i.castSucc_lt_succ)
  filter_upwards [hev, hIoo] with t ht hts
  intro tt htt y' hy'
  have hact : H.activeStage tt = i.castSucc :=
    (H.mem_stageDomain_iff tt i.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show (tt : ℝ) ∈ Ico (H.time i.castSucc) (H.time i.succ) from
          ⟨htt ▸ hts.1.le, htt ▸ hts.2⟩))
  rw [H.scalar_stage_castSucc_of_heq_P6SB2 i hact.symm tt p' y' hy', htt]
  exact ht

/-- **塔尺度 = output 标量（`_P6SB2`，PROVED）**：`σ = time i⁺`、`y ≍ q` ⇒ `R(σ, y) = R_out(q)`
（`hkappaC_tower_of_fresh_P6KA` 的 `R k` 与 crossing 端标量对齐）。 -/
theorem towerScale_eq_output_P6SB2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (σ : Icc (0 : ℝ) H.horizon) (hσ : (σ : ℝ) = H.time i.succ) (y : (H.stageAt σ).Carrier)
    (q : (H.stage i.succ).Carrier) (hyq : HEq y q) :
    metricScalarAt (H.stageMetric (H.activeStage σ) σ) y =
      metricScalarAt (H.event i).outputMetric q := by
  have hact : H.activeStage σ = i.succ := by
    have h := H.activeStage_at_time i.succ
    have he : σ = ⟨H.time i.succ, H.time_nonneg i.succ, H.time_le_horizon_at i.succ⟩ :=
      Subtype.ext hσ
    rw [he]
    exact h
  rw [hσ]
  exact scalar_output_of_stage_P6SB H i hact y q hyq

/-- **② 一般形（`_P6SB2`，PROVED）**：kernel 帧 `(K, j, ts, yG)`（中心标量 `Rc`）上的切片 BCBD +
eventually 中心可比性 `R(ts, ys) ≤ C·R`（`C > 0`）⇒ driver `hanchor0`（相对 `R`）逐字。 -/
theorem hanchor0_driver_of_kernel_comparable_P6SB2 (Hs : ℕ → ObservedHistory.{u})
    {K : ℕ → RetainedCoreHistory.{u}} (hHs : Hs = fun n => (K n).toHistory)
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    {j : ∀ n, Fin (K n).eventCount} {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hjt : ∀ n, (K n).time (j n).castSucc < (ts n : ℝ))
    (htj : ∀ n, (ts n : ℝ) < (K n).time (j n).succ) (hyG : ∀ n, HEq (ys n) (yG n))
    (Rc : ℕ → ℝ) (hRc : ∀ n, 0 < Rc n)
    (hRcn : ∀ n, Rc n = ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) {C : ℝ} (hC : 0 < C)
    (hle : ∀ᶠ n in atTop,
      metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n) ≤ C * R n)
    (hK : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (ts n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (ts n) (yG n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n := by
  subst hHs
  have h' := hanchor0_obs_of_kernel_P6SB (t := fun n => (ts n : ℝ)) hjt htj ts (fun _ => rfl) ys yG
    hyG Rc hRcn hK
  refine hanchor0_rescale_P6SB2 (H := fun n => (K n).toHistory) hR hRc hC ?_ h'
  filter_upwards [hle] with n hn
  have hact : (K n).toHistory.activeStage (ts n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (ts n) (hjt n).le (htj n)
  rw [(K n).scalar_of_incoming_P6X (j n) hact.symm (ts n) (yG n) (ys n) (hyG n), ← hRcn n] at hn
  exact hn

/-- **consumer：R4 第 1 步选点（`_P6SB2`，PROVED）**：塔中心 `y ≍ q`（`σ = time i⁺`，`R = R(σ, y) > 0`）、
`RegularCrossing p′ q`；若坏时刻 `∃ᶠ t ∈ 𝓝[<] time i⁺`，则可取坏时刻 `t` 使 `stageAt t` 中与 `p′` HEq 的
中心满足 `R(t, y′) < 2·R`——② 的 `hle` 以 `C = 2` 成立，无 isTracedRegion 输入。 -/
theorem exists_badTime_comparable_P6SB2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (σ : Icc (0 : ℝ) H.horizon) (hσ : (σ : ℝ) = H.time i.succ) (y : (H.stageAt σ).Carrier)
    {p' : (H.stage i.castSucc).Carrier} {q : (H.stage i.succ).Carrier} (hyq : HEq y q)
    (hcross : (H.event i).RegularCrossing p' q)
    (hRpos : 0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) {Bad : ℝ → Prop}
    (hbad : ∃ᶠ t in 𝓝[<] H.time i.succ, Bad t) :
    ∃ t : ℝ, Bad t ∧ ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t →
      ∀ y' : (H.stageAt tt).Carrier, HEq y' p' →
        metricScalarAt (H.stageMetric (H.activeStage tt) tt) y' <
          2 * metricScalarAt (H.stageMetric (H.activeStage σ) σ) y := by
  have hR := H.towerScale_eq_output_P6SB2 i σ hσ y q hyq
  rw [hR] at hRpos ⊢
  have hlt : metricScalarAt (H.event i).outputMetric q <
      2 * metricScalarAt (H.event i).outputMetric q := by linarith
  exact (hbad.and_eventually
    (H.eventually_centerScalar_lt_of_regularCrossing_P6SB2 i hcross hlt)).exists

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
