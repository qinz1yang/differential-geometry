import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireP6GW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFifthFinalP6AN5

/-!
# GUARDWIRE G2b：hdistW final 全链 guarded 副本（O-CH11-GUARDWIRE，后缀 `_P6GW`）

ANCHOR5 final 全链 `hdistW_finalSlab_of_hgood_local_noJ10_P6AN5` 的 guarded 孪生
`hdistW_finalSlab_guarded_P6GW`：
ShortSLT 侧改 `ShortSLTGuarded_C11KX`（KSWEXIT `shortSLT_guarded_C11KX`，无 binder），U 侧数据只在 KSWEXIT
guard 点要求；
top 窗口 seed localization 的 binder 从 hseedTop 换成 **`hseedG`（guarded hseed）**：同一结论
（`d_s(seed(σ), x) ≤ d_σ(seed(σ), y) + L/√R_n`）只在 guard 点 `GuardKX_C11KX (R(σ, ·)) (Cg·R_n) Ct σ s
x` 上要求。
**`hseedG` 严格弱于 hseedTop、不循环**：guard 是逐点 worldline 预算（`2·Ct·max(R(σ, x), Cg·R_n)·(σ − s) ≤ 1`），不需要
top 球 ceiling（`hanchor0`）、hpick 或 `hdistW` 槽；event 支里同形的量已由 WSBASE point-anchor PROVED
（`hseedTopGuarded_seq_P6GW`）。final 支差的只是 point-anchor 核的 final-slab 孪生。

**`hseedG` 的 repair target（三项，后继车道 brief；均为 event-slab 核的 final-slab 孪生，数学无新内容）**：
1. P6M4 `ObservedHistory.edist_le_add_of_slab_ricci_P6M4`（I.8.3(b) 单 slab 距离畸变）→ final 孪生：slab 前提
   `e : Fin H.eventCount`、`H.time e.castSucc < s`、`t < H.time e.succ`、度量 `(H.event
e).incoming.flow.base.metric` 换成
   final slab `(K.finalSlab h).restrictIncoming le_rfl h le_rfl`（`K.time last < s ≤ t <
K.horizon`），点在 `K.stage last`；
   估 ≈ 60–90 行（证明体逐字，只换 flow 与时间区间端点）。
2. SEEDCL2 `ObservedHistory.seed_closure_firstExit_stopped_C11SC2`（及其内核
`firstExit_distance_stopped_C11SC2`）→ final 孪生：
   `j : Fin H.eventCount` / `h1 h2 : activeStage aSeed ≤ j.castSucc ≤ activeStage Tn` / `hv2 : v <
H.time j.succ` / 所有
   `(H.event j).incoming.flow` 换成 final slab flow 与 `Fin.last`（`h1 := Fin.le_last _`，`hv2 := v <
K.horizon`），seed 点
   `seedTrace.point (Fin.last _)`；`edist_lt_near_left_P6L4` 对 flow 通用可直接用；估 ≈ 170 行（stopped 核 35 +
closure 135）。
3. SEEDCL2 `windowScal_of_pickedTop_local_C11SC2`（+
`deriv_of_hgood_slab_Cg_C11SC2`、`scalar_le_two_mul_of_localDeriv_C11SC2`）
   → final 孪生：hgood 的 stage 桥由 `stageMetric_castSucc_apply` + `activeStage_eq_castSucc_C11PB` 换成
   `stageMetric_last_of_lt` + `activeStage_eq_last_of_time_last_le`（ANCHOR5 final 文件已用的两条）；估 ≈ 200
行。
三项交付后，WSBASE `windowSeed_pointAnchor_C11WB` 的 final 版（≈ 80 行，证明逐字）+ 本文件 `hseedG` 的 producer
（照 `hseedTopGuarded_seq_P6GW`，≈ 150 行）即消去 final 支 `hseedG`，`hdistW_finalSlab_guarded_P6GW` 结论不变。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section FinalGuarded

/-- **final 合同 guarded 形（`_P6GW`）**：ANCHOR4 `PickedBallShortWindow_final_P6AN4` 逐字，字段 (2) 梯度加
KSWEXIT
guard `GuardKX_C11KX (R(v, ·)) qthr Ct v v′ x`（witness / κ 字段不变）。 -/
def PickedBallShortWindowGuarded_final_P6GW (β Rad qthr ρ κ ε C1 C2 : ℝ) (Ct Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (h : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ)
    (w : (K.stage (Fin.last K.eventCount)).Carrier) : Prop :=
  (∀ x ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    qthr < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v x →
    ∃ W : SpatialCanonicalWitness
        (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) ∧
  (∀ x ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    ∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v,
    v - β / ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w ≤ v' →
    qthr < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x →
    GuardKX_C11KX (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v) qthr Ct v
      v' x →
    ∀ ξ : TangentSpace ThreeModel x,
      |scalarDifferential ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow v' x ξ| ≤
        Cgrad * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x *
          Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v' x) *
          Real.sqrt
            ((((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v').inner x
              ξ ξ)) ∧
  (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
    v - β / ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w ≤ (τ : ℝ) →
    (τ : ℝ) ≤ v → K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
    ∀ z ∈ riemannianBallOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) w
        (Rad / Real.sqrt (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v w)),
    ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
    ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
          (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
          (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))

/-- **弱化 / inhabitant（`_P6GW`，PROVED）**：未 guard 的 final 合同 ⇒ guarded（丢 guard）。 -/
theorem PickedBallShortWindow_final_P6AN4.guarded_P6GW {β Rad qthr ρ κ ε C1 C2 : ℝ} (Ct : ℝ≥0)
    {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}} {h : K.time (Fin.last K.eventCount) < K.horizon}
    {v : ℝ} {w : (K.stage (Fin.last K.eventCount)).Carrier}
    (hw : PickedBallShortWindow_final_P6AN4 β Rad qthr ρ κ ε C1 C2 Cgrad K h v w) :
    PickedBallShortWindowGuarded_final_P6GW β Rad qthr ρ κ ε C1 C2 Ct Cgrad K h v w :=
  ⟨hw.1, fun x hx v' hv' hwin hq _ ξ => hw.2.1 x hx v' hv' hwin hq ξ, hw.2.2⟩

/-- **final 合同（guarded）⇐ hgood + guarded hseed + `hkappa`（`_P6GW`，PROVED ⇐ 显式输入，单个 `n`）**：AN4
`pickedBallShortWindow_final_of_hgood_P6AN4` 的孪生；`hW`（窗口 seed localization）只在 guard 点
`GuardKX_C11KX (R(σ, ·)) (Cg·R_n) Ct σ s x` 上要求，梯度字段只在 guard 点产出。证明体逐字（guard 透传）。 -/
theorem pickedBallShortWindowGuarded_final_of_hgood_P6GW {Cg β Rad D T κ : ℝ} {Ct Cgrad : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    {ρnc : ℕ → ℝ} (n : ℕ) (hRpos : 0 < R n) (hL0 : 0 ≤ L n) (hRadL : Rad ≤ L n / 2)
    (hRadD : Rad ≤ D) (hβT : β ≤ T) (hκ : 0 ≤ κ)
    (hav : (aSeed n : ℝ) ≤ σ n - β / R n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n - β / R n)
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
            (Cg * R n) Ct (σ n) s x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hK :
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    PickedBallShortWindowGuarded_final_P6GW β Rad (Cg * R n) (ρnc n) κ eps C1 C2 Ct Cgrad (K n)
      ((htl n).trans (htK n)) (t n) (yG n) := by
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hv1 : (K n).time (Fin.last (K n).eventCount) < σ n := by
    rw [hσ n]
    exact htl n
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hv1.le
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRpos
  have hRadL' : Rad ≤ L n := by linarith
  refine ⟨fun x hx hRx => ?_, fun x hx v' hv' hwin hRx hg ξ => ?_,
    fun τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hball => ?_⟩
  · -- (1) witness at the top time
    have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
        (yk x' : ((K n).toHistory.stage k).Carrier), HEq (y n) yk →
        x' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k (σ n)) x' →
        ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k (σ n)) eps C1 C2 x',
          W.capTubeHasNeckChart eps := by
      intro k hk
      subst hk
      intro yk x' hy hx' hR'
      obtain rfl := eq_of_heq hy
      have hvL0 : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n := by
        have := div_nonneg (sq_nonneg (L n)) hRpos.le
        linarith
      have hd : riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (le_rfl.trans (hsT n)))) x' ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) :=
        (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add le_rfl (hx'.le.trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hRadL' hsq.le))))
      exact (hgood n (σ n) (has n) le_rfl hvL0 x' hd hR').1
    have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
        (σ n)) (yG n) (Rad / Real.sqrt (R n)) := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
      exact hx
    have hR' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric
        (Fin.last (K n).eventCount) (σ n)) x := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n]
      exact hRx.le
    have hres := key (Fin.last (K n).eventCount) hact (yG n) x (hyG n) hx' hR'
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n] at hres
    exact hres
  · -- (2) gradient on the window
    have hτ0 : 0 ≤ v' := ((K n).toHistory.time_nonneg _).trans hv'.1.le
    have hτh : v' ≤ (K n).toHistory.horizon := (hv'.2.trans (htK n)).le
    let τ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v', hτ0, hτh⟩
    have hactτ : (K n).toHistory.activeStage τ = Fin.last (K n).eventCount :=
      (K n).toHistory.activeStage_eq_last_of_time_last_le τ hv'.1.le
    have hs1 : (σ n : ℝ) - β / R n ≤ v' := by
      rw [hσ n, hRn n]
      exact hwin
    have hs2 : v' < σ n := by
      rw [hσ n]
      exact hv'.2
    have hav' : aSeed n ≤ τ := by
      change (aSeed n : ℝ) ≤ v'
      linarith
    have hvs' : τ ≤ σ n := hs2.le
    have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
      change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
      linarith
    have h1 : (K n).toHistory.activeStage (aSeed n) ≤ Fin.last (K n).eventCount :=
      Fin.le_last _
    have h2 : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (Tn n) :=
      hact ▸ (K n).toHistory.activeStage_mono (hsT n)
    have key2 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
        (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
        (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x'' yk : ((K n).toHistory.stage k).Carrier),
        HEq (y n) yk →
        x'' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
        (K n).toHistory.time k < v' →
        Cg * R n < metricScalarAt ((K n).toHistory.stageMetric k v') x'' →
        GuardKX_C11KX (metricScalarAt ((K n).toHistory.stageMetric k (σ n))) (Cg * R n) Ct
          (σ n) v' x'' →
        riemannianEDistOf ((K n).toHistory.stageMetric k v') ((seedTrace n).point k h1' h2') x'' ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
      intro k hk
      subst hk
      intro h1' h2' x'' yk hy hx'' htk hRk hgk
      obtain rfl := eq_of_heq hy
      exact hW x'' hx'' v' hs1 hs2 htk hRk hgk
    have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
        (σ n)) (yG n) (Rad / Real.sqrt (R n)) := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
      exact hx
    have hRv : Cg * R n < metricScalarAt ((K n).toHistory.stageMetric
        (Fin.last (K n).eventCount) v') x := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)]
      exact hRx
    have hg' : GuardKX_C11KX (metricScalarAt ((K n).toHistory.stageMetric
        (Fin.last (K n).eventCount) (σ n))) (Cg * R n) Ct (σ n) v' x := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n]
      exact hg
    have hd := key2 (Fin.last (K n).eventCount) hact h1 h2 x (yG n) (hyG n) hx' hv'.1 hRv
      hg'
    have key3 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
        (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
        (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
        riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
        ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k τ) eps C1 C2 x',
          W.capTubeHasNeckChart eps := by
      intro k hk
      subst hk
      intro h1' h2' x' hd' hR'
      exact (hgood n τ hav' hvs' hvL' x' hd' hR').1
    have hres := key3 (Fin.last (K n).eventCount) hactτ h1 h2 x hd hRv.le
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)] at hres
    obtain ⟨W, -⟩ := hres
    have hR0 : 0 ≤ (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v' x :=
      W.Q_pos.le
    exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · -- (3) κ on the window, trivial trace
    have hactτ : (K n).toHistory.activeStage τ = Fin.last (K n).eventCount :=
      (K n).toHistory.activeStage_eq_last_of_time_last_le τ hτ3.le
    have hτσ : τ ≤ σ n := by
      change (τ : ℝ) ≤ σ n
      rw [hσ n]
      exact hτ2
    have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
        (y' z' : ((K n).toHistory.stage k).Carrier), HEq (y n) y' →
        z' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) y' (D / Real.sqrt (R n)) →
        ∃ x : ((K n).toHistory.stageAt (σ n)).Carrier, HEq x z' ∧
          x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)) := by
      intro k hk
      subst hk
      intro y' z' hy hz'
      obtain rfl := eq_of_heq hy
      exact ⟨z', HEq.rfl, hz'⟩
    have hzD : z ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
        (σ n)) (yG n) (D / Real.sqrt (R n)) := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
      exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hRadD (Real.sqrt_nonneg _)) hz
    obtain ⟨x, hxz, hxb⟩ := key (Fin.last (K n).eventCount) hact (yG n) z (hyG n) hzD
    have hwin' : (σ n : ℝ) - T / R n ≤ τ := by
      have h1 := div_le_div_of_nonneg_right hβT hRpos.le
      have h2 : (t n : ℝ) - β / R n ≤ τ := by
        rw [hRn n]
        exact hτ1
      rw [hσ n]
      linarith
    exact kappa_sameStage_of_trace_P6AN3 (K n).toHistory hτσ (hactτ.trans hact.symm) x zz
      (hzz.trans hxz.symm) hκ hb hbρ (hK x hxb τ hτσ hwin') hball

/-- **序列版（`_P6GW`，PROVISIONAL：binder = guarded hseed `hseedG`）**：AN4
`pickedBallShortWindow_final_seq_of_hgood_P6AN4` 的孪生，`hseedTop` 换成**严格更弱**的 `hseedG`（同一结论只在 guard
点要求）。 -/
theorem pickedBallShortWindowGuarded_final_seq_P6GW {Cg β κ : ℝ} {Ct Cgrad : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : C2 ≤ (Cgrad : ℝ)) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β) (hκ : 0 ≤ κ) {ρnc : ℕ → ℝ}
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop)
    (hseedG : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
            (Cg * R n) Ct (σ n) s x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallShortWindowGuarded_final_P6GW β Rad (Cg * R n) (ρnc n) κ eps C1 C2 Ct Cgrad
        (K n)
        ((htl n).trans (htK n)) (t n) (yG n) := by
  intro Rad
  filter_upwards [hseedG Rad, hkappa (max Rad 1) (max β 1) (lt_max_of_lt_right one_pos)
    (lt_max_of_lt_right one_pos), hwin β hβ,
    hL.eventually_ge_atTop (max (2 * Rad) (max β 1))] with n hW hK ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans ((le_max_right _ _).trans hLn)
  have hβL : β ≤ L n ^ 2 := by
    nlinarith [le_max_left β 1, (le_max_right (2 * Rad) (max β 1)).trans hLn]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  have hRadL : Rad ≤ L n / 2 := by linarith [(le_max_left (2 * Rad) (max β 1)).trans hLn]
  exact pickedBallShortWindowGuarded_final_of_hgood_P6GW K hgood hC2 htl htK hσ hyG hRn n (hRpos n)
    (by linarith) hRadL (le_max_left Rad 1) (le_max_left β 1) hκ ha (by linarith) hW hK

/-- **`hlocalGuarded_final_P6GW`（`_P6GW`，PROVED ⇐ 显式输入，构形通用）**：ANCHOR5 `hlocal_final_noJ10_P6AN5`
的 guarded 孪生（输入梯度 / top 导数加 guard；prefix 导数、κ、pinching 不 guard，输出侧 guard 丢弃）。 -/
theorem hlocalGuarded_final_P6GW {β : ℝ} {s t : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {qthr ρnc : ℕ → ℝ}
    (hpin : ∀ᶠ n in atTop,
      (∀ j : Fin (H n).eventCount,
        Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
          (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
          Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi)
    (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hwg : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        qthr n < (G n).flow.scalar (t n) x →
        ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
          W.capTubeHasNeckChart ε) ∧
      (∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        GuardKX_C11KX ((G n).flow.scalar (t n)) (qthr n) Ctime (t n) v x →
        ∀ w : TangentSpace ThreeModel x,
          |scalarDifferential (G n).flow v x w| ≤
            Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
              Real.sqrt (((G n).flow.base.metric v).inner x w w)))
    (hkap : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
        let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ j : Fin (H n).eventCount,
        ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
          (Fin.le_last first) z,
        ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < ((H n).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        GuardKX_C11KX ((G n).flow.scalar (t n)) (qthr n) Ctime (t n) v x →
        |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
          Ctime * (G n).flow.scalar v x ^ 2) :
    ∃ ε : ℝ, ε ≤ coneAccuracy ∧ ∃ κ C1 C2 : ℝ, 0 < κ ∧
      ∃ (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi ∧ ∃ Cq : ℝ,
      ∀ Λ Rad : ℝ, 1 ≤ Λ → ∀ᶠ n in atTop,
      ∃ q ρ : ℝ, 0 < q ∧ q ≤ Cq * (G n).flow.scalar (t n) (y n) ∧
      ∃ U : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
        (∀ w ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
          w ∈ U) ∧
        (∀ x ∈ U, q < (G n).flow.scalar (t n) x →
          ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
            W.capTubeHasNeckChart ε) ∧
        (∀ j : Fin (H n).eventCount,
          ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < ((H n).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v z →
          |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
            Ctime * (G n).flow.scalar v x ^ 2) ∧
        (∀ x ∈ U, ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
          t n - β / (G n).flow.scalar (t n) (y n) ≤ v →
          q < (G n).flow.scalar v x → GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential (G n).flow v x w| ≤
              Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
                Real.sqrt (((G n).flow.base.metric v).inner x w w)) ∧
        (∀ j : Fin (H n).eventCount,
          Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
            (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩
              Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩
            Ici (t n - β / (G n).flow.scalar (t n) (y n))) phi ∧
        (∀ (T : ℝ) (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
          t n - β / (G n).flow.scalar (t n) (y n) ≤ T →
          let B := (H n).extendHorizon T ((hend n) ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
          let tm : Icc (0 : ℝ) B.horizon :=
            ⟨T, (H n).horizon_nonneg.trans ((hend n) ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, GuardKX_C11KX ((G n).flow.scalar (t n)) q Ctime (t n) T z →
          ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) ∧
        Λ ≤ ρ * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
  refine ⟨ε, hε, κ, C1, C2, hκ, Ctime, Cgrad, phi, hphi, Cq, fun Λ Rad _ => ?_⟩
  filter_upwards [hwg Rad, hkap Rad, hpin, hradii.eventually_ge_atTop Λ, hderE Rad, hderT Rad]
    with n hwgn hkn hpn hρn hEn hTn
  obtain ⟨hwit, hgrad⟩ := hwgn
  refine ⟨qthr n, ρnc n, (hqthr n).1, (hqthr n).2,
    riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
    fun w hw => hw, fun x hx hqx => hwit x hx hqx,
    fun i first hf z hz B v hv hvw hRv _ => hEn i first hf z hz B v hv hvw hRv,
    fun x hx v hv hvw hRv hg => hTn x hx v hv hvw hRv hg,
    fun x hx v hv hvw hRv hg ξ => hgrad x hx v hv hvw hRv hg ξ,
    hpn.1, hpn.2, ?_, hρn⟩
  intro T hT hTs hTt hTa _ _ z hz _
  exact hkn T hT hTs hTt hTa z hz

/-- **final top 时间导数（guarded，`_P6GW`，PROVED ⇐ hgood + guarded hseed 在 `n` 处）**：ANCHOR5
`hderT_final_of_hgood_witness_P6AN5` 的孪生；证明体逐字（guard 透传）。 -/
theorem hderTG_final_of_hgood_witness_P6GW {Cg β Rad : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    (n : ℕ) (hav : (aSeed n : ℝ) ≤ σ n - β / R n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ σ n - β / R n)
    (hW :
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
            (Cg * R n) Ct (σ n) s x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ x ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
    ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
        (Rad / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
      t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar v x →
      GuardKX_C11KX ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar (t n)) (Cg * R n) Ct (t n) v x →
      |derivWithin (fun w => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl).flow.scalar w x) (Iic v) v| ≤
        Ctg * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar v x ^ 2 := by
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hv1 : (K n).time (Fin.last (K n).eventCount) < σ n := by
    rw [hσ n]
    exact htl n
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hv1.le
  intro x hx v' hv' hwin hRx hg
  have hτ0 : 0 ≤ v' := ((K n).toHistory.time_nonneg _).trans hv'.1.le
  have hτh : v' < (K n).toHistory.horizon := hv'.2.trans (htK n)
  let τ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v', hτ0, hτh.le⟩
  have hactτ : (K n).toHistory.activeStage τ = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le τ hv'.1.le
  have hs1 : (σ n : ℝ) - β / R n ≤ v' := by
    rw [hσ n, hRn n]
    exact hwin
  have hs2 : v' < σ n := by
    rw [hσ n]
    exact hv'.2
  have hav' : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : τ ≤ σ n := hs2.le
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
    linarith
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ Fin.last (K n).eventCount :=
    Fin.le_last _
  have h2 : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (Tn n) :=
    hact ▸ (K n).toHistory.activeStage_mono (hsT n)
  have key2 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x'' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x'' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      (K n).toHistory.time k < v' →
      Cg * R n < metricScalarAt ((K n).toHistory.stageMetric k v') x'' →
      GuardKX_C11KX (metricScalarAt ((K n).toHistory.stageMetric k (σ n))) (Cg * R n) Ct
        (σ n) v' x'' →
      riemannianEDistOf ((K n).toHistory.stageMetric k v') ((seedTrace n).point k h1' h2') x'' ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x'' yk hy hx'' htk hRk hgk
    obtain rfl := eq_of_heq hy
    exact hW x'' hx'' v' hs1 hs2 htk hRk hgk
  have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
      (σ n)) (yG n) (Rad / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
    exact hx
  have hRv : Cg * R n < metricScalarAt ((K n).toHistory.stageMetric
      (Fin.last (K n).eventCount) v') x := by
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)]
    exact hRx
  have hg' : GuardKX_C11KX (metricScalarAt ((K n).toHistory.stageMetric
      (Fin.last (K n).eventCount) (σ n))) (Cg * R n) Ct (σ n) v' x := by
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n]
    exact hg
  have hd := key2 (Fin.last (K n).eventCount) hact h1 h2 x (yG n) (hyG n) hx' hv'.1 hRv
    hg'
  have key3 : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      (K n).toHistory.time k < (τ : ℝ) → (τ : ℝ) < (K n).toHistory.horizon →
      |derivWithin (fun s => metricScalarAt ((K n).toHistory.stageMetric k s) x')
          (Iic (τ : ℝ)) τ| ≤
        Ctg * metricScalarAt ((K n).toHistory.stageMetric k τ) x' ^ 2 := by
    intro k hk
    subst hk
    intro h1' h2' x' hd' hR'
    exact (hgood n τ hav' hvs' hvL' x' hd' hR').2
  have hres := key3 (Fin.last (K n).eventCount) hactτ h1 h2 x hd hRv.le hv'.1 hτh
  simp only [ObservedHistory.stageMetric_last_of_lt (H := (K n).toHistory) (h := hfin)] at hres
  exact hres

/-- **序列版（`_P6GW`，PROVISIONAL：binder = `hseedG`）**：`hderT_final_seq_of_hgood_P6AN5` 的孪生。 -/
theorem hderTG_final_seq_P6GW {Cg β : ℝ} {Ct : ℝ≥0} (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hβ : 0 < β)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop)
    (hseedG : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
            (Cg * R n) Ct (σ n) s x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
    ((htl n).trans (htK n)) le_rfl).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
        t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n) ≤ v →
        Cg * R n < (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar v x →
        GuardKX_C11KX ((((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n)) (Cg * R n) Ct (t n) v x →
        |derivWithin (fun w => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar w x) (Iic v) v| ≤
          Ctg * (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar v x ^ 2 := by
  intro Rad
  filter_upwards [hseedG Rad, hwin β hβ, hL.eventually_ge_atTop (max β 1)] with n hW ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans hLn
  have hβL : β ≤ L n ^ 2 := by nlinarith [le_max_left β 1]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  exact hderTG_final_of_hgood_witness_P6GW K hgood htl htK hσ hyG hRn n ha (by linarith) hW

/-- **`topAnchorInputsGuarded_final_of_pickedBall_P6GW`（`_P6GW`，PROVED ⇐ 显式输入）**：ANCHOR5
`topAnchorInputs_final_of_pickedBall_noJ10_P6AN5` 的 guarded 孪生；证明体逐字。 -/
theorem topAnchorInputsGuarded_final_of_pickedBall_P6GW {β : ℝ} (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop)
    (hRlim : Tendsto (fun n => (G n).flow.scalar (t n) (yG n)) atTop atTop)
    {ε : ℝ} (hε : ε ≤ coneAccuracy) {κ C1 C2 Cq : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {qthr ρnc : ℕ → ℝ}
    (hqthr : ∀ n, 0 < qthr n ∧ qthr n ≤ Cq * (G n).flow.scalar (t n) (yG n))
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt ((G n).flow.scalar (t n) (yG n))) atTop atTop)
    (hpb : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      PickedBallShortWindowGuarded_final_P6GW β Rad (qthr n) (ρnc n) κ ε C1 C2 Ctime Cgrad (K n)
        ((htl n).trans (htK n)) (t n) (yG n))
    (hderE : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ j : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        ∀ (first : Fin (((K n).prefixAt (Fin.last (K n).eventCount)).eventCount + 1))
          (hf : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        ∀ B : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory first
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) (Fin.le_last first) z,
        ∀ v ∈ Ioo (((K n).prefixAt (Fin.last (K n).eventCount)).time j.castSucc)
          (((K n).prefixAt (Fin.last (K n).eventCount)).time j.succ),
        t n - β / (G n).flow.scalar (t n) (yG n) ≤ v →
        qthr n <
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w =>
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar w
              (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime *
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderT : ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
        t n - β / (G n).flow.scalar (t n) (yG n) ≤ v →
        qthr n < (G n).flow.scalar v x →
        GuardKX_C11KX ((G n).flow.scalar (t n)) (qthr n) Ctime (t n) v x →
        |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
          Ctime * (G n).flow.scalar v x ^ 2) :
    TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  obtain ⟨hDlim, hDrad, hord, hacc, hθ⟩ := selectionSchedule_noJ10_P6AN5 hβ hpar hθcap
  have hscale0 : ∀ n i hi b, 0 < ((records n i hi).static b).neck.scale := fun n i hi b =>
    lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) (hqcan n)))
      (hscale n i hi b)
  have hpin : ∀ᶠ n in atTop,
      (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩
            Ici (t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
              ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))) phi) ∧
      Perelman.PhiAlmostNonnegative (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
          le_rfl ((htl n).trans (htK n)) le_rfl).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩
          Ici (t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
            ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n))) phi := by
    filter_upwards [hT₀ β] with n hT
    exact ⟨fun i v hv => (hpinch n).1 i v ⟨hv.1, hT.trans hv.2⟩,
      fun v hv => (hpinch n).2 v ⟨hv.1, hT.trans hv.2⟩⟩
  refine topAnchorInputsGuarded_of_local_P6GW
    (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
    (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (s := fun n => (K n).horizon) (y := yG)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).final_initial ((htl n).trans (htK n)))
    records hcan hscale0 hRlim hRt (hT₀ β) hDlim hDrad hord hacc hθ hnot ?_
  refine hlocalGuarded_final_P6GW (fun n => (K n).prefixAt_time_last _)
    (fun n => (K n).final_initial ((htl n).trans (htK n))) hε hκ hphi hpin
    hqthr hradii (fun Rad => (hpb Rad).mono fun n h => ⟨h.1, h.2.1⟩)
    (fun Rad => (hpb Rad).mono fun n h => ?_) hderE hderT
  exact (K n).tested_noncollapse_final_P6M ((htl n).trans (htK n))
    (a := t n - β / (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) (t := t n) _ h.2.2
    ((K n).prefixAt_time_last _)

/-- **`topAnchorInputsGuarded_final_of_hgood_P6GW`（`_P6GW`，PROVISIONAL：binder = `hseedG`（guarded
hseed，
严格弱于 hseedTop、不循环）+ `hslabSel`（J10 残余）+ final `hkappa` + hgood + FINCOND 层 supplies + `hR /
hRlim`）**：
ANCHOR5 `topAnchorInputs_final_of_hgood_noJ10_P6AN5` 的孪生；guard 常数 `Ctime + Ctg + 1`。 -/
theorem topAnchorInputsGuarded_final_of_hgood_P6GW {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
    {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl)
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier}
    {D θcap qcan T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
      T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
            (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
      (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) * t n) atTop atTop)
    {Cg : ℝ} (hCg : 0 < Cg)
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {ε C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hslabSel : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime
      (Cg * R n) (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount))
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hseedG : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
            (Cg * R n) ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) (σ n) s x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
        ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (K n).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K n).toHistory.activeStage v) le_rfl
            ((K n).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) r'') :
    TopAnchorInputsGuarded_P6GW β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hRlim' : Tendsto (fun n => (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl).flow.scalar (t n) (yG n)) atTop atTop :=
    hRlim.congr fun n => hRn n
  refine topAnchorInputsGuarded_final_of_pickedBall_P6GW hβ htl htK (fun _ => rfl) hcan hqcan hpar
    hscale hθcap hphi hpinch hnot hT₀ hRt hRlim' hε hκ (Cq := Cg) (qthr := fun n => Cg * R n)
    (ρnc := ρnc) (Ctime := Ctime + Ctg + 1)
    (fun n => ⟨mul_pos hCg (hR n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallShortWindowGuarded_final_seq_P6GW K hgood hC2 htl htK hσ hyG hRn hR hβ0 hκ.le
      hwin hL hseedG hkappa)
    (fun Rad => (hderE_of_slabSel_gen_P6AN5 (β := β) (s := fun n => (K n).horizon)
      (H := fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (G := fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) (y := yG) hslabSel Rad).mono
      fun _ h j first hf z hz B v hv hvw hRv =>
        le_add_coe_mul_sq_P6AN5 (le_add_coe_mul_sq_P6AN5 (h j first hf z hz B v hv hvw hRv)))
    (fun Rad => (hderTG_final_seq_P6GW K hgood htl htK hσ hyG hRn hR hβ0 hwin hL hseedG
      Rad).mono fun _ h x hx v hv hvw hRv hg =>
        le_add_coe_mul_sq_P6AN5 (le_add_coe_mul_sq'_P6AN5 (h x hx v hv hvw hRv hg)))
  refine hradii.congr fun n => ?_
  rw [hRn n]

end FinalGuarded

section FinalChain

/-- **G2b `hdistW_finalSlab_guarded_P6GW`（`_P6GW`，PROVISIONAL：binder = `hseedG`（guarded hseed，**严格弱于
hseedTop、不循环**；repair = point-anchor 三核的 final-slab 孪生，见文件头）+ `hdepthAF`（⇐ J10GEN2A final）+
`hslabSel`（J10 残余，阈值形不变，owner SLTLOCAL）+ final `hkappa` + hgood + FINCOND 层 supplies + K0 / HI +
`hR / hRlim`；**无 hseedTop**、无 `hqR`）**：ANCHOR5 `hdistW_finalSlab_of_hgood_local_noJ10_P6AN5`
的孪生，陈述只在
hseedTop 位加 guard（→ `hseedG`）；ShortSLT 侧由 KSWEXIT `shortSLT_guarded_C11KX` 付。结论 = `hdistW`
槽逐字（final 支）。 -/
theorem hdistW_finalSlab_guarded_P6GW :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      (hdepthAF : (∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
          ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
              (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
            (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (yG n)) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      (∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (Cg * R n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (Kh n).time ((Kh n).activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x →
          GuardKX_C11KX
            (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)))
            (Cg * R n) ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) (σ n) s x →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi hphi K t htl htK G hG D θcap qcan T₀ p δb records yG hcan hqcan hpar hscale hθcap
    hpinch hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R hσ hyG hRn hR hRlim κ hκ ρnc hradii hkappa hdepthAF
    Tn aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood hslabSel Cgrad hC2
    hseedG hL hsmall hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hin := topAnchorInputsGuarded_final_of_hgood_P6GW hβ hβ2 htl htK (fun _ => rfl) hcan hqcan
    hpar hscale hθcap hphi hpinch hnot hT₀ hRt hCg hgood hσ hyG hRn hR hRlim hslabSel hL hεg hκ
    hradii hC2 hwin hseedG hkappa
  have hanc := hanchor0_final_of_topInputsGuarded_P6GW hβ htl htK hin
  have hslabσ := hσfin_of_selection_P6AN3 htl htK (fun n => (K n).toHistory) rfl σ hσ
  exact ObservedHistory.hdistW_of_firstExit_final_P6DW2 (fun n => (K n).toHistory) Tn aSeed σ haT
    hsT has pT seedTrace y R L hR r hL hsmall hclock hRr hwin ha₁ hpin hslabσ.1 hslabσ.2
    (ObservedHistory.hscalW_final_eventually_of_subseqDriver_P6AN2 (fun n => (K n).toHistory) Tn
      aSeed σ haT hsT has pT seedTrace y R L hR (fun φ hφ _ => hdepthAF hanc φ hφ))

end FinalChain

/-- consumer（G2b，`_P6GW`）：旧 final 合同经弱化喂 guarded final top 输入（guarded 合同严格更弱）。 -/
example := @PickedBallShortWindow_final_P6AN4.guarded_P6GW.{u}

/-- consumer（G2b，`_P6GW`）：final 全链即 guarded final top-anchor 半的消费者。 -/
example := @hdistW_finalSlab_guarded_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
