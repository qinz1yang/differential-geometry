import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthP6AN4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthFinalP6AN4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

/-!
# ANCHOR 第四轮 G2b：final 合同三字段 ⇐ hgood / final `hkappa` / hseedTop（O-CH11-ANCHOR4，后缀 `_P6AN4`）

G2 的 final 合同 `PickedBallShortWindow_final_P6AN4` 在 top 点（`v := t n`、`w := yG n`，
`σ = t` 在 final slab，`activeStage σ = last`）由 selection 数据付，照 event 支（ANCHOR3 G1/G4 + 本车道 G1）：
* witness ⇐ hgood（top 时刻；中心 seed 余量在 `v = σ`、`w ≅ y` 时平凡，`Rad ≤ L/2`）；
* κ ⇐ final `hkappa`（P6CD / FINCOND 层 trace-local κ；窗口内 `τ` 与 `σ` 同 stage `last`，平凡 trace，
  `kappa_sameStage_of_trace_P6AN3`）；
* 梯度 ⇐ hgood 的 witness `gradient` 字段 + **hseedTop**（同 G1 的 binder，activeStage 形对 event / final 通用；
  BLOCKED 同因：三条已知来源循环，repair = guarded ShortSLT）。
stage 度量桥：`activeStage τ = last`（`activeStage_eq_last_of_time_last_le`）+ `stageMetric_last_of_lt`
（`= finalSlab` 度量；`restrictIncoming` 的 flow = `timeRestrict`，`base` 定义等）。
* `pickedBallShortWindow_final_of_hgood_P6AN4`（PROVED ⇐ hgood + hseedTop@n + hkappa@n + 时间域）/ 序列版
  `pickedBallShortWindow_final_seq_of_hgood_P6AN4`；
* 组合 `topAnchorInputs_final_of_hgood_P6AN4` 与 final 全链 `hdistW_finalSlab_of_hgood_local_P6AN4`
  （= ANCHOR3 final 孪生，`hin` 换成 hgood + hseedTop + 同一个 `hkappa`；无 `GradientBoundBefore`、无 hpick）。
非循环：前提中无 `hdistW` 槽 / `HU` / `hgapJ` / `hclosG` / `CanonicalLateCore` / `hspine` /
`GradientBoundBefore`。
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

section FinalHgood

/-- **final 合同 ⇐ hgood + hseedTop + `hkappa`（`_P6AN4`，PROVED ⇐ 显式输入，单个 `n`）**：top 点 `v := t n`、
`w := yG n`（`σ n = t n` 在 final slab），阈值 `Cg·R_n`，`C₂ ≤ Cgrad`，`Rad ≤ L_n/2`、`Rad ≤ D`、`β ≤ T`。
(1) witness ⇐ hgood 在 `v = σ`（`d_σ(seed, x) ≤ d_σ(seed, y) + Rad/√R ≤ dσ + L/√R`）；
(2) 梯度 ⇐ hseedTop 给窗口点的 seed 余量 + hgood 在 `τ = v′` 的 witness 的 `gradient` 字段；
(3) κ ⇐ `hK`（= `hkappa D T` 在 `n` 处）+ 平凡 trace。
三处都经 `activeStage = last` 的一般化 `k` + `subst` 与 `stageMetric_last_of_lt`。 -/
theorem pickedBallShortWindow_final_of_hgood_P6AN4 {Cg β Rad D T κ : ℝ} {Cgrad : ℝ≥0}
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
    PickedBallShortWindow_final_P6AN4 β Rad (Cg * R n) (ρnc n) κ eps C1 C2 Cgrad (K n)
      ((htl n).trans (htK n)) (t n) (yG n) := by
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hv1 : (K n).time (Fin.last (K n).eventCount) < σ n := by
    rw [hσ n]
    exact htl n
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hv1.le
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRpos
  have hRadL' : Rad ≤ L n := by linarith
  refine ⟨fun x hx hRx => ?_, fun x hx v' hv' hwin hRx ξ => ?_,
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
        riemannianEDistOf ((K n).toHistory.stageMetric k v') ((seedTrace n).point k h1' h2') x'' ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
      intro k hk
      subst hk
      intro h1' h2' x'' yk hy hx'' htk hRk
      obtain rfl := eq_of_heq hy
      exact hW x'' hx'' v' hs1 hs2 htk hRk
    have hx' : x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).eventCount)
        (σ n)) (yG n) (Rad / Real.sqrt (R n)) := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin), hσ n, hRn n]
      exact hx
    have hRv : Cg * R n < metricScalarAt ((K n).toHistory.stageMetric
        (Fin.last (K n).eventCount) v') x := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)]
      exact hRx
    have hd := key2 (Fin.last (K n).eventCount) hact h1 h2 x (yG n) (hyG n) hx' hv'.1 hRv
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

/-- **final 合同序列版（`_P6AN4`，PROVED ⇐ hgood + hseedTop + `hkappa` + `hwin` + `L → ∞`）**：对每个 `Rad`，
eventually
`PickedBallShortWindow_final_P6AN4 β Rad (Cg·R_n) (ρnc n) κ eps C1 C2 Cgrad (K n) _ (t n) (yG n)`
（`D := max Rad 1`、`T := max β 1`；`L ≥ max (2 Rad) (max β 1)` 给 `Rad ≤ L/2`、`0 ≤ L`、`β ≤ L²`）。 -/
theorem pickedBallShortWindow_final_seq_of_hgood_P6AN4 {Cg β κ : ℝ} {Cgrad : ℝ≥0}
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
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
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
      PickedBallShortWindow_final_P6AN4 β Rad (Cg * R n) (ρnc n) κ eps C1 C2 Cgrad (K n)
        ((htl n).trans (htK n)) (t n) (yG n) := by
  intro Rad
  filter_upwards [hseedTop Rad, hkappa (max Rad 1) (max β 1) (lt_max_of_lt_right one_pos)
    (lt_max_of_lt_right one_pos), hwin β hβ,
    hL.eventually_ge_atTop (max (2 * Rad) (max β 1))] with n hW hK ha hLn
  have hL1 : 1 ≤ L n := (le_max_right β 1).trans ((le_max_right _ _).trans hLn)
  have hβL : β ≤ L n ^ 2 := by
    nlinarith [le_max_left β 1, (le_max_right (2 * Rad) (max β 1)).trans hLn]
  have hdiv : β / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hβL (hRpos n).le
  have hRadL : Rad ≤ L n / 2 := by linarith [(le_max_left (2 * Rad) (max β 1)).trans hLn]
  exact pickedBallShortWindow_final_of_hgood_P6AN4 K hgood hC2 htl htK hσ hyG hRn n (hRpos n)
    (by linarith) hRadL (le_max_left Rad 1) (le_max_left β 1) hκ ha (by linarith) hW hK

end FinalHgood

section FinalHgoodChain

/-- **`topAnchorInputs_final_of_hgood_P6AN4`（G2b 组合，PROVISIONAL：binder = hseedTop（BLOCKED，见 G1）+
FINCOND 层 supplies（含 final `hkappa`）+ hgood；导数 `hslab / hderG` = J10GEN）**：= G2
`topAnchorInputs_final_of_pickedBall_P6AN4`，`hpb` 由
`pickedBallShortWindow_final_seq_of_hgood_P6AN4` 供
（`qthr := Cg·R_n`、`Cq := Cg`、`ε := eps` of hgood）。无 hpick、无 `GradientBoundBefore`。 -/
theorem topAnchorInputs_final_of_hgood_P6AN4 {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
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
    (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount))
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n))
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
    (hL : Tendsto L atTop atTop) (hε : ε ≤ coneAccuracy) {κ : ℝ} (hκ : 0 < κ) {Cgrad : ℝ≥0}
    {ρnc : ℕ → ℝ} (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hC2 : C2 ≤ (Cgrad : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hseedTop : ∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
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
    TopAnchorInputs_P6AN2 β (fun n => (K n).prefixAt (Fin.last (K n).eventCount))
      (fun n => (K n).prefixAt_time_last _) (fun n => (K n).horizon)
      (fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl)
      (fun n => (K n).final_initial ((htl n).trans (htK n))) t yG := by
  obtain rfl : G = fun n => ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl := funext hG
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  refine topAnchorInputs_final_of_pickedBall_P6AN4 hβ htl htK (fun _ => rfl) hcan hqcan hpar hscale
    hθcap hphi hpinch hslab hderG hqR hnot hT₀ hRt hε hκ (Cq := Cg) (qthr := fun n => Cg * R n)
    (ρnc := ρnc) (fun n => ⟨mul_pos hCg (hRpos n), le_of_eq (by rw [hRn n])⟩) ?_
    (pickedBallShortWindow_final_seq_of_hgood_P6AN4 K hgood hC2 htl htK hσ hyG hRn hRpos hβ0 hκ.le
      hwin hL hseedTop hkappa)
  refine hradii.congr fun n => ?_
  rw [hRn n]

/-- **`hdistW_finalSlab_of_hgood_local_P6AN4`（G2b final 全链，PROVISIONAL：
binder = hseedTop（BLOCKED，见 G1）+ `hbcadC`
+ FINCOND 层 supplies（含 `hkappa / hseed / hwitC`）+ hgood + K0 / HI；
导数 `hslab / hderG` = J10GEN）**：
= ANCHOR3 `hscalW_finalSlab_to_hdistW_P6AN3`，`hin` 换成 `β ≤ 1/2` + hgood 块（`HgoodCg_C11SH Cg Kh …`、
`εg ≤ coneAccuracy`、`C2g ≤ Cgrad`、hseedTop，与 G1 event 全链逐字同形），`hin` 由
`topAnchorInputs_final_of_hgood_P6AN4` 供（κ 用链上**同一个** `hkappa`；`subst hKh`）。结论 = `hdistW` 槽逐字
（final 支）。无 hpick、无 `GradientBoundBefore`、无 final 合同 binder。 -/
theorem hdistW_finalSlab_of_hgood_local_P6AN4 :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
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
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
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
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (Kh n).time ((Kh n).activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x →
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
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 Kh hKh
    σ y R hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC hbcadC Tn
    aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood Cgrad hC2 hseedTop hL hsmall
    hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  have hin := topAnchorInputs_final_of_hgood_P6AN4 hβ hβ2 htl htK hG hcan hqcan hpar hscale hθcap
    hphi hpinch hslab hderG hqR hnot hT₀ hRt hCg hgood hσ hyG hRn hL hεg hκ hradii hC2 hwin hseedTop
    hkappa
  exact hscalW_finalSlab_to_hdistW_P6AN3 hε hεX hεN hphi htl htK hG recordsF hHI hcan hδF hqcan
    hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hin (fun n => (K n).toHistory)
    rfl σ y R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC hbcadC Tn aSeed haT hsT has pT
    seedTrace L r hL hsmall hclock hRr hwin ha₁ hpin

/-- consumer（G2b，`_P6AN4`）：final 合同序列版即 G2 `topAnchorInputs_final_of_pickedBall_P6AN4` 的 `hpb` 槽
（`qthr := Cg·R_n`）；hseedTop 与 G1 event 支同一 binder 形（activeStage 形对 event / final 通用）。 -/
example := @pickedBallShortWindow_final_seq_of_hgood_P6AN4.{u}

end FinalHgoodChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
