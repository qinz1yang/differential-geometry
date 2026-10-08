import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedHICondKappaP6CK

/-!
# J10GEN3 G1：closed-kappa kernel 的 anchor 去 J10（O-CH11-J10GEN3，后缀 `_P6JG3`）

J10GEN2B 的四个 kernel 合同 `NotKKernel{,Dec}NoJ10_P6JB` / `FinalKernel{,Dec}NoJ10_P6JB` 只删 `hQR`；
其内部（closed-cond κ-only `P6ClosedHICondKappaP6CK:233–366`）`Q < R` 的三处非 prefix 用途是**同一现象**：
slab 导数阈值 `qcan = max (n+1) Q` 必须被 q_sel `Cg·R` 支配——anchor `hq2`（SLT 导数槽）、slice
`hqRR`（`hsliceR_lateHI_core_P6S3:288–292` 单切片 `qcan ≤ Cg·R` + birth `qcan ≤ Cbirth·scale`）、
hctrl `hqR'`（survival ODE；J10GEN2A `exists_hctrl_lateHI_noJ10_P6JA` 已换 ceiling 形）。本文件：
* `hderSel_of_selection_sameSlab_Cg_P6JG3`（PROVED）：同 slab 时间导数 ⇐ hgood 时间分量 + `hdistW`；
* `RetainedCoreHistory.hanchor0_lateW_noJ10_P6JG3`（PROVISIONAL[`hslabsSel`]）：anchor 孪生，无 `qcan`
  / `hqR` / `hq2`；前 slab 导数槽 `hslabsSel` **= J10 残余**（导数阈值 `Q ≤ Cg·R` 的换皮，不算去 J10）；
* `hslabsSel_of_global_P6JG3`（PROVED 接线）：ANCHOR5 口径的全局 `EventSlabsDerivative Ctime q` ⇒ 槽；
* consumer `hanchor0_eventSlab_noJ10_P6JG3`（PROVISIONAL[`hslabsSel`]）：kernel 帧（`H := prefixAt`、
  `G := event incoming`、`q := Cg·R`），hW / hgrad / hder / κ 侧全部由 kernel 自带前提付，只剩 `hslabsSel`。
kernel 本身仍 BLOCKED（精确缺口表见 DELIVERIES 块与 state）。生成器 `build-logs/scratch/O-CH11-J10GEN3/gen1.py` /
`gen1b.py`（从 tracked 文本 assert 替换）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-- （`_P6JG3H`，`P6CondBridgeP6CD` private helper 逐字副本）首末 stage 指标相等时的单点 trace。 -/
theorem exists_trace_of_stage_eq_P6JG3H (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- slab 内部时刻的 `activeStage`。 -/
theorem activeStage_eq_of_mem_slab_P6JG3H (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- 球成员 incoming → `stageMetric m`（`m = j.castSucc`）。 -/
theorem mem_ball_of_incoming_P6JG3H (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v r : ℝ)
    (z yG : (K.stage j.castSucc).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG)
    (h : z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) yG r) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r := by
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_castSucc_apply]
  exact h

/-- 标量 `stageMetric m` ↔ incoming（`m = j.castSucc`）。 -/
theorem scalar_of_incoming_P6JG3H (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x =
      (K.toHistory.event j).incoming.flow.scalar v z := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- witness `stageMetric m` → incoming（`m = j.castSucc`）。 -/
theorem witness_of_stage_P6JG3H (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ) {ε C1 C2 : ℝ}
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v) ε C1 C2 z,
      W.capTubeHasNeckChart ε := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

/-- （`_P6JG3H`）时间导数 `stageMetric m` → incoming（`m = j.castSucc`）。 -/
theorem deriv_of_stage_P6JG3H (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ) {C : ℝ}
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) x) (Iic v) v| ≤
      C * metricScalarAt (K.toHistory.stageMetric m v) x ^ 2) :
    |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s z) (Iic v) v| ≤
      C * (K.toHistory.event j).incoming.flow.scalar v z ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hx
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **同 slab 时间导数 ⇐ selection + `hdistW`（`_P6JG3`，PROVED，阈值 `Cg·R`，无 J10）**：
`hgrad_of_selection_sameSlab_Cg_P6CD` 的副本，取 hgood `HasSpatialCanonicalTimeControl` 的**时间分量**
（`time (activeStage v) < v < horizon` 时 `|∂_t R| ≤ Ctime′ R²`）代替梯度分量；结论 = SLT 窗口 `hder` 槽
（`q := Cg·R`、`G := event incoming`、`Ctime := Ctime′`）。证明其余逐字。 -/
theorem hderSel_of_selection_sameSlab_Cg_P6JG3 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      |derivWithin (fun w => ((K n).toHistory.event (j n)).incoming.flow.scalar w x) (Iic v) v| ≤
        (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x ^ 2 := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistW (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon :=
    (hv.2.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) v' hv.1.le (hv.2.trans (htj n))
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6JG3H (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6JG3H (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_of_incoming_P6JG3H (j n) hvact.symm v x _ hptx
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) tr) (by rw [hsc']; exact hq.le)
  have hvh : v < (K n).toHistory.horizon :=
    (hv.2.trans (htj n)).trans_le ((K n).toHistory.time_le_horizon_at (j n).succ)
  have htv : (K n).toHistory.time ((K n).toHistory.activeStage v') < (v' : ℝ) := by
    rw [hvact]
    exact hv.1
  exact (K n).deriv_of_stage_P6JG3H (j n) hvact.symm v x _ hptx (hgoodv.2 htv hvh)

end ObservedHistory

/-- **anchor 无 J10 孪生（`_P6JG3`，PROVISIONAL[`hslabsSel`]）**：`hanchor0_lateW_P6LT`
（`P6TracedDepthHIP6LT.lean:76`）删 `qcan` / `hqcan` / `hslab` / `hderG` / `hqR` / `hq2`；SLT 阈值 = `q`
（q_sel，实例 `Cg·R`），`hR` / `hRpos` 升 binder；SLT 的两个导数槽改由 q 阈值 binder 直接给：
同 slab `hderSel`（**无 J10**，由 `hderSel_of_selection_sameSlab_Cg_P6JG3` ⇐ hgood 时间分量 + `hdistW` 付）与
前 slab `hslabsSel`。**`hslabsSel` = J10 残余：slab 导数阈值 `Q ≤ Cg·R` 的换皮，不算去 J10**——first-exit
producer（`hderivL_of_hgood_firstExit_P6JW` ⇐ hstopE ⇐ CXJD 端点球控制）以 anchor 球界为输入，对 anchor
循环；诚实修复 = SLT 核坏点尺度局部化孪生（研究级，见 state-O-CH11-J10GEN3 REPAIR TARGET）。结论逐字。 -/
theorem RetainedCoreHistory.hanchor0_lateW_noJ10_P6JG3
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap s t ρ T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ j : Fin (H n).eventCount, Perelman.PhiAlmostNonnegative
        ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (T₀ n)) phi)
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / ((G n).flow.scalar (t n) (y n)))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    (hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop)
    (hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n))
    {Cq : ℝ} (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
    (hslabsSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hderSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n))
        (y n) (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        Ctime * (G n).flow.scalar v x ^ 2)
    (hW : ∀ Rad : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))), q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hgrad : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
        (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ v ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (t n),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < (G n).flow.scalar v x → ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          Cgrad * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w))
    (hnc : ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : (H n).time (Fin.last (H n).eventCount) < T) (hTs : T < s n), T ≤ t n →
        t n - B / ((G n).flow.scalar (t n) (y n)) ≤ T →
        let Bh := (H n).extendHorizon T (hend n ▸ hT.le) ((G n).closedPrefix T hT hTs) (hGi n)
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, (H n).horizon_nonneg.trans (hend n ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b))
    (hρ : Tendsto (fun n => ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n))) atTop atTop) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * ((G n).flow.scalar (t n) (y n)) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop :=
    tendsto_atTop_mono (fun n => (hpar n).2.1.trans (hpar n).2.2.1) hnat
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := le_trans (by omega) (hpar n).2.2.2.1
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M
    (Ctime := Ctime) (Cq := Cq) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi t
    hat hts y q ρ hq hqC hR hRt T₀ hT₀
    records hcan hradius hord hacc hW hslabsSel hderSel hgrad
    (fun B => (hT₀ B).mono fun n hn j v hv w => (hpinch n).1 j v ⟨hv.1, hn.trans hv.2⟩ w)
    (fun B => (hT₀ B).mono fun n hn v hv w => (hpinch n).2 v ⟨hv.1, hn.trans hv.2⟩ w) hnc hρ D θcap
    hDt hθ
    hnot A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact (hRpos n).le


/-- **全局 q 阈值 slab 导数 ⇒ `hslabsSel` 槽（`_P6JG3`，PROVED 接线）**：ANCHOR5 口径的
`EventSlabsDerivative Ctime (q n)`（全 prefix）蕴含本文件 anchor 的窗口 / 半径索引槽。**J10 残余**。 -/
theorem hslabsSel_of_global_P6JG3 {Ctime : ℝ≥0} {s t q : ℕ → ℝ} {H : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hslabSel : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount)) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (y n))),
      ∀ Btr : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ v ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      t n - B / ((G n).flow.scalar (t n) (y n)) ≤ v →
      q n < ((H n).toHistory.event j).incoming.flow.scalar v
        (Btr.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((H n).toHistory.event j).incoming.flow.scalar w
        (Btr.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
  fun _ _ => Eventually.of_forall fun n j _ _ _ _ _ v hv _ hRv =>
    hslabSel n j (Fin.castSucc_lt_last j) _ v hv hRv

namespace ObservedHistory

/-- **consumer：kernel 帧 anchor 无 J10（`_P6JG3`，PROVISIONAL[`hslabsSel`]）**：closed-kappa kernel
（`P6ClosedHICondKappaP6CK:349–355`）的 anchor 调用去 J10——`H := prefixAt`、`G := event incoming`、
`q := Cg·R`、`Cq := Cg`；hW ⇐ `hW_of_selection_Cg_P6M3`、hgrad ⇐ `hgrad_of_selection_sameSlab_Cg_P6CD`、
同 slab hder ⇐ `hderSel_of_selection_sameSlab_Cg_P6JG3`、κ 侧 ⇐ `hvolK`，`R → ∞` ⇐ `hRlt`（kernel 自带，
非 J10）。前提里没有 `Q` / `qcan` / `hslab` / `hderG`；唯一非 kernel 前提 = `hslabsSel`（**J10 残余**）。
结论 = kernel 内 `hanchor0` 逐字形（喂 `exists_hctrl_lateHI_P6LT` / `exists_hctrl_lateHI_noJ10_P6JA`）。 -/
theorem hanchor0_eventSlab_noJ10_P6JG3
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hslabsSel : ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hk := exists_tracedKappa_of_kseq_P6D2 hvolK
  obtain ⟨ρnc, hradii, hkappa⟩ := hk
  subst hKh
  have hnc := hnc_window_of_tracedKappa_P6M hjt htj σ hσ y yG hyG R hRpos hRn hκd ρnc hkappa
  have hρ : Tendsto (fun n => ρnc n *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop :=
    hradii.congr fun n => by rw [hRn n]
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_sameSlab_Cg_P6CD hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hder := hderSel_of_selection_sameSlab_Cg_P6JG3 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hRlim : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop :=
    tendsto_atTop_mono (fun n => (hRlt n).le.trans_eq (hRn n)) hnat
  have hR0 : ∀ n, 0 < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_noJ10_P6JG3
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := ρnc) hεcone hκd hphi
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    hθcap hpinch hjt htj hnot hT₀ hRt hRlim hR0 (Cq := Cg) (fun n => Cg * R n) hCg0 hqC hslabsSel
    hder hW hgrad hnc hρ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
