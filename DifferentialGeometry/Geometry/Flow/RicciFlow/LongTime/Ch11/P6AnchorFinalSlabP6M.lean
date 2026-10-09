import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorSelectionP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# SLT 的 `hnc` / `hW` / `hgrad`（final-slab 情形）⇐ `Pre841` κ / selection（O-CH11-P6ANCH G3g，`_P6M`）

event 版 `P6AnchorKappaP6M`（`hnc_window_of_tracedKappa_P6M`）与 `P6AnchorSelectionP6M`
（`hW_of_selection_P6M`、`hgrad_of_selection_P6M`）的 final-slab 对应。坏点 `σ n = t n` 落在 final slab
（`time (Fin.last _) < t n`），SLT adapter-q `hanchor0_of_closure_data_window_q_P6M` 的数据取
`H n := (K n).prefixAt (Fin.last _)`、`G n := ((K n).finalSlab _).restrictIncoming le_rfl _ le_rfl`、
`s n := (K n).horizon`。与 event 版的差别只在 last stage 的识别：
* `activeStage τ = Fin.last _`（`time (Fin.last _) ≤ τ`，`stageDomain` 的 last 分支 `Icc`）；
* `stageMetric (Fin.last _) v = (K.finalSlab hfin).flow.base.metric v`（`stageMetric_last_of_lt`），
  与 `restrictIncoming` 的度量定义等；
* `hnc` 经 final 版桥 `tested_noncollapse_final_P6M`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-- 首末 stage 指标相等时的单点 trace（trace 点 `HEq` 端点）。 -/
private theorem exists_trace_of_stage_eq_fs_P6M (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- final slab 内（`time (Fin.last _) ≤ τ`）时刻的 `activeStage` 是 last stage。 -/
private theorem activeStage_eq_last_fs_P6M (K : RetainedCoreHistory.{u})
    (τ : Icc (0 : ℝ) K.toHistory.horizon) (h1 : K.time (Fin.last K.eventCount) ≤ τ) :
    K.toHistory.activeStage τ = Fin.last K.eventCount :=
  (K.toHistory.mem_stageDomain_iff τ (Fin.last _)).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_last] using
      (show (τ : ℝ) ∈ Icc (K.time (Fin.last K.eventCount)) K.horizon from ⟨h1, τ.2.2⟩))

/-- 球成员：final slab incoming 度量 → `stageMetric m`（`m = Fin.last _`，`HEq` 搬运）。 -/
private theorem mem_ball_final_fs_P6M (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v r : ℝ)
    (z yG : (K.stage (Fin.last K.eventCount)).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG) (h : z ∈ riemannianBallOf (G.flow.base.metric v) yG r) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)]
  exact h

/-- 标量 `stageMetric m` ↔ final slab incoming（`m = Fin.last _`）。 -/
private theorem scalar_final_fs_P6M (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v : ℝ)
    (z : (K.stage (Fin.last K.eventCount)).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x = G.flow.scalar v z := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)]
  rfl

/-- witness `stageMetric m` → final slab incoming（`m = Fin.last _`）。 -/
private theorem witness_final_fs_P6M (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v : ℝ) {ε C1 C2 : ℝ}
    (z : (K.stage (Fin.last K.eventCount)).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric v) ε C1 C2 z, W.capTubeHasNeckChart ε := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)] at h
  exact h

/-- **`_P6M`（单 history，final slab）**：K 层 trace-local κ（基点 `(σ, y)`、半径 `Rad`、深度 `θ`、
`r'' ≤ ρ`）⇒ final 版桥 `tested_noncollapse_final_P6M` 所需的 K 层窗口 tested κ
（`U = B_G(t)(yG, Rad)`、`a = t − θ`）。 -/
theorem tested_kappa_window_final_P6M (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {t : ℝ}
    (htl : K.time (Fin.last K.eventCount) < t)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hσ : (σ : ℝ) = t)
    (y : (K.toHistory.stageAt σ).Carrier) (yG : (K.stage (Fin.last K.eventCount)).Carrier)
    (hyG : HEq y yG) {κ ρ Rad θ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ σ), (σ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρ →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) r'') :
    ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), t - θ ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
      K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) yG Rad,
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b) := by
  intro τ haτ hτt hjτ _ z hz zz hzz b hb hbρ hball
  have hσact : K.toHistory.activeStage σ = Fin.last K.eventCount :=
    K.activeStage_eq_last_fs_P6M σ (by rw [hσ]; exact htl.le)
  have hτact : K.toHistory.activeStage τ = Fin.last K.eventCount :=
    K.activeStage_eq_last_fs_P6M τ hjτ.le
  have hvt : τ ≤ σ := show (τ : ℝ) ≤ σ by rw [hσ]; exact hτt
  let x : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hσact.symm) z
  have hxz : HEq x z := cast_heq _ _
  have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y Rad :=
    mem_ball_final_fs_P6M K hfin G hG hσact.symm σ Rad z yG x y hxz hyG (by rw [hσ]; exact hz)
  obtain ⟨tr, htr⟩ := exists_trace_of_stage_eq_fs_P6M K.toHistory (hτact.trans hσact.symm)
    (K.toHistory.activeStage_mono hvt) x
  have hθ' : (σ : ℝ) - θ ≤ τ := by rw [hσ]; exact haτ
  have hpt : tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt) = zz :=
    eq_of_heq (htr.trans (hxz.trans hzz.symm))
  have hball' : K.toHistory.isParabolicallyRmControlledBall τ
      (tr.point (K.toHistory.activeStage τ) le_rfl (K.toHistory.activeStage_mono hvt)) b := by
    rw [hpt]
    exact hball
  have h := hK x hx τ hvt hθ' tr b hb hbρ hball'
  rw [hpt, ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **`_P6M`（序列 `hnc`，窗口形，final slab）**：K 层 trace-local κ（`hkappa`，`ρnc`）⇒ adapter-q
`hanchor0_of_closure_data_window_q_P6M` 的窗口 `hnc`（`H n := (K n).prefixAt (Fin.last _)`、
`G n := ((K n).finalSlab _).restrictIncoming le_rfl _ le_rfl`、`s n := (K n).horizon`、`ρ := ρnc`）。 -/
theorem hnc_window_final_P6M
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
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
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (Fin.last (K n).eventCount)).time
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) < T)
      (hTs : T < (K n).horizon), T ≤ t n →
        t n - B / (G n).flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (Fin.last (K n).eventCount)).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          ((G n).closedPrefix T hT hTs) (by rw [hG n]; exact (K n).final_initial (hfin n))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (Fin.last (K n).eventCount)).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
            (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρnc n →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  intro Rad B
  filter_upwards [hkappa (max Rad 1) (max B 1) (by positivity) (by positivity)] with n hn
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hsingle := (K n).tested_kappa_window_final_P6M (hfin n) (G n) (hG n) (htl n) (σ n) (hσ n)
    (y n) (yG n) (hyG n) (Rad := max Rad 1 / Real.sqrt (R n)) (θ := max B 1 / R n) hκ.le hn
  have hU : ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n) (max Rad 1 / Real.sqrt (R n)) := by
    intro z hz
    rw [← hRn n] at hz
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hz
  have hbridge := (K n).tested_noncollapse_final_P6M (hfin n) (a := t n - max B 1 / R n)
    (t := t n) (ρ := ρnc n)
    (riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
      (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))))
    (fun τ haτ hτt hjτ hτj z hz zz hzz b hb hbρ hball =>
      hsingle τ haτ hτt hjτ hτj z (hU z hz) zz hzz b hb hbρ hball) ((K n).prefixAt_time_last _)
  obtain rfl : G = fun n => ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl :=
    funext hG
  intro T hT hTs hTt hBT
  refine hbridge T hT hTs hTt ?_
  rw [← hRn n] at hBT
  have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
  linarith

/-- **`_P6M`（selection ⇒ SLT 终端 `hW`，final slab，阈值 `4R`）**：L11 + last stage 识别 ⇒
adapter-q 的 `hW`（final slab incoming 形，witness 常数 = selection 的 `C1' C2'`）。 -/
theorem hW_final_P6M {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
        4 * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      4 * R n < (G n).flow.scalar (t n) x →
        ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) eps C1' C2' x,
          W.capTubeHasNeckChart eps := by
  intro Rad
  filter_upwards [hL.eventually_ge_atTop (max Rad 1)] with n hLn
  intro x hx hq
  have hσact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).activeStage_eq_last_fs_P6M (σ n) (by rw [hσ n]; exact (htl n).le)
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_final_fs_P6M (hfin n) (G n) (hG n) hσact.symm (σ n) _ x (yG n) x'
      (y n) hxx (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  have hL11 := (K n).toHistory.hasSpatialCanonicalTimeControl_at_terminal_of_selection_P6N
    (haT n) (hsT n) (has n) (seedTrace n) (y n) (hR n) (hgood n) hLn
  have hsc := (K n).scalar_final_fs_P6M (hfin n) (G n) (hG n) hσact.symm (σ n) x x' hxx
  have hgoodx := hL11 x' hx' (by rw [hsc, hσ n]; exact hq.le)
  have hw := (K n).witness_final_fs_P6M (hfin n) (G n) (hG n) hσact.symm (σ n) x x' hxx hgoodx.1
  rw [hσ n] at hw
  exact hw

/-- **`_P6M`（selection ⇒ SLT 窗口 `hgrad`，final slab，阈值 `4R`）**：L9（窗口时刻与基点同在 final
slab ⇒ 单点 trace）+ witness `gradient` 字段 ⇒ adapter-q 的 `hgrad`（`Cgrad = C2'.toNNReal`）。 -/
theorem hgrad_final_P6M {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2 : 0 ≤ C2')
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
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
        4 * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
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
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
      t n - B / (G n).flow.scalar (t n) (yG n) ≤ v →
      4 * R n < (G n).flow.scalar v x →
      ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          (C2'.toNNReal : ℝ) * (G n).flow.scalar v x * Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt (((G n).flow.base.metric v).inner x w w) := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdist (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq w
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).activeStage_eq_last_fs_P6M (σ n) (by rw [hσ n]; exact (htl n).le)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon := hv.2.le.trans (by rw [← hσ n]; exact (σ n).2.2)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = Fin.last (K n).eventCount :=
    (K n).activeStage_eq_last_fs_P6M v' hv.1.le
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_final_fs_P6M (hfin n) (G n) (hG n) hσact.symm (σ n) _ x (yG n) x'
      (y n) hxx (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_fs_P6M (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hL9 := (K n).toHistory.hasSpatialCanonicalTimeControl_on_window_traces_P6N (haT n)
    (hsT n) (has n) (seedTrace n) (y n) (hR n) (hgood n) hsc.1 hw hd
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_final_fs_P6M (hfin n) (G n) (hG n) hvact.symm v x _ hptx
  have hgoodv := hL9 x' hx' v' hvt hBv' tr (by rw [hsc']; exact hq.le)
  have hW := (K n).witness_final_fs_P6M (hfin n) (G n) (hG n) hvact.symm v x _ hptx hgoodv.1
  obtain ⟨W, -⟩ := hW
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient w

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
