import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureAnchorP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionGoodP6M

/-!
# SLT 的 U 侧也由 selection 给出：`hW` / `hgrad` ⇐ Good 区（O-CH11-P6ANCH G1y，后缀 `_P6M`）

G1x 的收口 `false_of_selection_eventSlab_anchor_P6M` 还留 SLT U 侧 `hWA`（终端 witness）/ `hgradA`
（窗口梯度界），阈值 `2·qcan`。selection 的 Good 区阈值是 `4R`（`R` = 坏点标量），故先把 G1w adapter
推广到一般阈值 `q n`（`2·qcan ≤ q ≤ Cq·R`，`hanchor0_of_closure_data_window_q_P6M`），取 `q = 4R`、
`Cq = 4`：
* `hW_of_selection_P6M`：L11（`Rad ≤ L n` eventually）+ 指标 / 度量识别（`stageMetric_castSucc_apply`）；
* `hgrad_of_selection_P6M`：L9（窗口时刻与基点同 slab ⇒ 单点 trace；`hwin` / `hdist` / `L n → ∞`）+
  witness 的 `gradient` 字段（`scalarDifferential` 与 `mfderiv metricScalarAt` 定义等），`Cgrad = C2'`；
* **`false_of_selection_eventSlab_final_P6M`**：P6 收口，SLT 的 U 侧前提全部消去（多一个小性条件
  `ε ≤ coneAccuracy`，SLT 的 witness 精度）。
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

/-- **`_q` 版（一般阈值 `q n`，`2·qcan ≤ q ≤ Cq·R`）**：G1w
`hanchor0_of_closure_data_window_P6M` 的推广；数据前提（全 family、全局 `hslab` /
`hderG` / pinching、`hnot`、`hRt`）+ 半径索引 `hW` / `hgrad`（阈值 `2·qcan`）+ 窗口 `hnc` + `hρ` ⇒
`hanchor0` 逐字形（`∃ Q ≥ 2`）。late 阈值取 `T₀ = 0`（`hRt` ⇒ eventually `0 ≤ t − B/R`）。 -/
theorem RetainedCoreHistory.hanchor0_of_closure_data_window_q_P6M
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t ρ : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
    (hRt : Tendsto (fun n => ((G n).flow.scalar (t n) (y n)) * t n) atTop atTop)
    {Cq : ℝ} (q : ℕ → ℝ) (hq2 : ∀ n, 2 * qcan n ≤ q n)
    (hqC : ∀ n, q n ≤ Cq * ((G n).flow.scalar (t n) (y n)))
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
  have hq0 (n : ℕ) : 0 < qcan n := by
    have := hqcan n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n => ((G n).flow.scalar (t n) (y n))) atTop atTop :=
    tendsto_atTop_mono (fun n => (hqcan n).trans (hqR n).le) hnat
  have hradius : Tendsto (fun n => (p n).modelRadius) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hnat
    rw [(hrec n).2.1]
    exact (hpar n).2.1.trans (hpar n).2.2.1
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun n => (hpar n).2.1) hnat
  have hacc : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζ := by
    intro ζ hζ
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hζ)] with n hn
    rw [(hrec n).2.2.2.1]
    exact (hpar n).1.trans hn
  have hθ (n : ℕ) : (1 : ℝ) / 2 ≤ θcap n := by
    refine le_trans ?_ (hθcap n)
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hord (n : ℕ) : 2 ≤ (p n).modelOrder := by
    rw [(hrec n).2.2.1]
    exact le_trans (by omega) (hpar n).2.2.2.1
  have hctime : ((2 * Ctime : ℝ≥0) : ℝ) = 2 * (Ctime : ℝ) := by push_cast; ring
  have hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, (0 : ℝ) ≤ t n - B / ((G n).flow.scalar (t n) (y n)) := by
    intro B
    filter_upwards [hRt.eventually_ge_atTop B] with n hn
    have hRn : 0 < ((G n).flow.scalar (t n) (y n)) := (hq0 n).trans (hqR n)
    rw [sub_nonneg, div_le_iff₀ hRn]
    linarith [mul_comm ((G n).flow.scalar (t n) (y n)) (t n)]
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := RetainedCoreHistory.eventually_scalar_bound_at_distance_window_P6M
    (Ctime := 2 * Ctime) (Cq := Cq) hεle hκ hphi (by norm_num : (0 : ℝ) < 1 / 2) H hend s G hGi t
    hat hts y q ρ (fun n => by have := hq0 n; have := hq2 n; linarith) hqC hR hRt (fun _ => 0) hT₀
    (fun n i _ => records n i)
    (fun n i _ b => (hrec n).2.2.2.2.2.1 i b) hradius hord hacc hW
    (fun Rad B => Eventually.of_forall fun n j first hf z _ Btr v hv _ hRv => by
      have hlt : qcan n < ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) := by
        have := hq0 n
        have := hq2 n
        linarith
      have h := hslab n j (Fin.castSucc_lt_last j) _ v hv hlt
      rw [hctime]
      have h0 : 0 ≤ (Ctime : ℝ) * ((H n).toHistory.event j).incoming.flow.scalar v
          (Btr.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
        mul_nonneg Ctime.coe_nonneg (sq_nonneg _)
      linarith)
    (fun Rad B => Eventually.of_forall fun n x _ v hv _ hRv =>
      hderG n x v hv (lt_of_le_of_lt (hq2 n) hRv)) hgrad
    (fun B => Eventually.of_forall fun n j v hv w => (hpinch n).1 j v hv.1 w)
    (fun B => Eventually.of_forall fun n v hv w => (hpinch n).2 v hv.1 w) hnc hρ D θcap hDt hθ
    (fun n => by
      rintro ⟨j, _, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot n ⟨j, hl, Btr, b, x, h1, h2, h3⟩) A hA
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  filter_upwards [hev] with n hn z hz
  refine (hn z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact ((hq0 n).trans (hqR n)).le


namespace RetainedCoreHistory

/-- 首末 stage 指标相等时的单点 trace。 -/
private theorem exists_trace_of_stage_eq_P6M' (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- slab 内部时刻的 `activeStage`。 -/
private theorem activeStage_eq_of_mem_slab_P6M' (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- 球成员 incoming → `stageMetric m`（`m = j.castSucc`）。 -/
private theorem mem_ball_of_incoming_P6M (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
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
private theorem scalar_of_incoming_P6M (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x =
      (K.toHistory.event j).incoming.flow.scalar v z := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- witness `stageMetric m` → incoming（`m = j.castSucc`）。 -/
private theorem witness_of_stage_P6M (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
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

end RetainedCoreHistory

namespace ObservedHistory

/-- **`_P6M`（selection ⇒ SLT 终端 `hW`，半径索引，阈值 `4R`）**：L11（`Rad ≤ L n` eventually）+ 指标 /
度量识别 ⇒ G1y adapter 的 `hW`（incoming slab 形，witness 常数 = selection 的 `C1' C2'`）。 -/
theorem hW_of_selection_P6M {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {K : ℕ → RetainedCoreHistory.{u}}
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
        4 * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      4 * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) x →
        ∃ W : SpatialCanonicalWitness
            (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) eps C1' C2' x,
          W.capTubeHasNeckChart eps := by
  intro Rad
  filter_upwards [hL.eventually_ge_atTop (max Rad 1)] with n hLn
  intro x hx hq
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6M' (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6M (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  have hL11 := (K n).toHistory.hasSpatialCanonicalTimeControl_at_terminal_of_selection_P6N
    (haT n) (hsT n) (has n) (seedTrace n) (y n) (hR n) (hgood n) hLn
  have hsc := (K n).scalar_of_incoming_P6M (j n) hσact.symm (σ n) x x' hxx
  have hgoodx := hL11 x' hx' (by rw [hsc, hσ n]; exact hq.le)
  have hw := (K n).witness_of_stage_P6M (j n) hσact.symm (σ n) x x' hxx hgoodx.1
  rw [hσ n] at hw
  exact hw

/-- **`_P6M`（selection ⇒ SLT 窗口 `hgrad`，阈值 `4R`）**：L9（窗口内 trace 点 Good；窗口时刻与基点同
slab ⇒ 单点 trace）+ witness `gradient` 字段 ⇒ G1y adapter 的 `hgrad`（`Cgrad = C2'.toNNReal`）。 -/
theorem hgrad_of_selection_P6M {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (hC2 : 0 ≤ C2')
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
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      4 * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential ((K n).toHistory.event (j n)).incoming.flow v x w| ≤
          (C2'.toNNReal : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x *
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar v x) *
            Real.sqrt
              ((((K n).toHistory.event (j n)).incoming.flow.base.metric v).inner x w w) := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdist (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq w
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6M' (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon :=
    (hv.2.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6M' (j n) v' hv.1.le (hv.2.trans (htj n))
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6M (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6M' (K n).toHistory
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
  have hsc' := (K n).scalar_of_incoming_P6M (j n) hvact.symm v x _ hptx
  have hgoodv := hL9 x' hx' v' hvt hBv' tr (by rw [hsc']; exact hq.le)
  have hW := (K n).witness_of_stage_P6M (j n) hvact.symm v x _ hptx hgoodv.1
  obtain ⟨W, -⟩ := hW
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient w

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
