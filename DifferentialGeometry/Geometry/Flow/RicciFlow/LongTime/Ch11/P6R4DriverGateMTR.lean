import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4DriverGateR4B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvSlotsR4J
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaR4FrameRcMTR

set_option autoImplicit false

/-!
# MTRS G1：整合 R4 driver gate 孪生——整体以 R4 中心标量 `R_c := scalar(t, y′)` 归一化（后缀 `_MTR`）

R4J10 repair target。基底 = R4BCAD G2 `hTR_of_driver_gate_R4B`（hbcadC 已内付），结论（gate 形 hTR）逐字。
改动：
(1) 删 `{Cst} {κ} 0 < κ` 与 hsurvive / hextend / hkappaC 三前提；hsurvive / hextend 换为一个 J10 槽：
    回调环境 → `J10Blk_JT K t y′ R_c`（= R4J10 `drvSlots_Rc_of_J10_R4J` 结论逐字；Cst 由 ∃ 给出）。
(2) hkappaC ⇐ R4KAP `hkappaC_R4frame_Rc_of_fresh_MTR`（Rc := R_c；κ := FRESH `hsupA Aseed hA` 的 κA）。
(3) driver 内全部以 `R_c` 跑 P6KA：hanchor0（comparable 常数 C := 1，hle 取等号）、hwin′(R_c)、hseed、hpinch、
    hbcadC ⇐ `hbcadC_R4center_Rc_R4B`（Rc := R_c，Cc := 1，B := 1）；hwitC / hderivC 在 `X := 2R_c`
    上调用 `hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2`（其阈值 4X > 4R，hgood′ 直接可用），再经精确常数重标
    `hwitC_half_MTR` / `hderivC_half_MTR` 转到 `R_c`（阈值 8R_c，P6KA 取 Cs = Cq := 8）。
(4) 末端 `∀ T` DepthExtendable(R_c) 取 `2T`，`false_of_depthExtendable_Rc_MTR`（A := 2r）对 R 形坏性收尾。
F-24-8：同一元组 `(ind, c, Tn, aSeed, seedTrace, σ, y, R, L, t, y′)`；同一 recQ / hfine / hsupA / phi；
R53：传引擎实际元组。无新顶层 binder。草稿源 `P6R4DriverGateR4N.lean`（R4NORM g1.py 生成）。
-/

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-- **常数重标（`_MTR`，PROVED）**：`X := 2·R_c` 归一化的 hwitC（阈值 `4X`）⇒ `R_c` 归一化的 hwitC
（阈值 `8R_c`）。`D ↦ √2·D`、`T ↦ 2T`、`K ↦ K/2`；n 无关常数因子，逐字精确。 -/
theorem hwitC_half_MTR {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
    {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {Rc : ℕ → ℝ}
    {eps C1' C2' : ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n)
          (2 * D / Real.sqrt (2 * Rc n)) (T / (2 * Rc n)) (K * (2 * Rc n))) →
        ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (2 * Rc n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / (2 * Rc n) ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          4 * (2 * Rc n) < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1' C2'
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (Rc n))
          (T / Rc n) (K * Rc n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (Rc n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / Rc n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          8 * Rc n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1' C2'
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps := by
  intro φ hφ D T K hD hT hK htr
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have e1 : ∀ n a, Real.sqrt 2 * a / Real.sqrt (2 * Rc n) = a / Real.sqrt (Rc n) := fun n a => by
    rw [Real.sqrt_mul zero_le_two, mul_div_mul_left _ _ hs2.ne']
  have e2 : ∀ n, 2 * T / (2 * Rc n) = T / Rc n := fun n => mul_div_mul_left _ _ two_ne_zero
  have e3 : ∀ n, K / 2 * (2 * Rc n) = K * Rc n := fun n => by ring
  have htr' : ∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n)
      (2 * (Real.sqrt 2 * D) / Real.sqrt (2 * Rc n)) (2 * T / (2 * Rc n))
      (K / 2 * (2 * Rc n)) :=
    htr.mono fun n hn => by
      rw [show 2 * (Real.sqrt 2 * D) = Real.sqrt 2 * (2 * D) by ring, e1, e2, e3]
      exact hn
  refine (h φ hφ (Real.sqrt 2 * D) (2 * T) (K / 2) (by positivity) (by positivity)
    (by positivity) htr').mono ?_
  intro n hn x hx v hvt hv hlt hact tr hsc
  exact hn x (by rwa [e1]) v hvt (by rwa [e2]) hlt hact tr (by linarith)

/-- **常数重标（`_MTR`，PROVED）**：hderivC 同 `hwitC_half_MTR`。 -/
theorem hderivC_half_MTR {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
    {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {Rc : ℕ → ℝ}
    {Ctime' : ℝ≥0}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n)
          (2 * D / Real.sqrt (2 * Rc n)) (T / (2 * Rc n)) (K * (2 * Rc n))) →
        ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (2 * Rc n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / (2 * Rc n) ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          4 * (2 * Rc n) < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime' * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (Rc n))
          (T / Rc n) (K * Rc n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (Rc n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / Rc n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          8 * Rc n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime' * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2 := by
  intro φ hφ D T K hD hT hK htr
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have e1 : ∀ n a, Real.sqrt 2 * a / Real.sqrt (2 * Rc n) = a / Real.sqrt (Rc n) := fun n a => by
    rw [Real.sqrt_mul zero_le_two, mul_div_mul_left _ _ hs2.ne']
  have e2 : ∀ n, 2 * T / (2 * Rc n) = T / Rc n := fun n => mul_div_mul_left _ _ two_ne_zero
  have e3 : ∀ n, K / 2 * (2 * Rc n) = K * Rc n := fun n => by ring
  have htr' : ∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n)
      (2 * (Real.sqrt 2 * D) / Real.sqrt (2 * Rc n)) (2 * T / (2 * Rc n))
      (K / 2 * (2 * Rc n)) :=
    htr.mono fun n hn => by
      rw [show 2 * (Real.sqrt 2 * D) = Real.sqrt 2 * (2 * D) by ring, e1, e2, e3]
      exact hn
  refine (h φ hφ (Real.sqrt 2 * D) (2 * T) (K / 2) (by positivity) (by positivity)
    (by positivity) htr').mono ?_
  intro n hn x hx v hvt hv hlt hact tr hsc
  exact hn x (by rwa [e1]) v hvt (by rwa [e2]) hlt hact tr (by linarith)

/-- **比值收尾（`_MTR`，PROVED）**：`R_c` 归一化的 `DepthExtendable … (2T)` 与 `R` 归一化坏性
`¬ TR(r/√R, T/R, n·R)` 矛盾（`R_c < 2R`；`A := 2r`、`n ≥ 2K₀`）。∀T 吸收窗比 `T ↦ 2T`。 -/
theorem false_of_depthExtendable_Rc_MTR {Hs : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier}
    {R Rc : ℕ → ℝ} {σ : ℕ → ℕ} {T r : ℝ} (hσ : StrictMono σ) (hr : 0 < r) (hT : 0 < T)
    (hR : ∀ n, 0 < R n) (hRc : ∀ n, 0 < Rc n) (hRc2 : ∀ n, Rc n < 2 * R n)
    (hDE : ObservedHistory.DepthExtendable Hs ts ys Rc σ (2 * T))
    (hbad : ∀ n, ¬ (Hs n).isTracedRegion (ts n) (ys n) (r / Real.sqrt (R n)) (T / R n)
      ((n : ℝ) * R n)) : False := by
  obtain ⟨K₀, hK₀, hev⟩ := hDE (2 * r) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * K₀)
  obtain ⟨i, hTR, hi⟩ := (hev.and (eventually_ge_atTop N)).exists
  have hσi : (N : ℝ) ≤ (σ i : ℝ) := by exact_mod_cast hi.trans (hσ.id_le i)
  set m := σ i
  have hRm := hR m
  have hRcm := hRc m
  have hsq : Real.sqrt (Rc m) ≤ 2 * Real.sqrt (R m) := by
    have h4 : Real.sqrt (4 * R m) = 2 * Real.sqrt (R m) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by linarith [hRc2 m])
  have hsR := Real.sqrt_pos.2 hRm
  have hsRc := Real.sqrt_pos.2 hRcm
  refine hbad m (hTR.mono (div_pos hr hsR) ?_ (div_pos hT hRm) ?_ (mul_nonneg hK₀ hRcm.le) ?_)
  · rw [div_le_div_iff₀ hsR hsRc]
    nlinarith
  · rw [div_le_div_iff₀ hRm hRcm]
    nlinarith [hRc2 m]
  · calc K₀ * Rc m ≤ K₀ * (2 * R m) := mul_le_mul_of_nonneg_left (hRc2 m).le hK₀
      _ = 2 * K₀ * R m := by ring
      _ ≤ (m : ℝ) * R m := mul_le_mul_of_nonneg_right (hN.trans hσi) hRm.le

/-- **整合 R4 driver gate，R_c 归一化孪生（`_MTR`，PROVISIONAL[hsepWK（带 hceil）, J10 槽（R_c）]；
hK / hpinch / hseed / hbcadC / hkappaC 在内付）**：见模块文档。 -/
theorem hTR_of_driver_gate_MTR :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius →
      0 < ε → ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} →
      -- HCEILT 环境（R4 中心 kernel 内付 hK）：SCRS⁺ 投影 / FRESH / 数值
      ε ≤ coneAccuracy → 0 ≤ C2 →
      ∀ (q : CutoffParameters), AntitoneOn q.neckRadius (Ici 0) → Tendsto q.delta atTop (𝓝 0) →
      ∀ (recQ : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e q),
      (∀ ε' : ℝ, 0 < ε' → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
        ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (recQ n i).nominalRadius h ≤ ε' * q.neckRadius t) →
      (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((recQ n i).static b).neck.scale) →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      (∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
        ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
          KappaSeedWindowFwd_C11PK
            (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
            (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory) →
      -- hsepWK（塔帧 (SEP-ρ)，owner HNOT-LOCALDT）
      (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
      -- J10 槽（R_c := scalar(t, y′) 归一化；= `drvSlots_Rc_of_J10_R4J` 结论；Cst 在 ∃ 内）
      (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
      J10Blk_JT (fun k => (F.tower.history (ind k)).rescale_P6N (c k) (hc k)) t y'
        (centerScalar_R4J (fun k => (F.tower.history (ind k)).rescale_P6N (c k) (hc k)) t y')) →
      ∀ Aseed : ℝ, 1 < Aseed →
      ∀ (T r : ℝ), 0 < T → 0 < r → ∃ Kt : ℝ, 0 ≤ Kt ∧
        ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
          let Kh : ℕ → ObservedHistory.{u} := fun k =>
            ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
          ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
            (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
          ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
            (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
            (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
            (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
              riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
                ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                  (pT k) 1)) →
            (∀ k, 2 < (Tn k : ℝ)) →
            (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
              q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
          ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
              ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
            (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
            (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
            (∀ k, R k =
              metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
            (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
            Tendsto L atTop atTop →
            (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
            (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
              ∀ z : ((Kh k).stageAt v).Carrier,
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                    ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                      ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                  riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                      ((seedTrace k).point ((Kh k).activeStage (σ k))
                        ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                    ENNReal.ofReal (L k / Real.sqrt (R k)) →
                4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
                (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
            (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
            (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
            Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
            Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
            (∀ᶠ k in atTop,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                    ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
            (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
              ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
              ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Kt * R k) := by
  obtain ⟨ε₁, hε₁, hG1⟩ := exists_R4_center_family_of_notTR_gate_HTP.{u}
  obtain ⟨ε₂, hε₂, hW⟩ := hwitC_hderivC_of_hPN_anyPos_le_P6DP4E2.{u}
  obtain ⟨ε₃, hε₃, hKap⟩ := hkappaC_R4frame_Rc_of_fresh_MTR.{u}
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃, ?_⟩
  intro P g F ε C1 C2 Ctime pF records hcanF hacc hord hrad hε hεX hεN hεcone hC20 q hanti hδq
    recQ hrecent hfine hTD hsupA hsepWK hJ10 Aseed hA T r hT hr
  -- recent 阈值（η_k = 1/(2(k+1))）、late recenter、HI、FRESH（HTP 逐字）
  choose Trec hTrec0 hTrec using fun k : ℕ =>
    hrecent (1 / (2 * ((k : ℝ) + 1))) (by positivity)
  obtain ⟨Tδ, hTδ0, hTδ⟩ := exists_late_recenter_CXW hδq
  obtain ⟨phi, hphi, hpinK, -⟩ := hpinch_core_of_HIProp_P6HP2 F
    (fun n => by
      obtain ⟨a, ha, h⟩ := exists_initialHI_P6WR F
      exact ⟨a, ha, fun x => h n x⟩)
    (fun n => ⟨pF, ⟨records n⟩⟩)
  obtain ⟨κA, hκA, Tf, hsupK⟩ := hsupA Aseed hA
  -- hbcadC producer（R4BCAD G1，R_c 泛型版）：Θb 并入 E2a′ 阈值序列
  obtain ⟨Θb, hΘb⟩ := hbcadC_R4center_Rc_R4B F hεcone hC20 q hanti hδq recQ hrecent hfine hTD hsupA
  by_contra hcon
  refine hG1 (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) F records hcanF
    (hacc.trans ((min_le_left _ _).trans (min_le_left _ _))) hord hrad q Aseed
    (fun k => max (max (Trec k) (2 * Tδ)) (Θb k)) hsepWK T r hT hr
    (fun m hm => hcon ⟨(m : ℝ), Nat.cast_nonneg m, hm⟩) ?_
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat hts hy' hcross
    hslab hclose hcompR hcmp hcmpL hgood' hbadTR hΘ h2R
  obtain ⟨Cst, hhsurvive, hhextend⟩ := hJ10 ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace
    σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi pm t y' hat hts hy'
    hcross hslab hclose hcmp hcmpL hgood'
  have hsepWK' := hsepWK ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hceil i hi
  let K : ℕ → RetainedCoreHistory.{u} := fun n =>
    (F.tower.history (ind n)).rescale_P6N (c n) (hc n)
  -- R4 中心标量 R_c（归一化序列），R/2 < R_c < 2R
  let Rc : ℕ → ℝ := centerScalar_R4J K t y'
  have hRc2 : ∀ n, Rc n < 2 * R n := hcmp
  have hRcl : ∀ n, R n / 2 < Rc n := hcmpL
  have hRcpos : ∀ n, 0 < Rc n := fun n => by linarith [hRcl n, hRpos n]
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hRr n]) tendsto_natCast_atTop_atTop
  have hRclim : Tendsto Rc atTop atTop :=
    tendsto_atTop_mono (fun n => (hRcl n).le) (hRlim.atTop_div_const (by norm_num))
  have hdivc : ∀ n (x : ℝ), 0 ≤ x → x / Rc n ≤ 2 * x / R n := fun n x hx => by
    rw [div_le_div_iff₀ (hRcpos n) (hRpos n)]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith [hRcl n] : R n ≤ 2 * Rc n) hx]
  have hdivX : ∀ n (x : ℝ), 0 ≤ x → x / (2 * Rc n) ≤ x / R n := fun n x hx =>
    div_le_div_of_nonneg_left hx (hRpos n) (by linarith [hRcl n])
  have hradiic : Tendsto (fun n => 1 / 200 * Real.sqrt (Rc n)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hRclim).const_mul_atTop (by norm_num)
  have hRcr : ∀ n : ℕ, (n : ℝ) + 1 ≤ Rc n := fun n => by linarith [h2R n, hRcl n]
  -- hkappaC（R_c 归一化）⇐ R4KAP `hkappaC_R4frame_Rc_of_fresh_MTR`（FRESH κA，同一元组）
  have hhkappaC := hKap F records hcanF (hacc.trans (min_le_right _ _)) hord hrad hC20 q
    (by linarith) ind c hc (fun k => hsupK ind c hc k) Tn pT hTc aSeed haT hclock hone hsm hvol
    hTn2 hnrS seedTrace σ y R hsT has L hRpos hRr hL hgood haS hTnS hgateP i hi hsepWK' pm t y' hat
    hts hy' hslab hclose hcompR Rc hRcl hRc2 hRcr
  -- hbcadC（R_c 归一化）⇐ R4BCAD G1：Cc := 1（hclose σ − t ≤ 1/R），B := 1（hcompR +1/√R）
  have hhbcadC := hΘb Aseed hA ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS
    (fun k => (le_max_right _ _).trans (hΘ k)) seedTrace σ y R hsT has L hRpos hRr hL haS hroom
    hgateP hceil t y' hat hts Rc 1 1 zero_le_one zero_le_one hRcl hRc2 hRcr hradiic hclose hcompR
    hgood'
  -- hanchor0 ⇐ SLICE-BCBD2 G5（comparable 常数 C := 1，相对 R_c），kernel 帧 (K, i, t, pm)
  have hact : ∀ n, (Kh n).activeStage (t n) = (i n).castSucc := fun n =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K n) (i n) (t n) (hslab n)
  have hRcK : ∀ n, 0 < ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n) := fun n => by
    have h := (K n).scalar_of_incoming_P6X (i n) (hact n).symm (t n) (pm n) (y' n) (hy' n)
    rw [← h]
    linarith [hcmpL n, hRpos n]
  have hhK := hK_R4center_of_env_HCT F records hεcone hC20 q hanti recQ hfine hTD hTrec hTδ hpinK
    hphi hA hκA hsupK ind c hc Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii hgateP hceil i hi pm t y' hat
    hts hy' hcross hslab hclose hcompR hcmp hcmpL hgood'
    (fun k => (le_max_left _ _).trans (hΘ k)) h2R
  have hanchor0 := ObservedHistory.hanchor0_driver_of_kernel_comparable_P6SB2 Kh (K := K) rfl t y'
    (j := i) (yG := pm) (fun n => (hslab n).1) (fun n => (hslab n).2) hy'
    (fun n => ((Kh n).event (i n)).incoming.flow.scalar (t n) (pm n)) hRcK (fun _ => rfl) Rc
    hRcpos one_pos (Filter.Eventually.of_forall fun n => (one_mul (Rc n)).symm.le) hhK
  -- 窗（R 形 / R_c 形 / X := 2R_c 形）
  have hwin' : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / R n := by
    intro T' hT'
    filter_upwards [haS (T' + 1) (by linarith)] with n hn
    have h1 := hclose n
    have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
    linarith
  have hwinc : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / Rc n := by
    intro T' hT'
    filter_upwards [hwin' (2 * T') (by linarith)] with n hn
    have := hdivc n T' hT'.le
    linarith
  have hwinX : ∀ T' : ℝ, 0 < T' → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ t n - T' / (2 * Rc n) := by
    intro T' hT'
    filter_upwards [hwin' T' hT'] with n hn
    have := hdivX n T' hT'.le
    linarith
  have hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ (t n : ℝ) := by
    filter_upwards [haS 1 one_pos, hTnS 1 one_pos] with n _ hn
    linarith [hclose n]
  have htime : ∀ᶠ n in atTop, 2 * (1 : ℝ) ^ 2 ≤ (Tn n : ℝ) :=
    Filter.Eventually.of_forall fun n => by linarith [hclock n, hone n]
  have hL2 : Tendsto (fun n => L n - 2) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-2) hL).congr fun n => by ring
  have hRr1X : Tendsto (fun n => 2 * Rc n * (1 : ℝ) ^ 2) atTop atTop := by
    simpa using hRclim.const_mul_atTop (two_pos : (0 : ℝ) < 2)
  have hLX : ∀ n, ENNReal.ofReal ((L n - 2) / Real.sqrt (2 * Rc n)) ≤
      ENNReal.ofReal ((L n - 2) / Real.sqrt (R n)) := fun n => by
    rcases le_total 0 (L n - 2) with h | h
    · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left h (Real.sqrt_pos.2 (hRpos n))
        (Real.sqrt_le_sqrt (by linarith [hRcl n])))
    · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg _))]
      exact bot_le
  -- hwitC / hderivC：在 X := 2R_c 上调用（阈值 4X > 4R），再精确重标到 R_c（阈值 8R_c）
  obtain ⟨hwCX, hdCX⟩ := hW (eps := ε) (C1' := C1) (C2' := C2) (Ctime' := Ctime) K t y'
    (fun n => 2 * Rc n) (fun _ => 1) (fun n => L n - 2) Tn aSeed haT
    (fun n => (hts n).trans (hsT n)) hat pT seedTrace hhalf htime
    (fun n => by linarith [hRcpos n]) hL2 (Filter.Eventually.of_forall hsm)
    (Filter.Eventually.of_forall hclock) hRr1X (a₀ := 0) le_rfl (Filter.Eventually.of_forall
      fun n => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n)
    (fun n => pF.rescale_P6N (c n) (hc n)) (fun _ => 0)
    (fun n e _ => (records (ind n) e).rescale_P6M (c n) (hc n))
    (Filter.Eventually.of_forall fun n e _ b =>
      ((records (ind n) e).static b).hasCanonicalWindow_rescale_P6M (hcanF _ _ b) _ _)
    (Filter.Eventually.of_forall fun _ =>
      hacc.trans ((min_le_left _ _).trans (min_le_right _ _)))
    (Filter.Eventually.of_forall fun _ => hord) (Filter.Eventually.of_forall fun _ => hrad)
    (fun T' hT' C hC => by
      filter_upwards [hsepWK' (T' + 1) (by linarith) (4 * C) (by linarith)] with n hn e _ b he
      have he' : (t n : ℝ) - T' / (2 * Rc n) < (K n).time e.succ := he
      refine lt_of_le_of_lt ?_ (hn e b ?_)
      · refine mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) (by norm_num)
        change C * (2 * Rc n) ≤ 4 * C * R n
        nlinarith [mul_le_mul_of_nonneg_left (hRc2 n).le hC]
      · have h1 := hclose n
        have h2 : (T' + 1) / R n = T' / R n + 1 / R n := add_div _ _ _
        have h3 := hdivX n T' hT'.le
        linarith)
    (fun T' hT' => by
      filter_upwards [hwinX T' hT'] with n hn
      change (0 : ℝ) ≤ (t n : ℝ) - T' / (2 * Rc n)
      linarith [hone n])
    (fun n v hav hvs hwv z hd hz => hgood' n v hav hvs
      (by
        have hwv' : (t n : ℝ) - (L n - 2) ^ 2 / (2 * Rc n) ≤ (v : ℝ) := hwv
        have := hdivX n ((L n - 2) ^ 2) (sq_nonneg _)
        linarith)
      z (hd.trans (add_le_add le_rfl (hLX n)))
      (le_trans (by linarith [hRcl n] : 4 * R n ≤ 4 * (2 * Rc n)) hz))
    hwinX
  have hwC := hwitC_half_MTR (Hs := Kh) (ts := t) (ys := y') hwCX
  have hdC := hderivC_half_MTR (Hs := Kh) (ts := t) (ys := y') hdCX
  -- hseed ⇐ hsurvive（A = 2·1，小 T）+ hanchor0 + hkappaC（DRV-HI 法，R_c 归一化）
  obtain ⟨Qa, hQa2, hQaev⟩ := hanchor0 (2 * 1) (by norm_num)
  have hCst0 : (0 : ℝ) ≤ (Cst : ℝ) := NNReal.coe_nonneg Cst
  have hden : 0 < 4 * (Cst : ℝ) * Qa + 1 := by
    have := mul_nonneg hCst0 (by linarith : (0 : ℝ) ≤ Qa)
    linarith
  have hT0pos : 0 < 1 / (4 * (Cst : ℝ) * Qa + 1) := by positivity
  have hT04 : 4 * (Cst : ℝ) * Qa * (1 / (4 * (Cst : ℝ) * Qa + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨K1, hK1, hev1⟩ := hhsurvive (2 * 1) (1 / (4 * (Cst : ℝ) * Qa + 1)) Qa (by norm_num)
    hT0pos hQa2 hT04
  have hTR1 : ∀ᶠ n in atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * 1 / Real.sqrt (Rc n))
      ((1 / (4 * (Cst : ℝ) * Qa + 1)) / Rc n) (K1 * Rc n) :=
    (hev1.and hQaev).mono fun n hn => hn.1 hn.2
  have hkap1 := hhkappaC id strictMono_id 1 (1 / (4 * (Cst : ℝ) * Qa + 1)) K1 one_pos hT0pos hK1
    (by rw [Filter.map_id]; exact hTR1)
  rw [Filter.map_id] at hkap1
  have hr₀pos : 0 < min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) :=
    lt_min (lt_min one_pos hT0pos) (by positivity)
  have hr₀1 : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hr₀T : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) ≤
      1 / (4 * (Cst : ℝ) * Qa + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hr₀K : min (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1)) * (K1 + 1) ≤ 1 := by
    have h := min_le_right (min 1 (1 / (4 * (Cst : ℝ) * Qa + 1))) (1 / (K1 + 1))
    have hK1' : 0 < K1 + 1 := by linarith
    calc _ ≤ 1 / (K1 + 1) * (K1 + 1) := mul_le_mul_of_nonneg_right h hK1'.le
      _ = 1 := by field_simp
  have hctrl := hTR1.mono fun n hn => ObservedHistory.controlled_of_traced_DH (Kh n) (t n) (y' n)
    (hRcpos n) hK1 hr₀pos hr₀1 hr₀T hr₀K hn
  have hhseed := ObservedHistory.hseed_of_tracedKappa_smallT_DH hRcpos
    (fun _ : ℕ => (1 : ℝ) / 200) hradiic hT0pos hkap1 hr₀pos hctrl
  -- hpinch ⇐ HI（同一 phi；v ∈ [t − T/R_c, t] ⊂ event slab ∩ Ici ½）
  have hhpinch : ∀ D T' : ℝ, 0 < D → 0 < T' → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
          (D / Real.sqrt (Rc n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T' / Rc n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
        ((Kh n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))) := by
    intro D T' _ hT'
    filter_upwards [hwinc T' hT'] with n hn x _ v hvt hv tr
    have hvw : (1 / 2 : ℝ) ≤ v := by linarith [hone n]
    have hvj : (v : ℝ) < (K n).time (i n).succ := lt_of_le_of_lt hvt (hslab n).2
    exact ObservedHistory.curvatureLB_stage_of_eventPinched_HTP (K n) (hpinK ind c hc n) v hvw
      (i n) hvj _
  obtain ⟨σd, hσd, hDE⟩ := ObservedHistory.exists_subseq_forall_depthExtendable_kappaC_P6KA Kh t y'
    Rc hRcpos hRclim hhsurvive hanchor0 hhextend hr₀pos hκA hhseed hκA (fun _ => 1 / 200) hradiic
    hhkappaC hphi hhpinch hε hεX hεN (Cs := 8) (qs := fun n => 8 * Rc n) (fun _ => le_rfl) hwC
    (Cq := 8) (qcan := fun n => 8 * Rc n) (fun _ => le_rfl) hdC hhbcadC
  exact false_of_depthExtendable_Rc_MTR hσd hr hT hRpos hRcpos hRc2 (hDE (2 * T) (by positivity))
    hbadTR

/-- consumer：G2 桥 `hTRs_of_res_gate_MTR` 的实际调用点取驱动常数 `ε₀ > 0`。 -/
example : ∃ ε₀ : ℝ, 0 < ε₀ := by
  obtain ⟨ε₀, hε₀, -⟩ := hTR_of_driver_gate_MTR.{0}
  exact ⟨ε₀, hε₀⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
