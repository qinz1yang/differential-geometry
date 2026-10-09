import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaR4FrameR4K

/-!
# MTRS：R4 帧 hkappaC 体的中心归一化泛型版（`Rc`，后缀 `_MTR`；HOLD 件 `P6KappaR4FrameRcR4K` 的换行孪生，内容逐字）

G2 `hkappaC_R4frame_of_fresh_R4K` 逐字前缀（σ 侧数据、hclose / hcompR 保持 `R` 形），加自由序列 `Rc` 与
`R/2 < Rc < 2R`、`k + 1 ≤ Rc k`（R4NORM 取 `Rc = scalar(t, y′)`，接口同
`hbcadC_R4center_Rc_R4B`）；结论 = hkappaC 槽体把 `R n` 全换 `Rc n`。内部：G1 body 以 `R := Rc`、
`L := L/2`、`Cg := 8` 调用；hgood 窗 / 半径 / 阈值由
`R ≤ 4Rc` 转换；hdy ⇐ hcompR（`1/√R ≤ (L/4)/√Rc`，`Rc ≤ 4R`、`L ≥ 8`）；窗口 `T ↦ 2T + 1`；hsepWK′ 取
`C = 4Qb`（`2Qb·Rc < 4Qb·R`）；footprint `(L/2)/√Rc ≤ L/√R`。
`Rc := R` 时即 G2（G2 独立证明，不经本文件）。
原件 `P6KappaR4FrameRcR4K.lean`（R4KAP 生成器 gRc.py）：仅第 8 行注释拆行、三个声明名 `_R4K`→`_MTR`。
-/

set_option autoImplicit false

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

/-- 因子 2（`_MTR`，PROVED）：`a ≤ 4b` ⇒ `√a ≤ 2√b`。 -/
theorem sqrt_le_two_mul_sqrt_MTR {a b : ℝ} (h : a ≤ 4 * b) :
    Real.sqrt a ≤ 2 * Real.sqrt b := by
  have h1 : Real.sqrt a ≤ Real.sqrt (2 ^ 2 * b) := Real.sqrt_le_sqrt (by linarith)
  rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at h1

/-- 因子 2 算术（`_MTR`，PROVED）：`R/2 < Rc < 2R`、`L ≥ 8` 下 R4 帧 `R ↔ Rc` 的五个换算。 -/
theorem rc_factor_two_MTR {R Rc L T : ℝ} (hR : 0 < R) (hlo : R / 2 < Rc) (hhi : Rc < 2 * R)
    (hL8 : 8 ≤ L) (hT : 0 < T) :
    T / Rc ≤ 2 * T / R ∧ 1 / R < 3 / 4 * ((L / 2) ^ 2 / Rc) ∧
    1 / Real.sqrt R ≤ L / 2 / 2 / Real.sqrt Rc ∧ L / 2 / Real.sqrt Rc ≤ L / Real.sqrt R ∧
    (L / 2) ^ 2 / Rc ≤ L ^ (2 : ℕ) / R := by
  have hRc : 0 < Rc := by linarith
  have hsR := Real.sqrt_pos.2 hR
  have hsRc := Real.sqrt_pos.2 hRc
  have hsq1 : Real.sqrt R ≤ 2 * Real.sqrt Rc := sqrt_le_two_mul_sqrt_MTR (by linarith)
  have hsq2 : Real.sqrt Rc ≤ 2 * Real.sqrt R := sqrt_le_two_mul_sqrt_MTR (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hRc hR]
    have := mul_le_mul_of_nonneg_left (show R ≤ 2 * Rc by linarith) hT.le
    linarith
  · have h1 : 1 / R < 2 / Rc := by
      rw [div_lt_div_iff₀ hR hRc]
      linarith
    have h64 : (8 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL8 2
    have h2 : 2 / Rc ≤ 3 / 16 * L ^ 2 / Rc :=
      div_le_div_of_nonneg_right (by nlinarith) hRc.le
    have he : 3 / 4 * ((L / 2) ^ 2 / Rc) = 3 / 16 * L ^ 2 / Rc := by ring
    linarith
  · rw [div_le_div_iff₀ hsR hsRc]
    have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L / 2 / 2 by linarith) hsR.le
    linarith
  · rw [div_le_div_iff₀ hsRc hsR]
    have := mul_le_mul_of_nonneg_left hsq1 (show (0 : ℝ) ≤ L / 2 by linarith)
    linarith
  · rw [div_le_div_iff₀ hRc hR]
    have := mul_le_mul_of_nonneg_left (show R / 4 ≤ Rc by linarith) (sq_nonneg L)
    calc (L / 2) ^ 2 * R = L ^ 2 * (R / 4) := by ring
      _ ≤ L ^ 2 * Rc := this

/-- **R4 帧 hkappaC 体，中心归一化泛型版（`_MTR`，PROVED ⇐ driver 实际元组 + FRESH）**：见模块文档。 -/
theorem hkappaC_R4frame_Rc_of_fresh_MTR :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters} {ε C1 : ℝ}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius → 0 ≤ C2 →
      ∀ (q : CutoffParameters) {Aseed κ Tf : ℝ}, 0 < Aseed →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        (∀ k, KappaSeedWindowFwd_C11PK
            (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
            (Tf / c k) (Kh k)) →
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
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
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
          (∀ k,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
              ((seedTrace k).point ((Kh k).activeStage (t k)) ((Kh k).activeStage_mono (hat k))
                ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (1 / Real.sqrt (R k))) →
      ∀ Rc : ℕ → ℝ, (∀ k, R k / 2 < Rc k) → (∀ k, Rc k < 2 * R k) →
        (∀ k : ℕ, (k : ℝ) + 1 ≤ Rc k) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (t n) (y' n) (2 * D / Real.sqrt (Rc n))
          (T / Rc n) (K * Rc n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (y' n)
            (D / Real.sqrt (Rc n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / Rc n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (t n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ (1 / 200) →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' := by
  obtain ⟨ε₃, hε₃, hB⟩ := ObservedHistory.hstopE_body_deep_fixT_R4K.{u}
  refine ⟨ε₃, hε₃, ?_⟩
  intro P g F C2 Ctime pF ε C1 records hcanF hacc hord hrad hC2 q Aseed κ Tf hAs ind c hc Kh hsupK
    Tn pT hTc aSeed haT hclock hone hsm hvol hTn2 hnrS seedTrace σ y R hsT has L hRpos _ hL hgood
    haS hTnS hgateP i hi hsepWK pm t y' hat hts hy' hslab hclose hcompR Rc hRcLo hRcHi hRcr
    φ hφ D T K hD hT hK hTRev
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max (9 * K) 8) 1 := ⟨_, rfl⟩
  have hQb : max (max (9 * K) 8) 1 ≤ Qb := hQbdef ▸ le_rfl
  have hQ1 : (1 : ℝ) ≤ Qb := (le_max_right _ _).trans hQb
  have h9Q : 9 * K ≤ Qb := (le_max_left _ _).trans ((le_max_left _ _).trans hQb)
  have hX : 0 ≤ 2 * (Ctime : ℝ) * Qb := by positivity
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 1 / (2 * (Ctime : ℝ) * Qb + 1) := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβs : 2 * (Ctime : ℝ) * Qb * β ≤ 1 := by
    rw [hβdef, mul_one_div, div_le_one (by linarith)]
    linarith
  obtain ⟨cn, hcn, hnumF⟩ := crossSlab_numerics_P6JW (C2' := C2) (r := 1) hC2 hQ1 one_pos
  have hTf : ∀ᶠ k in atTop, Tf ≤ c k * (Tn k : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈Tf⌉₊] with k hk
    have h1 := hTc k
    have h2 : (⌈Tf⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.le_ceil Tf]
  have hmain : ∀ᶠ k in atTop,
      (Kh k).isTracedRegion (t k) (y' k) (2 * D / Real.sqrt (Rc k)) (T / Rc k) (K * Rc k) →
      ∀ x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)
          (D / Real.sqrt (Rc k)),
      ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hvt : v ≤ t k), (t k : ℝ) - T / Rc k ≤ v →
      ∀ tr : BackwardPointTrace (Kh k) ((Kh k).activeStage v) ((Kh k).activeStage (t k))
        ((Kh k).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ (1 / 200) →
        (Kh k).isParabolicallyRmControlledBall v
          (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((Kh k).stageMetric ((Kh k).activeStage v) v)
            (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) r'' := by
    filter_upwards [hsepWK (2 * T + 1) (by linarith) (4 * Qb) (by linarith),
      haS (2 * T + 1) (by linarith), hTnS (2 * T + 1) (by linarith),
      hL.eventually_ge_atTop (8 * (2 * D + 8 * T / cn) + 1),
      hL.eventually_ge_atTop (16 * (localPropagationRadius C2 / Real.sqrt (2 * Qb))),
      hL.eventually_ge_atTop (4 * T + 4), hL.eventually_ge_atTop 8, hTf]
      with k hsepk haSk hTnSk hL1 hL2 hL3 hL8 hTfk
    intro hTR x hx v hvt hvT tr b hb0 hbρ hctrl
    have hRk := hRpos k
    have hlo := hRcLo k
    have hhi := hRcHi k
    have hRck : 0 < Rc k := by linarith
    have hR1 : (1 : ℝ) ≤ Rc k := by
      have h := hRcr k
      have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hsR := Real.sqrt_pos.2 hRk
    have hsRc := Real.sqrt_pos.2 hRck
    obtain ⟨ℓ, K', hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ :=
      hnumF (R := Rc k) (L := L k / 2 / 2) (D := 2 * D) (T := T) hR1 (by linarith) (by linarith)
    have hh : T + 1 ≤ L k / 2 / 2 := by linarith
    have hTL : T ≤ (L k / 2 / 2) ^ 2 := by
      have h1 := mul_le_mul hh hh (by linarith) (by linarith)
      have h2 : T + 1 ≤ (T + 1) * (T + 1) := le_mul_of_one_le_right (by linarith) (by linarith)
      rw [sq]
      linarith
    have hL0 : 0 ≤ L k / 2 := by linarith
    have h2T1 : (2 * T + 1) / R k = 2 * T / R k + 1 / R k := add_div _ _ _
    have h2TR : 0 < 2 * T / R k := div_pos (by linarith) hRk
    have h1R : 0 < 1 / R k := one_div_pos.mpr hRk
    have haσ : (aSeed k : ℝ) < σ k := by linarith
    have hRa : 1 ≤ Rc k * aSeed k := one_le_mul_of_one_le_of_one_le hR1 (hone k)
    have ht1 := (hslab k).1
    have ht2 := (hslab k).2
    have hclk := hclose k
    obtain ⟨hTRc, h3, hdiv, hhalf, hwin⟩ := rc_factor_two_MTR hRk hlo hhi hL8 hT
    have hTlo : (σ k : ℝ) - (2 * T + 1) / R k ≤ (t k : ℝ) - T / Rc k := by linarith
    have ht3 : (σ k : ℝ) - 3 / 4 * ((L k / 2) ^ 2 / Rc k) < t k := by linarith
    have hfin : riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add (hgateP k))
    have hTRt : ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t k →
        ∀ y'' : ((Kh k).stageAt tt).Carrier, HEq y'' (pm k) →
          (Kh k).isTracedRegion tt y'' (2 * D / Real.sqrt (Rc k)) (T / Rc k) (K * Rc k) := by
      intro tt htt y'' hy''
      obtain rfl : tt = t k := Subtype.ext htt
      obtain rfl : y'' = y' k := eq_of_heq (hy''.trans (hy' k).symm)
      exact hTR
    have hth : (t k : ℝ) ≤ (Kh k).horizon := (t k).2.2
    have h9 : 9 * K * Rc k ≤ Qb * Rc k := mul_le_mul_of_nonneg_right h9Q hRck.le
    have hst := hB (Cg := 8) (Cball := 9 * K) (Qb := Qb) (ρb := 2 * D) (β := β) hC2
      ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (Kh k) rfl (haT k) (hsm k) (hclock k)
      (seedTrace k) le_rfl
      (fun τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
      (hsT k) (has k) (y k) (L k / 2) hRck
      (fun v hav hvs hvw z hz hsc => hgood k v hav hvs (by linarith) z
        (hz.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hhalf))) (by linarith))
      hQb hβ hβs hT hTL hL0 hRa haσ hℓ hKℓ hℓr hKr hKC
      hℓρ hρL hnum (T₀ := 0) (aSeed k).2.1
      (fun e _ => (records (ind k) e).rescale_P6M (c k) (hc k))
      (fun e _ => ((records (ind k) e).rescale_P6M (c k) (hc k)).old_eq_retained)
      (fun e _ b => ((records (ind k) e).static b).hasCanonicalWindow_rescale_P6M
        (hcanF _ _ b) _ _)
      hrad hacc hord hTlo
      (fun e _ b hlt => by
        have h := hsepk e b hlt
        have hQR := mul_le_mul_of_nonneg_left hhi.le (by linarith : (0 : ℝ) ≤ Qb)
        have hm : max (3 / (1 : ℝ) ^ 2) (2 * (Qb * Rc k)) ≤
            max (3 / ((1 : ℝ) / 100) ^ 2) (4 * Qb * R k) :=
          max_le_max (by norm_num) (by linarith)
        linarith)
      hfin (i k) (hi k) (pm k) ht1 ht2 ht3
      (fun tt htt _ _ y'' hy'' => by
        obtain rfl : tt = t k := Subtype.ext htt
        obtain rfl : y'' = y' k := eq_of_heq (hy''.trans (hy' k).symm)
        exact (hcompR k).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdiv)))
      (fun z hz => ((Kh k).ballAt_of_TRat_P6KA (i k) (pm k) hRck hK ht1 ht2 hth hTRt z hz))
      (fun tt h1 h2 a h3 hat' h4 z' hP A j hj w haw hwt hw =>
        ((Kh k).gridAt_of_TRat_P6KA (i k) (pm k) hRck hK ht1 ht2 hTRt tt h1 h2 a h3 hat' h4
          z' hP A j hj w haw hwt hw).trans h9)
    have he : (Kh k).activeStage (t k) = (i k).castSucc :=
      (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) (t k) ht1.le ht2
    have hx2 : x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)
        (2 * D / Real.sqrt (Rc k)) :=
      riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (by linarith) hsRc.le) hx
    have hP : ∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq x z →
        z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric (t k)) (pm k)
          (2 * D / Real.sqrt (Rc k)) := by
      intro z hz
      have h1 := (ObservedHistory.ball_transport_P6BB he rfl x (y' k) z (pm k) hz (hy' k)).mp hx2
      rwa [ObservedHistory.stageMetric_castSucc_apply] at h1
    have haSv : aSeed k ≤ v := by
      change (aSeed k : ℝ) ≤ v
      linarith
    have hd := hst (t k) rfl (hts k) v haSv hvt hvT x hP tr v le_rfl hvt
    have hvTn : v ≤ Tn k := (hvt.trans (hts k)).trans (hsT k)
    have hτw : (Tn k : ℝ) - 1 ^ 2 / 2 ≤ v := by linarith
    have hTn' : Tf / c k ≤ (Tn k : ℝ) := by
      rw [div_le_iff₀ (hc k)]
      linarith [mul_comm (c k) (Tn k : ℝ)]
    have hvolA : ENNReal.ofReal ((Aseed + 7)⁻¹ * 1 ^ 3) ≤
        ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) 1 := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvol k)
      have : (Aseed + 7)⁻¹ ≤ Aseed⁻¹ := inv_anti₀ hAs (by linarith)
      simpa using this
    have hL1' : L k / 2 / Real.sqrt (Rc k) ≤ (L k + 1) / Real.sqrt (R k) :=
      hhalf.trans (div_le_div_of_nonneg_right (by linarith) hsR.le)
    have hmem : riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
        ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono haSv)
          ((Kh k).activeStage_mono hvTn))
        (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) <
        ENNReal.ofReal ((Aseed + 7) * 1) := by
      refine lt_of_le_of_lt
        (hd.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hL1')).trans (hgateP k))) ?_
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    exact hsupK k (Tn k) (pT k) 1 hTn' (by linarith [hTn2 k]) (hsm k) hvolA (hnrS k)
      (aSeed k) (haT k) (hclock k) (seedTrace k) v haSv hvTn hτw
      (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) hmem b hb0.le
      (by linarith) hctrl
  exact (hTRev.and (hφ.tendsto_atTop hmain)).mono fun n hn => hn.2 hn.1

/-- consumer。 -/
example : True := by
  have := hkappaC_R4frame_Rc_of_fresh_MTR.{0}
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
