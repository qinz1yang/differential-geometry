import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11KappaCInteriorJ11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11OrigFrameJ11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersLocP6KT2c
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# hgap J11 ⇐ FRESH + interior footprint `hfpL_hPN` ⇐ `hDext`（O-CH11-J11STAY G3，后缀 `_J11S`）

KT2c 局部阈值 producer `hgapJ_loc_of_producers_P6KT2c` 的 OPEN binder `hJ11`（κ 沿任意已存在的 backward
trace，原尺度帧 + `scaleMetric (R/c)`）。分解（J8KAPPA 判定）：
* **footprint `hfpL_hPN`**（重标度帧，`hfpL_hPN_of_depthExt_J11S`，PROVED ⇐ 塔层 interior stay 的实例
  `hstayK` + `hDext` + top gate `hdistσ`）：`∀ D B > 0, ∀ᶠ n`，从 `B_σ(y, D/√R)` 出发、深度 `B/R` 的任意
  trace 在 `v` 处落在 `B_v(O_v, A + 3)`。traced region 由 `hDext`（hPN 中心 driver 输出）沿子列给，
  子列 → `∀ᶠ` 用子列原理（`eventually_of_subseq_J11S`）。
* **κ 半边**（`hJ11_of_fresh_fpL_J11S`，PROVED ⇐ 重标度 FRESH(A + 3) + `hfpL_hPN`）：FRESH 在 footprint
  内给 κ（`b ≤ 1/200`），G3a `volume_orig_of_rescale_J11S` 搬回原尺度；结论 = J11 体逐字。
* **binder 级 producer** 见 G3c（`P6J11HgapWireJ11S`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- 子列原理（`_J11S`）：每个子列都有更细的子列使 `P` 终将成立 ⇒ `P` 终将成立。 -/
theorem eventually_of_subseq_J11S {P : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ k in atTop, P (φ (ψ k))) :
    ∀ᶠ n in atTop, P n := by
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hne
  obtain ⟨ψ, -, hk⟩ := h φ hφ
  obtain ⟨k, hk⟩ := hk.exists
  exact hφP (ψ k) hk

/-- **footprint `hfpL_hPN` ⇐ `hDext`（`_J11S`，PROVED ⇐ `hstayK` + `hDext` + top gate）**：重标度帧，
`∀ D B > 0, ∀ᶠ n`，从 `B_σ(y, D/√R)` 出发、起点 `v ∈ [σ − B/R, σ]` 的任意 trace 满足
`d_v(O_v, tr(v)) < (A + 3)·1`。`hstayK` = G1 `hstay_interior_tower_J11S` 在本实例上的结论。 -/
theorem hfpL_hPN_of_depthExt_J11S {Kh : ℕ → ObservedHistory.{u}}
    {Tn aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon} {haT : ∀ k, aSeed k ≤ Tn k}
    {pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier}
    (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
      ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
    (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
    (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ) {A : ℝ}
    (hRpos : ∀ k, 0 < R k) (hL : Tendsto L atTop atTop)
    (hstayK : ∀ T r : ℝ, 0 < T → 0 < r → ∀ K : ℝ, 0 ≤ K → ∀ᶠ k in atTop,
      (Kh k).isTracedRegion (σ k) (y k) (r / Real.sqrt (R k)) (T / R k) (K * R k) →
      ∀ x ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)
          (r / Real.sqrt (R k)),
      ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hvt : v ≤ σ k), (σ k : ℝ) - T / R k ≤ v →
      ∀ (hav : aSeed k ≤ v)
        (tr : BackwardPointTrace (Kh k) ((Kh k).activeStage v) ((Kh k).activeStage (σ k))
          ((Kh k).activeStage_mono hvt) x),
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
            ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
              ((Kh k).activeStage_mono (hvt.trans (hsT k))))
            (tr.point ((Kh k).activeStage v) le_rfl ((Kh k).activeStage_mono hvt)) ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k))
                ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / Real.sqrt (R k)))
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T)
    (hdistσ : ∀ᶠ k in atTop,
      riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k) +
        ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) :
    ∀ D B : ℝ, 0 < D → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ (hav : aSeed n ≤ v)
        (tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x),
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvt.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal ((A + 3) * 1) := by
  intro D B hD hB
  refine eventually_of_subseq_J11S fun φ hφ => ?_
  obtain ⟨ψ, hψ, hdx⟩ := hDext φ hφ
  obtain ⟨K, hK0, htr⟩ := hdx B hB D hD
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [htr, hφψ.tendsto_atTop (hstayK B D hB hD K hK0), hφψ.tendsto_atTop hdistσ,
    hφψ.tendsto_atTop (hL.eventually_ge_atTop 0)] with i hTR hst hdσ hL0
  intro x hx v hvt hvT hav tr
  have h := hst hTR x hx v hvt hvT hav tr
  have hfin : riemannianEDistOf ((Kh (φ (ψ i))).stageMetric
      ((Kh (φ (ψ i))).activeStage (σ (φ (ψ i)))) (σ (φ (ψ i))))
      ((seedTrace (φ (ψ i))).point ((Kh (φ (ψ i))).activeStage (σ (φ (ψ i))))
        ((Kh (φ (ψ i))).activeStage_mono (has (φ (ψ i))))
        ((Kh (φ (ψ i))).activeStage_mono (hsT (φ (ψ i))))) (y (φ (ψ i))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hdσ)
  have hL0' : (0 : ℝ) ≤ L (φ (ψ i)) := hL0
  have hsR : 0 < Real.sqrt (R (φ (ψ i))) := Real.sqrt_pos.2 (hRpos _)
  have hlt : ENNReal.ofReal (L (φ (ψ i)) / Real.sqrt (R (φ (ψ i)))) <
      ENNReal.ofReal ((L (φ (ψ i)) + 1) / Real.sqrt (R (φ (ψ i)))) := by
    refine (ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hsR)).mpr ?_
    exact div_lt_div_of_pos_right (by linarith) hsR
  exact lt_of_le_of_lt h (lt_of_lt_of_le (ENNReal.add_lt_add_left hfin hlt) hdσ)

end ObservedHistory

/-- **J11 ⇐ FRESH + `hfpL_hPN`（实例，`_J11S`，PROVED）**：重标度 FRESH（footprint 系数 `A + 3`、`r = 1`，
`nrK` / `TfK` 任意，FRESH 前提逐项给出）+ footprint ⇒ J11 体逐字（原尺度帧，`scaleMetric (R/c)`，
`κd = κ`）。 -/
theorem hJ11_of_fresh_fpL_J11S {Ho : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ}
    (hc : ∀ k, 0 < c k)
    {Tn aSeed : ∀ k, Icc (0 : ℝ) ((Ho k).rescale_P6N (c k) (hc k)).toHistory.horizon}
    {haT : ∀ k, aSeed k ≤ Tn k}
    {pT : ∀ k, (((Ho k).rescale_P6N (c k) (hc k)).toHistory.stageAt (Tn k)).Carrier}
    (seedTrace : ∀ k, BackwardPointTrace ((Ho k).rescale_P6N (c k) (hc k)).toHistory
      (((Ho k).rescale_P6N (c k) (hc k)).toHistory.activeStage (aSeed k))
      (((Ho k).rescale_P6N (c k) (hc k)).toHistory.activeStage (Tn k))
      (((Ho k).rescale_P6N (c k) (hc k)).toHistory.activeStage_mono (haT k)) (pT k))
    (σ : ∀ k, Icc (0 : ℝ) ((Ho k).rescale_P6N (c k) (hc k)).toHistory.horizon)
    (y : ∀ k, (((Ho k).rescale_P6N (c k) (hc k)).toHistory.stageAt (σ k)).Carrier)
    (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) {A κ : ℝ} (hκ : 0 < κ)
    (hRpos : ∀ k, 0 < R k)
    (nrK : ℕ → ℝ → ℝ) (TfK : ℕ → ℝ)
    (hsupK : ∀ k, KappaSeedWindowFwd_C11PK (nrK k) (A + 3) κ (TfK k)
      ((Ho k).rescale_P6N (c k) (hc k)).toHistory)
    (hTf : ∀ᶠ k in atTop, TfK k ≤ (Tn k : ℝ)) (h2 : ∀ k, 2 * (1 : ℝ) ^ 2 < (Tn k : ℝ))
    (hsm : ∀ k, GC.LongTime.hasSmallParabolicCurvature ((Ho k).rescale_P6N (c k) (hc k)).toHistory
      (Tn k) (pT k) 1)
    (hvol : ∀ k, ENNReal.ofReal ((A + 3)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume (((Ho k).rescale_P6N (c k) (hc k)).toHistory.stageMetric
        (((Ho k).rescale_P6N (c k) (hc k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) 1)
    (hnr : ∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) → nrK k w ≤ 1)
    (hclock : ∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k)
    (hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k)
    (hradii : Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop)
    (hfpL : ∀ D B : ℝ, 0 < D → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon) (hvt : v ≤ σ n),
        (σ n : ℝ) - B / R n ≤ v →
      ∀ (hav : aSeed n ≤ v)
        (tr : BackwardPointTrace ((Ho n).rescale_P6N (c n) (hc n)).toHistory
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v)
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n))
          (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt) x),
        riemannianEDistOf (((Ho n).rescale_P6N (c n) (hc n)).toHistory.stageMetric
            (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) v)
            ((seedTrace n).point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v)
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hav)
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono (hvt.trans (hsT n))))
            (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
              (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt)) <
          ENNReal.ofReal ((A + 3) * 1)) :
    ∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ := by
  refine ⟨κ, hκ, fun D Lv B hD hLv hB => ?_⟩
  have hrad := hradii.eventually_ge_atTop Lv
  filter_upwards [hfpL D B hD hB, hTf, hwin B hB, hwin' B hB, hrad] with n hfp hTfn hwn hwn' hrn
  have hRn := hRpos n
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hLρ : Lv / Real.sqrt (R n) ≤ 1 / 200 := by
    rw [div_le_iff₀ hsR]
    linarith
  refine (Ho n).volume_orig_of_rescale_J11S (hc n) ((Ho n).unscaleTime_P6X (hc n) (σ n))
    ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (div_pos hRn (hc n)) (σ n) (y n) hRn
    ((Ho n).rescale_unscaleTime_P6X (hc n) (σ n))
    (((Ho n).heq_castRescale_P6X (hc n) _ _).trans
      ((Ho n).heq_uncastRescale_P6CK (hc n) (σ n) (y n)))
    (mul_div_cancel₀ (R n) (hc n).ne') hLρ ?_
  intro x hx v hvt hvT tr b hb hbρ hctrl
  have hvT' : (σ n : ℝ) - B / R n ≤ (v : ℝ) := hvT
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    linarith
  have hvTn : v ≤ Tn n := hvt.trans (hsT n)
  have hτw : (Tn n : ℝ) - 1 ^ 2 / 2 ≤ v := by linarith
  have hmem := hfp x hx v hvt hvT hav tr
  exact hsupK n (Tn n) (pT n) 1 hTfn (h2 n) (hsm n) (hvol n) (hnr n) (aSeed n) (haT n)
    (hclock n) (seedTrace n) v hav hvTn hτw
    (tr.point (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage v) le_rfl
      (((Ho n).rescale_P6N (c n) (hc n)).toHistory.activeStage_mono hvt)) hmem b hb.le
    (by linarith) hctrl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
