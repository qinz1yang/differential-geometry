import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV2P6HPB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepNeckP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW

/-!
# `hrecords` 槽的 late non-CWP：(CWS) + (SEP′) 本族孪生，直接 PROVED（O-CH11-NONCWP G1，后缀 `_P6NC`）

**G1 `hrecords_slot_P6NC`（PROVED，0 binder）**：结论 = HP6B2 v2 `hP6bTwoLevelTime_of_slots_v2_P6HPB2` 的
`hrecords` 槽**逐字**（生成器 `build-logs/scratch/O-CH11-NONCWP/gen_g1.py` 从 `P6HP6bAssemblyV2P6HPB2.lean`
l.1141–1208 切出，sha256 `af630e70…1fd2`；断言 = FOOT5 G3b `hrecords_slot_of_nCWP_P6F5` 的结论 = v6
`P6HP6bAssemblyCollarV3P6HPC.lean` 两处 `hrecords` 槽）。**本定理绕过了 FOOT5 G3b**
（不经其 binder `hnCWPslot`）：records 改取 SCRS⁺ 末字段（NOMID S14，带与 base records 的 nominal identity），
参数 `(max Rrad R, min ζ₀ ζ₀′, max 2 m₀)` 在 `Dcap` 已知后选（槽的 `∃ pp T₀ records` 允许）。

**FOOT5 冻结形 `hnCWPslot` 为何证不出（外审材料，O1–O3）**：该 binder 对**任意** linked late records 量化，
只给 `2 ≤ order`、`Rrad ≤ radius`（`Rrad` 自由）、`accuracy ≤ ζ₀ ≤ ζ*`（`ζ*` 在 `Dcap` 之前选），且 records
与 SCRS⁺ base records 之间**无** nominal identity。
* (O1) (CWS) 的唯一树内机制 = 标准解比较
  `exists_scalar_lower_bound_of_cap_window_trace_late_P6LL`
  （经 `exists_standard_comparison_of_cap_window_trace_late_P6LL`），它要 `R(Θ, D) ≤ modelRadius`
  （`R > D + 1`，`D ≥ Dcap`）、
  `m₀(Θ, D) ≤ modelOrder`（`m₀ ≥ 4`）、`modelAccuracy ≤ ζ₀(Θ, D)`——三者都依赖 `Dcap`，
  而 binder 的 records 只保证 `order ≥ 2`、自由 `Rrad`、`Dcap` 之前的 `ζ*`。
* (O2) (SEP′) 与 `hbirth`（`qcan ≤ Cbirth·scale`）对任意 record 只能走 record 自身的 `nominal_small`
  （`nom < δ(tᵢ)² ρ(tᵢ)`），要把 `ρ(tᵢ)` 换成 `ρ(σ)` 需参数级 `RecentScaleSupply_C11S q`
  （⇐ `RadiusDoublingSupply_C11S`，块间半径比）——树内无 producer（= HSCALESEP 的 `hstep` 缺口）；
  SCRS⁺ 的 `RecentCutoffSupply_C11S` 只管 base records 的 nominal 半径。
* (O3) 同一 event 的两个 record（任意 binder record 与 S14 精确 record）的 cap window 比较引理树内没有，
  故不能把任意 record 的 window 点换成精确 record 的 window 点。

**证明（数学一页）**：坏点 `y_k`、`p′ ↦ q′ ≍ y_k` crossing，`t ↑ σ_k`；假设 `p′` 回溯到 late record `i′`
（`i′⁺ ≤ (i k)⁻`）的 cap window 点 `w`（`‖w‖ < Dcap + 1`）、年龄 `t − tᵢ′ ≤ ½·scale⁻¹`。
* 连续性：`TerminalLimitMetric.tendsto_metricScalarAt` + `RegularCrossing.scalar_eq` +
  `transport_at_stage_P6JW` + `stageMetric_succ_time_C11G`
  ⇒ `R(t, p′) → R_k`，故 eventually `R(t, p′) < 2 R_k`。
* ceiling：`ceiling_of_not_good_P6SS` + `outerSupply_twoLevel_C11G2` 的 `hcan` / TDS
  （**正好**在 `hsel` 的元组
  `(Γ.ε, C1P6 std, C2P6 std, p6Ctime)`）⇒ `R_k ≤ c_k·Q`，`Q := ρ(c_k σ_k)⁻²`。
* 尺度：`static_scale_ge_of_recenter_P6CD`（late δ 小）⇒ `scale_o ≥ (2 nom²)⁻¹`；
  a priori `nom < ρ(0)` ⇒ 年龄
  `≤ ρ(0)²` ⇒ `tᵢ′ ∈ [σ_o/2, σ_o]`（`σ_o = c_k σ_k ≥ 4ρ(0)²`）；
  SCRS⁺ `RecentCutoffSupply_C11S` + NOMID nominal identity ⇒ `nom ≤ ε ρ(σ_o)`
  ⇒ `scale_o ≥ Q / (2ε²)`。
* (CWS)：`exists_scalar_lower_bound_of_cap_window_trace_late_P6LL` @ `Θ = ½`、`C = p6Ctime Γ`、
  `D = |Dcap| + 1`，于重标度 history：`hderiv` / `hcur` ⇐ TDS（阈值 `ρ(t)⁻² ≤ Q`，`ρ` antitone）+
  `eventSlabsDerivative_rescale_P6X3`；HI ⇐ `exists_initialHI_P6WR` + `hHI_rescale_P6X3`；
  `pF` = base records
  重标度，`δbound` ⇐ `δ → 0`；`hbirth` / `hbirthA` ⇐ `2ε² ≤ Cbirth`、`2ε²ρ(0)² ≤ a₀`；
  `scalar_ge_of_age_factor_P6SN` ⇒ `cc·scale ≤ R(t, p′)`。
* (SEP′)：`4ε² ≤ cc` ⇒ `2 R_k ≤ 2 c_k Q ≤ cc·scale ≤ R(t, p′) < 2 R_k`，矛盾。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory

/-- 常数选取（`_P6NC`）：`ε > 0` 使 `2ε² ≤ A`、`4ε² ≤ B`、`2ε²ρ² ≤ a`。 -/
theorem exists_eps_P6NC {A B a ρ : ℝ} (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hρ : 0 < ρ) :
    ∃ x : ℝ, 0 < x ∧ 2 * x ^ 2 ≤ A ∧ 4 * x ^ 2 ≤ B ∧ 2 * x ^ 2 * ρ ^ 2 ≤ a := by
  set e := min (A / 2) (min (B / 4) (a / (2 * ρ ^ 2))) with he
  have hepos : 0 < e := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hx1 := min_le_left 1 e
  have hx2 := min_le_right 1 e
  have hxpos : 0 < min 1 e := lt_min one_pos hepos
  have hsq : min 1 e ^ 2 ≤ e := by nlinarith
  have h1 : e ≤ A / 2 := min_le_left _ _
  have h2 : e ≤ B / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : e ≤ a / (2 * ρ ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min 1 e, hxpos, by linarith, by linarith, ?_⟩
  have h4 : min 1 e ^ 2 ≤ a / (2 * ρ ^ 2) := hsq.trans h3
  rw [le_div_iff₀ (by positivity)] at h4
  linarith

/-- 晚期（`_P6NC`）：clock `aSeed = Tn − 1`、`1 ≤ aSeed ≤ σ`、`k + 1 ≤ c Tn` ⇒ `c σ → ∞`（FOOT5 G3b 同款）。 -/
theorem tendsto_late_P6NC {c Tn aS σ : ℕ → ℝ} (hc : ∀ k, 0 < c k)
    (hTc : ∀ k : ℕ, (k : ℝ) + 1 ≤ c k * Tn k) (hclock : ∀ k, aS k = Tn k - 1 ^ (2 : ℕ))
    (h1 : ∀ k, 1 ≤ aS k) (has : ∀ k, aS k ≤ σ k) :
    Tendsto (fun k => c k * σ k) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_)
    ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
      two_pos)
  have hck := hc k
  have has' := has k
  have hcl := hclock k
  have h1k := h1 k
  have hT := hTc k
  nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
    mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ Tn k - 2)]

/-- `T₀` 门槛（`_P6NC`）：`2T₁ ≤ cσ`、`1 ≤ σ`、`B/R ≤ 1/2` ⇒ `T₁/c ≤ σ − B/R`。 -/
theorem thr_le_P6NC {c σ T₁ BR : ℝ} (hc : 0 < c) (hσ1 : 1 ≤ σ) (hk2 : 2 * T₁ ≤ c * σ)
    (hkB : BR ≤ 1 / 2) : T₁ / c ≤ σ - BR := by
  rw [div_le_iff₀ hc]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ σ / 2 - BR by linarith) hc.le]

/-- 尺度算术（`_P6NC`）：`1 ≤ 2 nom² S`、`nom ≤ ε ρ`、`ρ > 0` ⇒ `ρ⁻² ≤ 2ε² S`。 -/
theorem inv_sq_le_P6NC {nom S ε ρ : ℝ} (hn : 0 < nom) (hS : 0 < S) (hρ : 0 < ρ)
    (hB1 : 1 ≤ 2 * nom ^ 2 * S) (hnε : nom ≤ ε * ρ) : (ρ ^ 2)⁻¹ ≤ 2 * ε ^ 2 * S := by
  have h2 : nom ^ 2 ≤ (ε * ρ) ^ 2 := pow_le_pow_left₀ hn.le hnε 2
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * S)
  have hC : 1 ≤ (2 * ε ^ 2 * S) * ρ ^ 2 := by nlinarith
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  linarith

/-- 年龄算术（`_P6NC`）：`t − τ/c ≤ ½(cS)⁻¹`、`(2 nom²)⁻¹ ≤ S` ⇒ `c t − τ ≤ nom²`。 -/
theorem age_le_P6NC {c S nom t τ : ℝ} (hc : 0 < c) (hS : 0 < S) (hn : 0 < nom)
    (hw : t - τ / c ≤ 1 / 2 * (c * S)⁻¹) (hSlo : (2 * nom ^ 2)⁻¹ ≤ S) : c * t - τ ≤ nom ^ 2 := by
  have hB1 : 1 ≤ 2 * nom ^ 2 * S := by
    have h := mul_le_mul_of_nonneg_left hSlo (by positivity : (0 : ℝ) ≤ 2 * nom ^ 2)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  have h := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 2 * (c * S))
  have e1 : 2 * (c * S) * (t - τ / c) = (c * t - τ) * (2 * S) := by
    field_simp
  have e2 : 2 * (c * S) * (1 / 2 * (c * S)⁻¹) = 1 := by
    field_simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 * S)
  nlinarith

/-- a priori 尺度（`_P6NC`）：`nom < d² r`、`0 < d < 1`、`0 < r ≤ r₀` ⇒ `nom < r₀`。 -/
theorem nom_lt_P6NC {nom d r r₀ : ℝ} (hs : nom < d ^ 2 * r) (hd0 : 0 < d) (hd1 : d < 1)
    (hr : 0 < r) (hra : r ≤ r₀) : nom < r₀ := by
  have hdd : d ^ 2 < 1 := by nlinarith
  have : d ^ 2 * r ≤ r := by nlinarith
  linarith

/-- 时间窗（`_P6NC`）：`c t − τ ≤ nom² ≤ ρ₀²`、`4ρ₀² ≤ cσ`、`¾σ < t`、`τ/c ≤ σ` ⇒ `τ ∈ [cσ/2, cσ]`。 -/
theorem window_P6NC {c σ t τ nom ρ₀ : ℝ} (hc : 0 < c) (hage : c * t - τ ≤ nom ^ 2)
    (hnn : nom ^ 2 ≤ ρ₀ ^ 2) (hk4 : 4 * ρ₀ ^ 2 ≤ c * σ) (ht : 3 / 4 * σ < t) (hτ : τ / c ≤ σ) :
    c * σ / 2 ≤ τ ∧ τ ≤ c * σ := by
  have h1 := mul_lt_mul_of_pos_left ht hc
  rw [div_le_iff₀ hc] at hτ
  constructor
  · linarith only [h1, hage, hnn, hk4]
  · linarith only [hτ]

/-- 收尾算术（`_P6NC`）：`cc·(cS) ≤ X < 2R ≤ 2cQ`、`Q ≤ 2ε²S`、`4ε² ≤ cc` ⇒ 矛盾。 -/
theorem final_P6NC {cc c S X R Q ε : ℝ} (hc : 0 < c) (hS : 0 < S) (hcws : cc * (c * S) ≤ X)
    (hX : X < 2 * R) (hR : R ≤ c * Q) (hQS : Q ≤ 2 * ε ^ 2 * S) (hεcc : 4 * ε ^ 2 ≤ cc) :
    False := by
  have h1 := mul_le_mul_of_nonneg_right hεcc hS.le
  have h2 : 2 * Q ≤ cc * S := by linarith only [h1, hQS]
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  linarith only [h3, hcws, hX, hR]

/-- `hbirthA` 算术（`_P6NC`）：`Q ρ² = 1`、`ρ ≤ ρ₀`、`Q ≤ 2ε²S`、`2ε²ρ₀² ≤ a` ⇒ `1 ≤ a S`。 -/
theorem birthA_P6NC {Q ρ ρ₀ ε S a : ℝ} (hQ : 0 < Q) (hρ : 0 < ρ) (hS : 0 < S)
    (hQρ : Q * ρ ^ 2 = 1) (hρρ : ρ ≤ ρ₀) (hQS : Q ≤ 2 * ε ^ 2 * S) (hεa : 2 * ε ^ 2 * ρ₀ ^ 2 ≤ a) :
    1 ≤ a * S := by
  have h3 := mul_le_mul_of_nonneg_right hεa hS.le
  have h4 : ρ ^ 2 ≤ ρ₀ ^ 2 := pow_le_pow_left₀ hρ.le hρρ 2
  have h5 := mul_le_mul_of_nonneg_left h4 hQ.le
  have h6 := mul_le_mul_of_nonneg_right hQS (sq_nonneg ρ₀)
  linarith only [h3, h5, h6, hQρ]

/-- **单点矛盾（`_P6NC`）**：一个原尺度 history `H₀`、重标度 `c`、坏 event `j₀`
（`σ = time j₀⁺ / c`）、crossing 点 `p′`、`t ∈ (max(t_{j₀⁻}, ¾σ), σ)` 且 `R(t, p′) < 2R`；
若 `p′` 回溯到 late record `i′` 的 cap window（`‖w‖ < D + 1`、年龄 `≤ ½ scale⁻¹`）则矛盾。
(CWS) = P6LL 尾部 `hLL3`（常数已取定）；(SEP′) = ceiling `hR2` + RecentCutoff `hrc` +
nominal identity `hnomid` + `static_scale_ge_of_recenter_P6CD`。 -/
theorem nonCWP_point_P6NC {H₀ : RetainedCoreHistory.{u}} {c : ℝ} (hc : 0 < c)
    {C : ℝ≥0} {cc Cbirth Dd Rw ζw δw a₀ εr : ℝ} {m₀ : ℕ}
    (hLL3 : ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rw ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζw →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δw →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ 1 / 2 →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < Dd + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    cc * ((records j hj).static b).neck.scale ≤
      (1 - ((records j hj).static b).neck.scale * (t - H.time j.succ)) * Gk.flow.scalar t y)
    (hcc : 0 < cc) (hεCb : 2 * εr ^ 2 ≤ Cbirth) (hεcc : 4 * εr ^ 2 ≤ cc)
    {q₀ p : CutoffParameters} {Tthr T₁ : ℝ}
    (hεa : 2 * εr ^ 2 * q₀.neckRadius 0 ^ 2 ≤ a₀)
    (records : ∀ i : Fin H₀.eventCount, Tthr ≤ H₀.time i.succ →
      GeometricCutoffRecord H₀.toHistory i p)
    (records₀ : ∀ i : Fin H₀.eventCount, GeometricCutoffRecord H₀.toHistory i q₀)
    (hpδ : p.delta = q₀.delta) (hpρ : p.neckRadius = q₀.neckRadius)
    (hprc : p.recenterConstant = q₀.recenterConstant)
    (hlink : ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b))
    (hnomid : ∀ i hi, (records i hi).nominalRadius = (records₀ i).nominalRadius)
    (hRw : Rw ≤ p.modelRadius) (hm₀ : m₀ ≤ p.modelOrder) (hζw : p.modelAccuracy ≤ ζw)
    (hT₁a : Tthr ≤ T₁)
    (hTδ : ∀ s, T₁ ≤ s → q₀.delta s ≤ min δw (1 / (2 * q₀.recenterConstant)))
    (hρanti : AntitoneOn q₀.neckRadius (Ici 0))
    (hTD1 : ∀ (j : Fin H₀.eventCount) (y : (H₀.stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo (H₀.time j.castSucc) (H₀.time j.succ) →
      (q₀.neckRadius t ^ 2)⁻¹ < (H₀.toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H₀.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H₀.toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hHI : ∀ x, InFixedHamiltonIveyRegion (H₀.initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt (H₀.initialMetric 0) x)
    {j₀ : Fin H₀.eventCount} {σ R : ℝ}
    (hσ : σ = (H₀.rescale_P6N c hc).time j₀.succ)
    (hk4 : 4 * q₀.neckRadius 0 ^ 2 ≤ c * σ)
    (hrc : ∀ i : Fin H₀.eventCount, H₀.time i.succ ∈ Icc (c * σ / 2) (c * σ) →
      ∀ h, (records₀ i).nominalRadius h ≤ εr * q₀.neckRadius (c * σ))
    (hR2 : R ≤ c * (q₀.neckRadius (c * σ) ^ 2)⁻¹)
    {p' : (H₀.stage j₀.castSucc).Carrier} {t : ℝ}
    (ht2 : ((H₀.rescale_P6N c hc).toHistory.event j₀).incoming.flow.scalar t p' < 2 * R)
    (htI : t ∈ Ioo (max ((H₀.rescale_P6N c hc).time j₀.castSucc) (3 / 4 * σ))
      ((H₀.rescale_P6N c hc).time j₀.succ))
    (i' : Fin H₀.eventCount) (hT : T₁ / c ≤ (H₀.rescale_P6N c hc).time i'.succ)
    (hl : i'.succ ≤ j₀.castSucc)
    (Btr : BackwardPointTrace (H₀.rescale_P6N c hc).toHistory i'.succ j₀.castSucc hl p')
    (b : ((H₀.rescale_P6N c hc).toHistory.event i').RetainedBoundaryIndex)
    (w : standardCapWindow p.modelRadius)
    (hw1 : Btr.point i'.succ le_rfl hl =
      (((records i' (hT₁a.trans ((div_le_div_iff_of_pos_right hc).mp hT))).rescale_P6M c
        hc).static b).window w)
    (hxD : ‖w.val‖ < Dd + 1)
    (hw3 : t - (H₀.rescale_P6N c hc).time i'.succ ≤ 1 / 2 *
      ((((records i' (hT₁a.trans ((div_le_div_iff_of_pos_right hc).mp hT))).rescale_P6M c
        hc).static b).neck.scale)⁻¹) :
    False := by
  have hT1 : T₁ ≤ H₀.time i'.succ := (div_le_div_iff_of_pos_right hc).mp hT
  have hTt : Tthr ≤ H₀.time i'.succ := hT₁a.trans hT1
  -- 原尺度时刻 / 尺度 / nominal（不透明化）
  obtain ⟨tio, htio⟩ : ∃ x, H₀.time i'.succ = x := ⟨_, rfl⟩
  have htio0 : 0 ≤ tio := by
    rw [← htio]
    exact H₀.toHistory.time_nonneg i'.succ
  obtain ⟨So, hSodef⟩ : ∃ s, ((records i' hTt).static b).neck.scale = s := ⟨_, rfl⟩
  have hSo : 0 < So := by
    rw [← hSodef]
    exact ((records i' hTt).static b).neck.scale_pos
  have hSS : (((records i' hTt).rescale_P6M c hc).static b).neck.scale = c * So := by
    rw [← hSodef]
    exact ((records i' hTt).static b).rescale_P6M_scale c hc
  have hw3' : t - tio / c ≤ 1 / 2 * (c * So)⁻¹ := by
    rw [← htio, ← hSS]
    exact hw3
  obtain ⟨nom, hnomdef⟩ : ∃ r, (records i' hTt).nominalRadius ⟨b.1.1⟩ = r := ⟨_, rfl⟩
  have hnpos : 0 < nom := by
    rw [← hnomdef]
    exact (records i' hTt).nominal_pos _
  -- δ 条件 ⇒ static scale ≥ (2 nom²)⁻¹
  have hΛpos : 0 < q₀.recenterConstant := by linarith [q₀.recenterConstant_ge_four]
  have hδq : q₀.delta tio ≤ min δw (1 / (2 * q₀.recenterConstant)) := hTδ tio (htio ▸ hT1)
  have hδc : p.recenterConstant * p.delta (H₀.time i'.succ) ≤ 1 / 2 := by
    rw [hprc, hpδ, htio]
    have h2 : q₀.delta tio ≤ 1 / (2 * q₀.recenterConstant) := hδq.trans (min_le_right _ _)
    calc q₀.recenterConstant * q₀.delta tio
        ≤ q₀.recenterConstant * (1 / (2 * q₀.recenterConstant)) :=
          mul_le_mul_of_nonneg_left h2 hΛpos.le
      _ = 1 / 2 := by field_simp
  have hSlo : (2 * nom ^ 2)⁻¹ ≤ So := by
    rw [← hSodef, ← hnomdef]
    exact static_scale_ge_of_recenter_P6CD (records i' hTt) hδc b
  have hB1 : 1 ≤ 2 * nom ^ 2 * So := by
    have h := mul_le_mul_of_nonneg_left hSlo (by positivity : (0 : ℝ) ≤ 2 * nom ^ 2)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  -- a priori：nom < ρ(0)
  have hρ0 : 0 < q₀.neckRadius 0 := q₀.neckRadius_pos 0 le_rfl
  have hnρ0 : nom < q₀.neckRadius 0 := by
    have hs : nom < q₀.delta tio ^ 2 * q₀.neckRadius tio := by
      rw [← hnomdef, ← htio, ← hpδ, ← hpρ]
      exact (records i' hTt).nominal_small ⟨b.1.1⟩
    exact nom_lt_P6NC hs (q₀.delta_pos tio htio0) (q₀.delta_lt_one tio htio0)
      (q₀.neckRadius_pos tio htio0) (hρanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr htio0) htio0)
  -- 年龄 ⇒ c t − tio ≤ nom²；时间窗 [cσ/2, cσ]
  have hage_o : c * t - tio ≤ nom ^ 2 := age_le_P6NC hc hSo hnpos hw3' hSlo
  have ht34 : 3 / 4 * σ < t := (le_max_right _ _).trans_lt htI.1
  have hnn : nom ^ 2 ≤ q₀.neckRadius 0 ^ 2 := pow_le_pow_left₀ hnpos.le hnρ0.le 2
  have hcast : (H₀.rescale_P6N c hc).time i'.succ ≤ (H₀.rescale_P6N c hc).time j₀.castSucc :=
    (H₀.rescale_P6N c hc).time_strictMono.monotone hl
  have hcs : (H₀.rescale_P6N c hc).time j₀.castSucc < σ := by
    rw [hσ]
    exact (H₀.rescale_P6N c hc).time_strictMono (Fin.castSucc_lt_succ (i := j₀))
  have hτσ : tio / c ≤ σ := by
    rw [← htio]
    exact hcast.trans hcs.le
  obtain ⟨hlo', hhi'⟩ := window_P6NC hc hage_o hnn hk4 ht34 hτσ
  -- RecentCutoff + nominal identity ⇒ nom ≤ εr·ρ(cσ)
  have hσo0 : 0 ≤ c * σ := by linarith only [hk4, sq_nonneg (q₀.neckRadius 0)]
  obtain ⟨ρo, hρodef⟩ : ∃ r, q₀.neckRadius (c * σ) = r := ⟨_, rfl⟩
  have hρo : 0 < ρo := by
    rw [← hρodef]
    exact q₀.neckRadius_pos _ hσo0
  have hnomε : nom ≤ εr * ρo := by
    have h := hrc i' (by rw [htio]; exact ⟨hlo', hhi'⟩) ⟨b.1.1⟩
    rw [← hnomdef, ← hρodef, congrFun (hnomid i' hTt) ⟨b.1.1⟩]
    exact h
  obtain ⟨Q, hQdef⟩ : ∃ x, (ρo ^ 2)⁻¹ = x := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [← hQdef]
    positivity
  have hQS : Q ≤ 2 * εr ^ 2 * So := by
    rw [← hQdef]
    exact inv_sq_le_P6NC hnpos hSo hρo hB1 hnomε
  have hρoρ0 : ρo ≤ q₀.neckRadius 0 := by
    rw [← hρodef]
    exact hρanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hσo0) hσo0
  have hR2' : R ≤ c * Q := by
    rw [← hQdef, ← hρodef]
    exact hR2
  -- (CWS)：P6LL 于重标度 history
  have hsucc : H₀.time j₀.succ = c * σ := by
    rw [hσ]
    exact (mul_div_cancel₀ _ hc.ne').symm
  have hEo : H₀.EventSlabsDerivative C Q j₀.succ := by
    intro j hj y' t' ht' hR'
    refine hTD1 j y' t' ht' (lt_of_le_of_lt ?_ hR')
    have hjs : j.succ ≤ j₀.succ := Fin.castSucc_lt_iff_succ_le.mp hj
    have ht'σ : t' ≤ c * σ := by
      rw [← hsucc]
      exact ht'.2.le.trans (H₀.time_strictMono.monotone hjs)
    have ht'0 : 0 ≤ t' := (H₀.toHistory.time_nonneg j.castSucc).trans ht'.1.le
    have hρle : ρo ≤ q₀.neckRadius t' := by
      rw [← hρodef]
      exact hρanti (mem_Ici.mpr ht'0) (mem_Ici.mpr hσo0) ht'σ
    rw [← hQdef]
    exact inv_anti₀ (pow_pos hρo 2) (pow_le_pow_left₀ hρo.le hρle 2)
  have hEr := RetainedCoreHistory.eventSlabsDerivative_rescale_P6X3 H₀ hc hEo
  have hHIr := RetainedCoreHistory.hHI_rescale_P6X3 H₀ hc hHI
  have htk : (H₀.rescale_P6N c hc).time j₀.castSucc < t := (le_max_left _ _).trans_lt htI.1
  have hts : t < (H₀.rescale_P6N c hc).time j₀.succ := htI.2
  have hbirth : c * Q ≤ Cbirth * (((records i' hTt).rescale_P6M c hc).static b).neck.scale := by
    rw [hSS]
    have h3 := mul_le_mul_of_nonneg_right hεCb hSo.le
    have h4 := mul_le_mul_of_nonneg_left (hQS.trans h3) hc.le
    linarith only [h4]
  have haq : 1 ≤ a₀ / c * (((records i' hTt).rescale_P6M c hc).static b).neck.scale := by
    rw [hSS, ← mul_assoc, div_mul_cancel₀ _ hc.ne']
    have hQρ : Q * ρo ^ 2 = 1 := by
      rw [← hQdef]
      exact inv_mul_cancel₀ (by positivity)
    exact birthA_P6NC hQpos hρo hSo hQρ hρoρ0 hQS hεa
  have hmain := hLL3 (H₀.rescale_P6N c hc)
    (fun i'' hT'' =>
      (records i'' (hT₁a.trans ((div_le_div_iff_of_pos_right hc).mp hT''))).rescale_P6M c hc)
    (fun i'' hT'' b'' =>
      ((records i'' (hT₁a.trans ((div_le_div_iff_of_pos_right hc).mp hT''))).static
        b'').hasCanonicalWindow_rescale_P6M
        (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
          (hlink i'' _ b'')) c hc)
    hRw hm₀ hζw (fun j => (records₀ j).rescale_P6M c hc) δw
    (fun j hj => by
      have hTj : T₁ ≤ H₀.time j.succ := (div_le_div_iff_of_pos_right hc).mp hj
      calc (q₀.rescale_P6N c hc).delta (H₀.time j.succ / c) = q₀.delta (H₀.time j.succ) :=
            (q₀.rescale_P6N_eval c hc _).1
        _ ≤ δw := (hTδ _ hTj).trans (min_le_left _ _))
    le_rfl (c * Q) (a₀ / c) (1 / 2) (by positivity) le_rfl
    (fun x => (hHIr x).1) (fun x => (hHIr x).2)
    j₀.castSucc ((H₀.rescale_P6N c hc).time j₀.succ)
    (((H₀.rescale_P6N c hc).toHistory.event j₀).incoming)
    ((H₀.rescale_P6N c hc).event_initial j₀)
    (fun j hj => hEr j (hj.trans (Fin.castSucc_lt_succ (i := j₀)))) t htk hts
    ((((H₀.rescale_P6N c hc).toHistory.event j₀).incoming).derivativeBoundBefore_mono hts.le
      (hEr j₀ (Fin.castSucc_lt_succ (i := j₀))))
    i' hT hl p' Btr b w hw1 hw3 hxD hbirth haq
  have hS0 : 0 < c * So := by positivity
  have hage0 : 0 ≤ t - (H₀.rescale_P6N c hc).time i'.succ := by linarith only [hcast, htk]
  have hage1 : c * So * (t - (H₀.rescale_P6N c hc).time i'.succ) < 1 := by
    have h'' := mul_le_mul_of_nonneg_left hw3' hS0.le
    have e2 : (c * So) * (1 / 2 * (c * So)⁻¹) = 1 / 2 := by field_simp
    have e3 : (H₀.rescale_P6N c hc).time i'.succ = tio / c := by
      rw [← htio]
      rfl
    rw [e3]
    linarith only [h'', e2]
  have hcws : cc * (c * So) ≤
      (((H₀.rescale_P6N c hc).toHistory.event j₀).incoming).flow.scalar t p' :=
    scalar_ge_of_age_factor_P6SN hcc hS0 hage0 hage1 (by rw [← hSS]; exact hmain)
  exact final_P6NC hc hSo hcws ht2 hR2' hQS hεcc

/-- **G1 `hrecords_slot_P6NC`**（PROVED，0 binder）：结论 = HP6B2 v2 `hrecords` 槽逐字（sha `af630e70…`）；
records = SCRS⁺ NOMID S14（Dcap 之后选参数），late non-CWP 由 (CWS) + (SEP′) 本族孪生证出；绕过 FOOT5 G3b。 -/
theorem hrecords_slot_P6NC (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (Rrad ζ₀ B Dcap : ℝ), 0 < ζ₀ →
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
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (T₀ : ℝ)
          (records : ∀ i' : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time i'.succ →
            GeometricCutoffRecord (Kh k) i' pp),
          (∀ i' hT b, ((records i' hT).static b).hasCanonicalWindow) ∧
          Rrad ≤ pp.modelRadius ∧ 2 ≤ pp.modelOrder ∧ pp.modelAccuracy ≤ ζ₀ ∧
          T₀ ≤ (σ k : ℝ) - B / R k ∧
          ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
              (hT : T₀ ≤ (Kh k).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
              (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
              (b : ((Kh k).event i').RetainedBoundaryIndex)
              (w : standardCapWindow pp.modelRadius),
              Btr.point i'.succ le_rfl hl = ((records i' hT).static b).window w ∧
                ‖w.val‖ < Dcap + 1 ∧
                t - (Kh k).time i'.succ ≤ 1 / 2 * (((records i' hT).static b).neck.scale)⁻¹ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Rrad ζ₀ B Dcap hζ₀ ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  subst hε hC1 hC2 hCt
  obtain ⟨F₀, q₀, -, records₀, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, hρanti, hδlim⟩, ⟨-, hrecent, -, -⟩,
    -, -, -, -, hNOM⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, hTD⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6Ctime_C11G7B.{u} Γ)
  -- (SEP′) 的 ceiling 侧：σ 处 `R_k ≤ c_k · ρ(c_k σ_k)⁻²`（hsel 元组 = outerSupply 元组）
  have hceil : ∀ k, R k ≤ c k * (q₀.neckRadius (c k * σ k) ^ 2)⁻¹ := fun k => by
    have h := (Kh k).ceiling_of_not_good_P6SS (nr := (q₀.rescale_P6N (c k) (hc k)).neckRadius)
      ((F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcanS (ind k)))
      ((F.tower.history (ind k)).derivative_rescale_P6X (hc k)
        (fun v z hlo hhi hR =>
          GC.LongTime.Ch11.stageDerivative_of_timeDerivativeSupply_P6X hTD (ind k) v z hlo hhi hR))
      (hsel k)
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc k) q₀] at h
    rw [hRdef k]
    exact h
  -- (CWS) 常数：P6LL @ Θ = 1/2、C = p6Ctime Γ、D = |Dcap| + 1
  obtain ⟨cc, hcc, hLL⟩ :=
    RetainedCoreHistory.exists_scalar_lower_bound_of_cap_window_trace_late_P6LL.{u}
  obtain ⟨Cbirth, hCb, hLL2⟩ := hLL (1 / 2) (by norm_num) (by norm_num) (p6Ctime_C11G7B.{u} Γ)
  obtain ⟨Rw, -, m₀, -, ζw, δw, hζw, -, hδw, hLL3⟩ := hLL2 (|Dcap| + 1) (by positivity)
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨εr, hεr, hεCb, hεcc, hεa⟩ := exists_eps_P6NC hCb hcc ha₀
    (q₀.neckRadius_pos 0 le_rfl)
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp (hδlim.eventually (ge_mem_nhds
    (lt_min hδw (div_pos one_pos (by linarith [q₀.recenterConstant_ge_four] :
      (0 : ℝ) < 2 * q₀.recenterConstant)))))
  obtain ⟨Trc, -, hrc⟩ := hrecent εr hεr
  -- records：SCRS⁺ NOMID S14 @ (max Rrad Rw, min ζ₀ ζw, max 2 m₀)，带 nominal identity
  obtain ⟨Tthr, hTthr⟩ := hNOM (max Rrad Rw) (min ζ₀ ζw) (max 2 m₀) (lt_min hζ₀ hζw)
  choose p hpδ hpρ _hpf hprc hD hacc' hord' hrec using hTthr
  choose records hlink hid using hrec
  obtain ⟨T₁, hT₁a, hT₁b⟩ : ∃ x : ℝ, Tthr ≤ x ∧ Tδ ≤ x := ⟨max Tthr Tδ, le_max_left _ _,
    le_max_right _ _⟩
  have hlate : Tendsto (fun k => c k * (σ k : ℝ)) atTop atTop :=
    tendsto_late_P6NC hc hTc hclock h1 (fun k => Subtype.coe_le_coe.mpr (has k))
  have hBR : ∀ᶠ k in atTop, B / R k ≤ 1 / 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |B|)] with k hk
    rw [div_le_iff₀ (hRpos k)]
    have hR1 := hRr k
    linarith only [le_abs_self B, hR1, hk]
  filter_upwards [hlate.eventually_ge_atTop
    (max (2 * T₁) (max Trc (4 * q₀.neckRadius 0 ^ 2))), hBR] with k hk hkB
  have hσ1 : (1 : ℝ) ≤ σ k := (h1 k).trans (Subtype.coe_le_coe.mpr (has k))
  have hck := hc k
  have hk2 : 2 * T₁ ≤ c k * σ k := (le_max_left _ _).trans hk
  have hkrc : Trc ≤ c k * σ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hk4 : 4 * q₀.neckRadius 0 ^ 2 ≤ c k * σ k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have conv : ∀ i' : Fin (Kh k).eventCount, T₁ / c k ≤ (Kh k).time i'.succ →
      Tthr ≤ (F.tower.history (ind k)).time i'.succ := fun i' hT =>
    hT₁a.trans ((div_le_div_iff_of_pos_right hck).mp hT)
  refine ⟨(p (ind k)).rescale_P6N (c k) (hc k), T₁ / c k,
    fun i' hT => (records (ind k) i' (conv i' hT)).rescale_P6M (c k) (hc k),
    fun i' hT b => ?_, (le_max_left _ _).trans (hD (ind k)),
    (le_max_left _ _).trans (hord' (ind k)), (hacc' (ind k)).trans (min_le_left _ _),
    thr_le_P6NC hck hσ1 hk2 hkB, ?_⟩
  · exact ((records (ind k) i' (conv i' hT)).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
        (hlink (ind k) i' (conv i' hT) b)) (c k) (hc k)
  intro p' q' hq' hcr
  -- R(t, p′) → R_k（terminal 极限 + crossing 等距）
  have hσi : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hσact : (Kh k).activeStage (σ k) = (i k).succ := by
    refine le_antisymm ?_ ((Kh k).le_activeStage (σ k) (i k).succ (le_of_eq hσi.symm))
    by_contra hlt
    have h1' := (Kh k).time_strictMono (not_le.mp hlt)
    have h2' := (Kh k).activeStage_time_le (σ k)
    have h3' : ((σ k : Icc (0 : ℝ) (Kh k).horizon) : ℝ) = (σ k).1 := rfl
    linarith only [h1', h2', h3', hσi]
  have hiT : (Kh k).time (i k).succ ≤ (Tn k : ℝ) := by
    rw [← hσi]
    exact hsT k
  have h2i : (i k).succ ≤ (Kh k).activeStage (Tn k) := (Kh k).le_activeStage (Tn k) (i k).succ hiT
  have h1s : (Kh k).activeStage (aSeed k) ≤ (i k).succ := hσact ▸ (Kh k).activeStage_mono (has k)
  obtain ⟨-, hRσ, -⟩ := (Kh k).transport_at_stage_P6JW (haT k) (seedTrace k) (has k) (hsT k)
    hσact hσi (y k) q' hq' h1s h2i
  have hqR : metricScalarAt ((Kh k).event (i k)).outputMetric q' = R k := by
    rw [hRdef k, hRσ, (Kh k).stageMetric_succ_time_C11G (i k)]
  have hp : p' ∈ ((Kh k).event (i k)).incoming.terminalRegularOpen :=
    MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion _ hcr
  have hlim := ((Kh k).event (i k)).terminal.tendsto_metricScalarAt ⟨p', hp⟩
  rw [MetricCutCapEvent.RegularCrossing.scalar_eq _ (p := ⟨p', hp⟩) hcr, hqR] at hlim
  have hRk := hRpos k
  have hev1 : ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
      ((Kh k).event (i k)).incoming.flow.scalar t p' < 2 * R k :=
    hlim.eventually (gt_mem_nhds (by linarith only [hRk]))
  have hlo : max ((Kh k).time (i k).castSucc) (3 / 4 * (σ k : ℝ)) < (Kh k).time (i k).succ := by
    refine max_lt ((Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))) ?_
    rw [← hσi]
    linarith only [hσ1]
  filter_upwards [hev1, Ioo_mem_nhdsLT hlo] with t ht2 htI
  rintro ⟨i', hT, hl, Btr, b, w, hw1, hw2, hw3⟩
  exact nonCWP_point_P6NC (hc k) hLL3 hcc hεCb hεcc hεa (records (ind k)) (records₀ (ind k))
    (hpδ (ind k)) (hpρ (ind k)) (hprc (ind k)) (hlink (ind k))
    (fun i'' hi'' => (hid (ind k) i'' hi'').1)
    ((le_max_right _ _).trans (hD (ind k))) ((le_max_right _ _).trans (hord' (ind k)))
    ((hacc' (ind k)).trans (min_le_right _ _)) hT₁a (fun s hs => hTδ s (hT₁b.trans hs)) hρanti
    (hTD.1 (ind k)) (hHI (ind k)) hσi hk4
    (fun i'' hi'' h => hrc (c k * σ k) hkrc (ind k) i'' hi'' h) (hceil k) ht2 htI i' hT hl Btr b
    w hw1 (by linarith only [le_abs_self Dcap, hw2]) hw3

/-- consumer（G1 → HP6B2 v2）：`hrecords` 槽由 G1 付（0 binder，不经 FOOT5 G3b 的 `hnCWPslot`），
其余槽保持 binder，喂 `hP6bTwoLevelTime_of_slots_v2_P6HPB2`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := fun εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8 hgapJF hgapJF8 hmargin
      hpinch hderivL hgradL hdistLA hscaleSep hcollar =>
    hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8
      hgapJF hgapJF8 hmargin (hrecords_slot_P6NC P g εP6) hpinch hderivL hgradL hdistLA hscaleSep
      hcollar
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
