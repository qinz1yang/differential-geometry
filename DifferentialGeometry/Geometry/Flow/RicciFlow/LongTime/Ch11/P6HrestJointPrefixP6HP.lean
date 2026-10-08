import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S

/-!
# hrestP 的 stage / horizon 支：HbdLate rev2 的 joint-prefix 形重述（O-CH11-HRESTP G1 / G2，后缀 `_P6HP`）

R-C11-10 D-4 + RERUN8B 槽级 BLOCKED 的 repair。冻结 `hrestP`（`canonicalLateCore_of_jointD_P6CK`）的第二支只说
"所有目标点无 spatial witness"，真正落在 stage 时刻 / 视界的子列要走 boundary closure：HbdLate rev2 的局部化 +
rerun，但 rerun 槽换成 RERUN8B 的 **prefix 形** `hrerunE8'` / `hrerunF8'`（提案文本
build-logs/scratch/O-CH11-RERUN8B/hrerun{E,F}8prime.txt 逐字，只把 binder 名里的 `′`（非合法标识符字符）写成 `'`）。
* `ceiling_of_bad_P6HP`：坏点 `¬∃ W η₁` + **`hcan₁`**（S5 `HistoryCanonicalSupply_C11S` 在坏点精度
  `(η₁, C1₁, C2₁)` 的实例）+ Antitone ⇒ `R' ≤ nr_q̃(Tn)⁻²`（`canonical_rescale_P6X` 逆否 +
  重标度 neck 半径 antitone）。
* `rerun_data_dist_P6HP`：`rerun_data_of_localized_ev_P6HB` 逐字 + 额外导出 rerun 点的种子距离
  `d(O(t), z) ≤ d(O(σ), y) + L/(4√R)`（原证明内部的 `hcen`）。
* `false_of_rerun_jointPrefix_P6HP`（泛型类 `Cls`）：在 rerun 点付 prefix 形槽的四项新欠——
  (1) ceiling：`hcan₁`（**PROVISIONAL**）；(2) `Qt < R'`：`R' → ∞` 抽子列
  （`extraction_forall_of_eventually`）；
  (3) footprint：取 `A' := A + 1`（seed-volume `(A+1)⁻¹ ≤ A⁻¹`），`L²/R ≤ 1/2` ⇒ `z ∈ B(A'+1)`，
  `(L''+1)/√R' ≤ 2` ⇒ `≤ A'+3`；(4) ∀k room：`L'' := min (L/2) √(R'(t − (Tn − 1/2)))`（hgood 对 L 单调，
  `L'' → ∞` 由 rerun 的 room）。`T₀ ≤ c·aSeed` 由 `Monotone T₀` 搬到子列。
* **G1 `hbd_stage_jointPrefix_P6HP`**：结论 = hrestP prefix 逐字 + stage 类（hstage 槽类前提逐字）⇒ False；
  binder `hcapWL hfoot htrans hcenE`（HbdLate rev2 逐字）+ 槽 `hrerunE8'` + `hcan₁` + `hanti` + `hT₀m`。
* **G2 `hbd_hor_jointPrefix_P6HP`**：同上 horizon 支（hhor 槽类前提逐字）；binder `hlocH` + 槽 `hrerunF8'`。
**PROVISIONAL**：`hcan₁`（repair target：surgery 在 `ηf = p6FineEta ε` 处构造，SCRS⁺ → HCS 的常数搬运，
owner P6OUTER / CX-OUTER2）；槽 `hrerunE8'` / `hrerunF8'` 由 G3（`P6HrestJointPrefixAssembleP6HP`）付。
陈述由 build-logs/scratch/O-CH11-HRESTP/g1.py 从源文件逐字抽取生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **rerun 点 ceiling**：坏点（无 `(η₁, C1₁, C2₁)` spatial witness）的曲率不超过重标度 neck 尺度
`nr_q̃(t)⁻²`（S5 逆否，`canonical_rescale_P6X`），再由 neck 半径 antitone 推到 `t ≤ Tn` 处的 `nr_q̃(Tn)⁻²`。 -/
theorem ceiling_of_bad_P6HP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {η₁ C1₁ C2₁ : ℝ}
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (n : ℕ) {c : ℝ} (hc : 0 < c)
    {t Tn : Icc (0 : ℝ) ((F.tower.history n).rescale_P6N c hc).toHistory.horizon} (htT : t ≤ Tn)
    (z : (((F.tower.history n).rescale_P6N c hc).toHistory.stageAt t).Carrier)
    (hbad : ¬ ∃ W : SpatialCanonicalWitness
      (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t) η₁ C1₁ C2₁ z,
      W.capTubeHasNeckChart η₁) :
    metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t) z ≤
      ((q.rescale_P6N c hc).neckRadius Tn ^ 2)⁻¹ := by
  have h1 : metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t) z ≤
      ((q.rescale_P6N c hc).neckRadius t ^ 2)⁻¹ := by
    by_contra hlt
    exact hbad (RetainedCoreHistory.canonical_rescale_P6X (F.tower.history n) hc (hcan₁ n) t z
      (lt_of_not_ge hlt))
  have hpos : 0 < (q.rescale_P6N c hc).neckRadius Tn :=
    (q.rescale_P6N c hc).neckRadius_pos _ Tn.2.1
  have hle : (q.rescale_P6N c hc).neckRadius Tn ≤ (q.rescale_P6N c hc).neckRadius t :=
    RetainedCoreHistory.neckRadius_rescale_antitone_P6X hc hanti t.2.1 Tn.2.1
      (Subtype.coe_le_coe.mpr htT)
  exact h1.trans (inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2))

/-- **重跑数据 + rerun 点种子距离**：`rerun_data_of_localized_ev_P6HB` 逐字，多导出一项：localized 坏点
`(t k, z k)` 的种子距离 `d(O(t), z) ≤ d(O(σ), y) + L/(4√R)`（原证明内部的 `hcen`，喂 footprint）。 -/
theorem rerun_data_dist_P6HP {Kh : ℕ → ObservedHistory.{u}} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {Bad : ∀ k (t : Icc (0 : ℝ) (Kh k).horizon), ((Kh k).stageAt t).Carrier → Prop}
    (Tn aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k)
    (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
    (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
      ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
    (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
    (R L : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k)
    (hRpos : ∀ k, 0 < R k) (hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k) (hL : Tendsto L atTop atTop)
    (hgood : ∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
      (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
      ∀ z : ((Kh k).stageAt v).Carrier,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
            ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
              ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k))
                ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / Real.sqrt (R k)) →
        4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
        (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k)
    (hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k)
    (hroom : Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop)
    (lo : ℕ → ℝ) (hlo : ∀ k, lo k < σ k)
    (hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ)) (Bad k)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, k ≤ φ k) ∧
    ∃ (t : ∀ k, Icc (0 : ℝ) (Kh (φ k)).horizon) (z : ∀ k, ((Kh (φ k)).stageAt (t k)).Carrier)
      (R' : ℕ → ℝ) (hsT' : ∀ k, t k ≤ Tn (φ k)) (has' : ∀ k, aSeed (φ k) ≤ t k),
      (∀ k, R' k =
        metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k)) (z k)) ∧
      (∀ k, lo (φ k) < t k ∧ (t k : ℝ) < σ (φ k)) ∧
      (∀ k, Bad (φ k) (t k) (z k)) ∧
      (∀ k, 0 < R' k) ∧ (∀ k : ℕ, (k : ℝ) + 1 < R' k) ∧
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh (φ k)).horizon) (hav : aSeed (φ k) ≤ v) (hvs : v ≤ t k),
        (t k : ℝ) - (L (φ k) / 2) ^ 2 / R' k ≤ (v : ℝ) →
        ∀ w : ((Kh (φ k)).stageAt v).Carrier,
          riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage v) v)
              ((seedTrace (φ k)).point ((Kh (φ k)).activeStage v)
                ((Kh (φ k)).activeStage_mono hav)
                ((Kh (φ k)).activeStage_mono (hvs.trans (hsT' k)))) w ≤
            riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k))
                ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (t k))
                  ((Kh (φ k)).activeStage_mono (has' k))
                  ((Kh (φ k)).activeStage_mono (hsT' k))) (z k) +
              ENNReal.ofReal (L (φ k) / 2 / Real.sqrt (R' k)) →
          8 * R' k ≤ metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage v) v) w →
          (Kh (φ k)).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v w) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed (φ k) : ℝ) ≤ t k - T / R' k) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop,
        (Tn (φ k) : ℝ) - 1 ^ 2 / 2 ≤ (t k : ℝ) - T / R' k) ∧
      Tendsto (fun k => R' k * ((t k : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun k => 1 / 200 * Real.sqrt (R' k)) atTop atTop ∧
      (∀ k, riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k))
          ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (t k))
            ((Kh (φ k)).activeStage_mono (has' k)) ((Kh (φ k)).activeStage_mono (hsT' k))) (z k) ≤
        riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k)))
            ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (σ (φ k)))
              ((Kh (φ k)).activeStage_mono (has (φ k)))
              ((Kh (φ k)).activeStage_mono (hsT (φ k)))) (y (φ k)) +
          ENNReal.ofReal (L (φ k) / (4 * Real.sqrt (R (φ k))))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((hwin 1 one_pos).and (hL.eventually_gt_atTop 0)).and hloc)
  let φ : ℕ → ℕ := fun k => 2 * (k + N) + 2
  have hφmono : StrictMono φ := fun a b hab => by
    change 2 * (a + N) + 2 < 2 * (b + N) + 2
    omega
  have hφk : ∀ k, k ≤ φ k := fun k => by
    change k ≤ 2 * (k + N) + 2
    omega
  have hφN : ∀ k, N ≤ φ k := fun k => by
    change N ≤ 2 * (k + N) + 2
    omega
  have hφt : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have haσ : ∀ k, aSeed (φ k) < σ (φ k) := fun k => by
    have h := (hN (φ k) (hφN k)).1.1
    have hr := hRpos (φ k)
    have : 0 < 1 / R (φ k) := by positivity
    exact Subtype.coe_lt_coe.mp (by linarith)
  have hLpos : ∀ k, 0 < L (φ k) := fun k => (hN (φ k) (hφN k)).1.2
  have ha : ∀ k, max (aSeed (φ k) : ℝ) (lo (φ k)) < σ (φ k) := fun k =>
    max_lt (Subtype.coe_lt_coe.mpr (haσ k)) (hlo (φ k))
  obtain ⟨t, z, hfact, hA, hρ⟩ := localized_left_bad_sequence_CXST
    (a := fun k => max (aSeed (φ k) : ℝ) (lo (φ k)))
    (fun k => (hN (φ k) (hφN k)).2 (haσ k) (hLpos k)) ha (fun k => hRpos (φ k)) hLpos
  have has' : ∀ k, aSeed (φ k) ≤ t k := fun k =>
    Subtype.coe_le_coe.mp ((le_max_left _ _).trans (hfact k).1.le)
  have hsT' : ∀ k, t k ≤ Tn (φ k) := fun k =>
    Subtype.coe_le_coe.mp ((hfact k).2.1.le.trans (Subtype.coe_le_coe.mpr (hsT (φ k))))
  let R' : ℕ → ℝ := fun k =>
    metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k)) (z k)
  have hhalf : ∀ k, R (φ k) / 2 ≤ R' k := fun k => (hfact k).2.2.2.1
  have hR'pos : ∀ k, 0 < R' k := fun k => by
    have := hRpos (φ k)
    have := hhalf k
    linarith
  have hR'r : ∀ k : ℕ, (k : ℝ) + 1 < R' k := fun k => by
    have hcast : ((φ k : ℕ) : ℝ) = 2 * ((k : ℝ) + N) + 2 := by
      change ((2 * (k + N) + 2 : ℕ) : ℝ) = _
      push_cast
      ring
    have := hRr (φ k)
    have := hhalf k
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hcen : ∀ k, riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k))
        ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (t k))
          ((Kh (φ k)).activeStage_mono (has' k)) ((Kh (φ k)).activeStage_mono (hsT' k))) (z k) ≤
        riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k)))
            ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (σ (φ k)))
              ((Kh (φ k)).activeStage_mono (has (φ k)))
              ((Kh (φ k)).activeStage_mono (hsT (φ k)))) (y (φ k)) +
          ENNReal.ofReal (L (φ k) / (4 * Real.sqrt (R (φ k)))) := fun k => by
    have hc := (hfact k).2.2.2.2.2
    split_ifs at hc with hh
    · exact hc
    · exact absurd ⟨has' k, hsT' k⟩ hh
  refine ⟨φ, hφmono, hφk, t, z, R', hsT', has', fun _ => rfl,
    fun k => ⟨(le_max_right _ _).trans_lt (hfact k).1, (hfact k).2.1⟩,
    fun k => (hfact k).2.2.1, hR'pos, hR'r, ?_, ?_, ?_, ?_, ?_, hcen⟩
  · intro k
    have hσσ : t k ≤ σ (φ k) := Subtype.coe_le_coe.mp (hfact k).2.1.le
    exact leftShift_rerun_P6S2 (haT (φ k)) (hsT (φ k)) (has (φ k)) hσσ (has' k)
      (seedTrace (φ k)) (y (φ k)) (z k) (hRpos (φ k)) (hhalf k) (hLpos k).le
      (hfact k).2.2.2.2.1 (hcen k) (hgood (φ k))
  · intro T hT
    filter_upwards [hφt.eventually (hwin (3 * T) (by positivity)), hA.eventually (gt_mem_nhds hT)]
      with k hk1 hk2
    have hr := hRpos (φ k)
    have hr' := hR'pos k
    have e1 : (σ (φ k) : ℝ) - t k < T / R (φ k) := by
      rw [lt_div_iff₀ hr]
      linarith
    have e2 : T / R' k ≤ 2 * T / R (φ k) := by
      rw [div_le_div_iff₀ hr' hr]
      nlinarith [hhalf k]
    have e3 : 3 * T / R (φ k) = T / R (φ k) + 2 * T / R (φ k) := by ring
    linarith
  · intro T hT
    filter_upwards [hφt.eventually (hwin' (3 * T) (by positivity)), hA.eventually (gt_mem_nhds hT)]
      with k hk1 hk2
    have hr := hRpos (φ k)
    have hr' := hR'pos k
    have e1 : (σ (φ k) : ℝ) - t k < T / R (φ k) := by
      rw [lt_div_iff₀ hr]
      linarith
    have e2 : T / R' k ≤ 2 * T / R (φ k) := by
      rw [div_le_div_iff₀ hr' hr]
      nlinarith [hhalf k]
    have e3 : 3 * T / R (φ k) = T / R (φ k) + 2 * T / R (φ k) := by ring
    linarith
  · have hB := hroom.comp hφt
    have hlow := tendsto_atTop_add_const_right atTop (-2) (hB.atTop_div_const two_pos)
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [hB.eventually_gt_atTop 0, hA.eventually (gt_mem_nhds one_pos),
      hρ.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with k hk1 hk2 hk3
    have hr := hRpos (φ k)
    simp only [comp_apply] at hk1 ⊢
    have hX : 0 ≤ (σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2) :=
      (pos_of_mul_pos_right hk1 hr.le).le
    have hst : 0 ≤ (σ (φ k) : ℝ) - t k := sub_nonneg.mpr (hfact k).2.1.le
    have hR'2 : R' k ≤ 2 * R (φ k) := by
      rw [div_lt_iff₀ hr] at hk3
      linarith
    have i1 := mul_le_mul_of_nonneg_right (hhalf k) hX
    have i2 := mul_le_mul_of_nonneg_right hR'2 hst
    have e1 : R' k * ((t k : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) =
        R' k * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) - R' k * ((σ (φ k) : ℝ) - t k) := by
      ring
    have e2 : R (φ k) * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) / 2 =
        R (φ k) / 2 * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) := by ring
    have e3 : 2 * R (φ k) * ((σ (φ k) : ℝ) - t k) = 2 * (R (φ k) * ((σ (φ k) : ℝ) - t k)) := by
      ring
    linarith
  · have hR'top : Tendsto R' atTop atTop := tendsto_atTop_mono (fun k => (hR'r k).le)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact Tendsto.const_mul_atTop (by norm_num) (Real.tendsto_sqrt_atTop.comp hR'top)

/-- **rerun 点付款（泛型类 `Cls`）**：hrestP 的 joint prefix 逐字 + 左端 `lo`（`lo < t < σ ⇒ Cls`）+ eventual
localized 坏点 ⇒ 在 rerun 点 `(t, z, R')`（子列 `φ ∘ ψ`）喂 prefix 形槽 `hslot`。新欠四项见文件头：
ceiling 由 `hcan₁`；`Qt < R'` 抽子列；footprint 取 `A' := A + 1`；∀k room 取 `L''`。 -/
theorem false_of_rerun_jointPrefix_P6HP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {T₀ Qt : ℕ → ℝ}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (Cls : ∀ H : ObservedHistory.{u}, Icc (0 : ℝ) H.horizon → Prop)
    (hslot :
      ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
      ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
        (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
        (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
          ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
      let c : ℕ → ℝ := fun k => r k ^ 2
      let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
      let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
      let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
      let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
      let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
        (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        (∀ k, Cls (Kh k) (σ k)) →
        (∀ k : ℕ, (k : ℝ) + 1 < R k) →
      False)
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hT₀m : Monotone T₀) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    ∀ lo : ℕ → ℝ, (∀ k, lo k < σ k) →
      (∀ k (s : Icc (0 : ℝ) (Kh k).horizon), lo k < (s : ℝ) → (s : ℝ) < σ k → Cls (Kh k) s) →
      (∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage t) t) η₁ C1₁ C2₁ z,
            W.capTubeHasNeckChart η₁)
          (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
          (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
              ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
                ((Kh k).activeStage_mono h.2)) z
            else 0)
          (σ k) (R k) (L k)
          (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k))) → False := by
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ lo hlo hcls hloc
  clear hQR hQρ hdistσ hsel
  obtain ⟨φ, hφ, hφk, t, z, R', hsT', has', hR'def, hlt, hbad, hR'pos, hR'r, hgood', hwin2, hwin3,
    hroom', hradii', hdist⟩ := rerun_data_dist_P6HP (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
      Tn aSeed haT pT seedTrace σ y R L hsT has hRpos hRr hL hgood hwin hwin' hroomT lo hlo hloc
  have hR'top : Tendsto R' atTop atTop := tendsto_atTop_mono (fun k => (hR'r k).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hev : ∀ n : ℕ, ∀ᶠ k in atTop,
      Qt n < R' k ∧ 0 < L (φ k) ∧ (Tn (φ k) : ℝ) - 1 ^ 2 / 2 < t k := by
    intro n
    filter_upwards [hR'top.eventually_gt_atTop (Qt n),
      (hL.comp hφ.tendsto_atTop).eventually_gt_atTop 0, hwin3 1 one_pos] with k k1 k2 k3
    have := hR'pos k
    have : 0 < 1 / R' k := by positivity
    exact ⟨k1, k2, by linarith⟩
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_forall_of_eventually hev
  have hψk : ∀ k, k ≤ ψ k := hψ.id_le
  have hφψ : ∀ k, k ≤ φ (ψ k) := fun k => (hψk k).trans (hφk (ψ k))
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have e12 : (1 : ℝ) ^ 2 / 2 = 1 / 2 := by norm_num
  let L'' : ℕ → ℝ := fun k => min (L (φ (ψ k)) / 2)
    (Real.sqrt (R' (ψ k) * ((t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2))))
  have hX : ∀ k, 0 < (t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2) := fun k => by
    have := (hψP k).2.2
    linarith
  have hXle : ∀ k, (t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2) ≤ 1 / 2 := fun k => by
    have h1' := (hlt (ψ k)).2
    have h2' : (σ (φ (ψ k)) : ℝ) ≤ Tn (φ (ψ k)) := hsT (φ (ψ k))
    linarith
  have hL''nn : ∀ k, 0 ≤ L'' k := fun k =>
    le_min (by have := (hψP k).2.1; linarith) (Real.sqrt_nonneg _)
  have hL''sq : ∀ k, L'' k ^ 2 ≤
      R' (ψ k) * ((t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2)) := fun k => by
    have h := pow_le_pow_left₀ (hL''nn k) (min_le_right _ _) 2
    rwa [Real.sq_sqrt (mul_nonneg (hR'pos (ψ k)).le (hX k).le)] at h
  have hball' : ∀ k, riemannianEDistOf ((Kh (φ (ψ k))).stageMetric
        ((Kh (φ (ψ k))).activeStage (t (ψ k))) (t (ψ k)))
      ((seedTrace (φ (ψ k))).point ((Kh (φ (ψ k))).activeStage (t (ψ k)))
        ((Kh (φ (ψ k))).activeStage_mono (has' (ψ k)))
        ((Kh (φ (ψ k))).activeStage_mono (hsT' (ψ k)))) (z (ψ k)) <
      ENNReal.ofReal ((A + 1 + 1) * 1) := fun k => by
    have hq : L (φ (ψ k)) / (4 * Real.sqrt (R (φ (ψ k)))) ≤ 1 := by
      have hR := hRpos (φ (ψ k))
      have hσT : (σ (φ (ψ k)) : ℝ) ≤ Tn (φ (ψ k)) := hsT (φ (ψ k))
      have hrm := hroom (φ (ψ k))
      have h2 : L (φ (ψ k)) ^ 2 / R (φ (ψ k)) ≤ 1 := by linarith
      have h3 : L (φ (ψ k)) ^ 2 ≤ R (φ (ψ k)) := by rwa [div_le_iff₀ hR, one_mul] at h2
      have h4 := Real.abs_le_sqrt h3
      have h5 := le_abs_self (L (φ (ψ k)))
      have hs := Real.sqrt_pos.mpr hR
      rw [div_le_one (by positivity)]
      linarith
    have hb : riemannianEDistOf ((Kh (φ (ψ k))).stageMetric
          ((Kh (φ (ψ k))).activeStage (σ (φ (ψ k)))) (σ (φ (ψ k))))
        ((seedTrace (φ (ψ k))).point ((Kh (φ (ψ k))).activeStage (σ (φ (ψ k))))
          ((Kh (φ (ψ k))).activeStage_mono (has (φ (ψ k))))
          ((Kh (φ (ψ k))).activeStage_mono (hsT (φ (ψ k))))) (y (φ (ψ k))) <
        ENNReal.ofReal ((A + 1) * 1) := hball (φ (ψ k))
    calc _ ≤ _ := hdist (ψ k)
      _ < ENNReal.ofReal ((A + 1) * 1) + ENNReal.ofReal 1 :=
        ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top hb (ENNReal.ofReal_le_ofReal hq)
      _ = ENNReal.ofReal ((A + 1 + 1) * 1) := by
        rw [← ENNReal.ofReal_add (by linarith) zero_le_one]
        congr 1
        ring
  refine hslot (A + 1) (by linarith) (fun k => ind (φ (ψ k))) (fun k => Tno (φ (ψ k)))
    (fun k => pTo (φ (ψ k))) (fun k => r (φ (ψ k))) (fun k => hr (φ (ψ k))) ?_
    (fun k => htime (φ (ψ k))) (fun k => hsmallo (φ (ψ k))) ?_ (fun k => aSeed (φ (ψ k)))
    (fun k => haT (φ (ψ k))) (fun k => hclock (φ (ψ k))) (fun k => h1 (φ (ψ k)))
    (fun k => hsm (φ (ψ k))) (fun k => (hT₀m (hφψ k)).trans (hT₀l (φ (ψ k))))
    (fun k => seedTrace (φ (ψ k))) (fun k => t (ψ k)) (fun k => z (ψ k)) (fun k => R' (ψ k))
    (fun k => hsT' (ψ k)) (fun k => has' (ψ k)) L'' (fun k => hR'def (ψ k))
    (fun k => hR'pos (ψ k)) ?_ (fun k => (hψP k).1) ?_ (fun k hg => hbad (ψ k) hg.1) ?_
    (fun T hT => hψt.eventually (hwin2 T hT)) (fun T hT => hψt.eventually (hwin3 T hT))
    (hroom'.comp hψt) (hradii'.comp hψt) ?_ ?_ hball' ?_
    (fun k => hcls (φ (ψ k)) (t (ψ k)) (hlt (ψ k)).1 (hlt (ψ k)).2) ?_
  · intro k
    have := hlate (φ (ψ k))
    have hk : (k : ℝ) ≤ (φ (ψ k) : ℝ) := by exact_mod_cast hφψ k
    linarith
  · intro k
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hvolo (φ (ψ k)))
    have hr3 := pow_pos (hr (φ (ψ k))) 3
    have hinv : (A + 1)⁻¹ ≤ A⁻¹ := inv_anti₀ (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right hinv hr3.le
  · intro k
    have := hR'r (ψ k)
    have hk : (k : ℝ) ≤ (ψ k : ℝ) := by exact_mod_cast hψk k
    linarith
  · have hA2 : Tendsto (fun k => L (φ (ψ k)) / 2) atTop atTop :=
      (hL.comp (hφ.comp hψ).tendsto_atTop).atTop_div_const two_pos
    have hB2 : Tendsto (fun k => Real.sqrt
        (R' (ψ k) * ((t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2)))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (hroom'.comp hψt)
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hA2.eventually_ge_atTop b, hB2.eventually_ge_atTop b] with k ha hb
    exact le_min ha hb
  · intro k v hav hvs hv w hw h8
    refine hgood' (ψ k) v hav hvs ?_ w ?_ h8
    · have hR := hR'pos (ψ k)
      have hsq : L'' k ^ 2 ≤ (L (φ (ψ k)) / 2) ^ 2 :=
        pow_le_pow_left₀ (hL''nn k) (min_le_left _ _) 2
      have : L'' k ^ 2 / R' (ψ k) ≤ (L (φ (ψ k)) / 2) ^ 2 / R' (ψ k) :=
        div_le_div_of_nonneg_right hsq hR.le
      linarith
    · refine hw.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
      exact div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  · intro k
    exact (hR'def (ψ k)).trans_le (ceiling_of_bad_P6HP hcan₁ hanti (ind (φ (ψ k)))
      (hc (φ (ψ k))) (hsT' (ψ k)) (z (ψ k)) (hbad (ψ k)))
  · intro k
    have hR := hR'pos (ψ k)
    have h1' : L'' k ^ 2 / R' (ψ k) ≤ (t (ψ k) : ℝ) - ((Tn (φ (ψ k)) : ℝ) - 1 ^ 2 / 2) := by
      rw [div_le_iff₀ hR]
      nlinarith [hL''sq k]
    linarith
  · refine Eventually.of_forall fun k => ?_
    have hR := hR'pos (ψ k)
    have hR1 : 1 ≤ R' (ψ k) := by
      have := hR'r (ψ k)
      have : (0 : ℝ) ≤ (ψ k : ℝ) := Nat.cast_nonneg _
      linarith
    have hs1 : 1 ≤ Real.sqrt (R' (ψ k)) := by
      have := Real.sqrt_le_sqrt hR1
      rwa [Real.sqrt_one] at this
    have hLs : L'' k ≤ Real.sqrt (R' (ψ k)) := by
      refine (min_le_right _ _).trans (Real.sqrt_le_sqrt ?_)
      have := hXle k
      nlinarith
    have hfoot2 : (L'' k + 1) / Real.sqrt (R' (ψ k)) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc _ ≤ ENNReal.ofReal ((A + 1 + 1) * 1) + ENNReal.ofReal 2 :=
          add_le_add (hball' k).le (ENNReal.ofReal_le_ofReal hfoot2)
      _ = ENNReal.ofReal ((A + 1 + 3) * 1) := by
        rw [← ENNReal.ofReal_add (by linarith) (by norm_num)]
        congr 1
        ring
  · intro k
    have := hR'r (ψ k)
    have hk : (k : ℝ) ≤ (ψ k : ℝ) := by exact_mod_cast hψk k
    linarith

/-- **G1：hrestP 的 stage 支（joint-prefix 形 hbd）**：结论 = hrestP prefix 逐字 + hstage 槽类前提逐字
`(∀ k, ∃ i, σ k = time i.succ) → False`。证明照 `hbd_stage_late_P6HB2` 重放（lateness、`hcapWL`/`hcenE`
局部化），rerun 点交 `false_of_rerun_jointPrefix_P6HP`（槽 `hrerunE8'`，类 = event 内部，左端
`time (i k).castSucc`）。 -/
theorem hbd_stage_jointPrefix_P6HP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {T₀ Qt : ℕ → ℝ}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    (hcapWL : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    (hfoot : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (htrans : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
          W.capTubeHasNeckChart ε) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁)
    (hcenE :
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) (Kh k).horizon) (z : ((Kh k).stageAt t).Carrier),
            (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed k ≤ t) (hvt : t ≤ Tn k),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
                ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k))))
    (hrerunE8' :
      ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
      ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
        (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
        (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
          ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
      let c : ℕ → ℝ := fun k => r k ^ 2
      let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
      let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
      let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
      let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
      let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
        (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
        (σ k : ℝ) < (Kh k).time j.succ) →
        (∀ k : ℕ, (k : ℝ) + 1 < R k) →
      False)
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hT₀m : Monotone T₀) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False := by
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hS
  choose i hi using hS
  have hTc : ∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ) := fun k => by
    have e : c k * (Tn k : ℝ) = Tno k := by
      change r k ^ 2 * ((Tno k : ℝ) / r k ^ 2) = Tno k
      field_simp [(hr k).ne']
    rw [e]
    exact hlate k
  have hlate' : Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_)
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        two_pos)
    have hck := hc k
    have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have hcl := hclock k
    have h1k := h1 k
    have hT := hTc k
    rw [← hi k]
    nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
      mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]
  have hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
        (fun t z => ¬ ∃ W : SpatialCanonicalWitness
          ((Kh k).stageMetric ((Kh k).activeStage t) t) η₁ C1₁ C2₁ z,
          W.capTubeHasNeckChart η₁)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k)) := by
    filter_upwards [hcapWL ind c hc i hlate', hcenE ind c hc Tn pT hTc aSeed haT hclock h1 hsm
      seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroomT hradii i hi]
      with k hW hE
    intro hak _
    choose pp Rc hW using hW
    rw [hRdef k] at hE ⊢
    exact Rc.stage_localizedBad_trans_P6HB2 hW (haT k) (seedTrace k) (hsT k) (has k) (y k)
      (hi k) hak
      (hfoot (ind k) (c k) (hc k) (i k) (σ k) (y k) (hi k) (hsel k))
      (htrans (ind k) (c k) (hc k) (i k)) hE (hsel k)
  have hlo : ∀ k, (Kh k).time (i k).castSucc < σ k := fun k => by
    rw [hi k]
    exact (Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))
  exact false_of_rerun_jointPrefix_P6HP
    (fun H s => ∃ j : Fin H.eventCount, H.time j.castSucc < (s : ℝ) ∧ (s : ℝ) < H.time j.succ)
    hrerunE8' hcan₁ hanti hT₀m A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock
    h1 hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT
    hradii hQρ hroom hball hdistσ
    (fun k => (Kh k).time (i k).castSucc) hlo
    (fun k s hs1 hs2 => ⟨i k, hs1, hs2.trans_eq (hi k)⟩) hloc

/-- **G2：hrestP 的 horizon 支（joint-prefix 形 hbd）**：结论 = hrestP prefix 逐字 + hhor 槽类前提逐字
`(∀ k, time last < horizon ∧ σ k = horizon) → False`。局部化由 `hlocH`（逐字），rerun 点交
`false_of_rerun_jointPrefix_P6HP`（槽 `hrerunF8'`，类 = final 内部，左端 `time last`）。 -/
theorem hbd_hor_jointPrefix_P6HP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {T₀ Qt : ℕ → ℝ}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    (hlocH : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            η₁ C1₁ C2₁ z, W.capTubeHasNeckChart η₁)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y))
    (hrerunF8' :
      ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
      ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
        (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
        (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
          ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
      let c : ℕ → ℝ := fun k => r k ^ 2
      let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
      let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
      let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
      let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
      let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
        (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
        (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k =
          metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
        (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
          (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((Kh k).stageAt v).Carrier,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / Real.sqrt (R k)) →
            8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
            (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
        (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
        (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
        (∀ᶠ k in atTop,
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) →
        (∀ k : ℕ, (k : ℝ) + 1 < R k) →
      False)
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hT₀m : Monotone T₀) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ 2
    let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
      Tendsto L atTop atTop →
      (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
      Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
      Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
      (σ k : ℝ) = (Kh k).horizon) → False := by
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hH
  have hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
        (fun t z => ¬ ∃ W : SpatialCanonicalWitness
          ((Kh k).stageMetric ((Kh k).activeStage t) t) η₁ C1₁ C2₁ z,
          W.capTubeHasNeckChart η₁)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k)) :=
    Eventually.of_forall fun k hak hLk => by
      rw [hRdef k]
      exact hlocH (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (σ k) (hsT k)
        (has k) (y k) (hH k).1 (hH k).2 hak (hRdef k ▸ hRpos k) (hsel k) (L k) hLk
  have hlo : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < σ k := fun k => by
    rw [(hH k).2]
    exact (hH k).1
  exact false_of_rerun_jointPrefix_P6HP
    (fun H s => H.time (Fin.last H.eventCount) < (s : ℝ) ∧ (s : ℝ) < H.horizon)
    hrerunF8' hcan₁ hanti hT₀m A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock
    h1 hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT
    hradii hQρ hroom hball hdistσ
    (fun k => (Kh k).time (Fin.last (Kh k).eventCount)) hlo
    (fun k s hs1 hs2 => ⟨hs1, hs2.trans_eq (hH k).2⟩) hloc

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
