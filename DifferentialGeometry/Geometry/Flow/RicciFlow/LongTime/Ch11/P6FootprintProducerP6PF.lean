import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FootprintP6ST3

/-!
# P-F surviving footprint：`hfoot` 的 producer 分解（O-CH11-HFOOT G1，后缀 `_P6PF`）

R-C11-10 D-11 / D-21：`hfoot`（`hbd_stage_late_P6HB2` 的显式前提，结论
`Nonempty (BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk)`）须同时覆盖 recovery 与 transfer
两种定量 footprint。
STAB3 已把合同的 `J`/`comparison`/`scalar_tendsto`/`gradient_tendsto`/`v` 全部生产，`footprint` 归约到 terminal
BCD（`nonempty_footprintData_of_scalarBound_P6ST3`）。本文件：
* **obstruction（PROVED）**：`SpatialCanonicalWitness.Q_pos` ⇒ `R ≤ 0` 处 `¬Good` 自动成立
  （`not_good_of_scalar_nonpos_P6PF`），而合同有 `Q_pos` 字段（`isEmpty_footprintData_of_scalar_nonpos_P6PF`）；
  故冻结 `hfoot` 槽 ⇒ 每个 rescaled tower event 的**每个** RegularCrossing 目标 `R⁺(q) > 0`
  （`scalar_pos_of_hfoot_P6PF`）——一般 `F` 不成立，冻结槽不可填（lead 18:5x 裁定收窄为 `hfootE`）。
* **recovery 桥（PROVED）**：`recoveryFootprint_of_footprintData_P6PF`——同一 `D` 在 `2C+1 ≤ c`
  （`c = 8C1 + 3((ηout/2)⁻¹+7)√C2`；推论 `_le_`：`C ≤ C1`、`ηout > 0`）时 eventually 给出 P-W(a)
  `exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen(_margins_P6ST4)` 的 `hball`
  `B̄_{Q_n·g(v_n)}(p, 2C+1) ⊆ D.U`。recovery footprint 不是独立义务，"同时受控" = 常数序 `C_rec ≤ C1f`。
* **reduction（PROVISIONAL）**：`footprintData_of_terminalBCD_P6PF`（单 history）；
  `hfoot_of_selection_P6PF`：结论 = `hfoot` 槽逐字，binder `hQF`（crossing 处 `R⁺ > 0`；obstruction 表明它对
  `hfoot` 必要，owner = lead 收窄裁定，已裁为 `hfootE`）+ `hBCDF`（record + terminal BCD，owner = 分析车道）。
* **`hfootE`（lead 裁定的收窄槽，文本 build-logs/scratch/O-CH11-HFOOT/hfootE.txt）**：
  `hfootE_of_hfoot_P6PF`（旧槽 ⇒ 新槽，平凡桥，PROVED）；`hfootE_of_terminalBCD_P6PF`（PROVISIONAL，
  唯一 binder `hBCDE`：selected family 上 eventual 的 record + terminal BCD；`Q_pos` 由 `hRpos` + `hRdef` +
  `scalar_eq_of_heq_P6PF` 免费）；`hBCDE_of_localBCD_P6PF`（PROVED 相对两条分析 binder）：`hBCDE` ⇐
  `hlocBCD`（incoming-slab terminal localized BCD：`∀ A, ∃ Q_A`，`R_ḡ ≤ Q_A·R_k` 于 `B_ḡ(p', A/√R_k)`）+
  `hscaleSep`（尺度分离：`Q_A·R_k < (1 − 4323δ_j)·scale_j`，`δ_j ≤ 1/2`）。
陈述由 build-logs/scratch/O-CH11-HFOOT/gen.py 从 `P6HbdLateP6HB2.lean`（hfoot 槽）与
`O-CH11-SFPFIX/hcenE.txt`（selected-family 前提）逐字生成。
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

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier} {ηout C1 C2 m : ℝ} {k : ℕ}

/-- **obstruction（event 层）**：`R⁺(q) ≤ 0` ⇒ footprint 合同为空（`Q_pos` 字段）。 -/
theorem isEmpty_footprintData_of_scalar_nonpos_P6PF
    (hle : metricScalarAt E.outputMetric q ≤ 0) :
    IsEmpty (E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k) :=
  ⟨fun D => absurd D.Q_pos (not_lt.mpr hle)⟩

/-- **recovery footprint ⇐ transfer footprint**：`D` 的 footprint 半径常数 `c ≥ 2C + 1` ⇒ eventually
`Q_n > 0` 且 P-W(a) 的 `hball`：`B̄_{Q_n·g(v_n)}(p, 2C+1) = B̄_{g(v_n)}(p, (2C+1)/√Q_n) ⊆ D.U`。 -/
theorem recoveryFootprint_of_footprintData_P6PF
    (D : E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k) {C : ℝ}
    (hC : 2 * C + 1 ≤ 8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) :
    ∀ᶠ n in atTop, ∃ hQn : 0 < metricScalarAt (E.incoming.flow.base.metric (D.v n)) p,
      riemannianClosedBallOf (I := I3)
        (DifferentialGeometry.scaleMetric (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p)
          hQn (E.incoming.flow.base.metric (D.v n))) p (2 * C + 1) ⊆ (D.U : Set P.Carrier) := by
  have hpos : ∀ᶠ n in atTop, 0 < metricScalarAt (E.incoming.flow.base.metric (D.v n)) p :=
    D.scalar_tendsto.eventually (lt_mem_nhds D.Q_pos)
  filter_upwards [hpos, D.footprint] with n hn hfp
  refine ⟨hn, ?_⟩
  have hs : 0 < Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p) :=
    Real.sqrt_pos.mpr hn
  have h := riemannianClosedBallOf_scaleMetric (I := I3) _ hn
    (E.incoming.flow.base.metric (D.v n)) p
    ((2 * C + 1) / Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p))
  have hmul : Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p) *
      ((2 * C + 1) / Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p)) =
      2 * C + 1 := by
    field_simp
  rw [hmul] at h
  rw [h]
  exact (riemannianClosedBallOf_mono _ p ((div_le_div_iff_of_pos_right hs).mpr hC)).trans hfp

/-- **recovery 桥（常数序版）**：`C ≤ C1`、`ηout > 0` ⇒ `2C + 1 ≤ c`，同上结论。 -/
theorem recoveryFootprint_of_footprintData_le_P6PF
    (D : E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k) {C : ℝ} (hη0 : 0 < ηout)
    (hC : C ≤ C1) :
    ∀ᶠ n in atTop, ∃ hQn : 0 < metricScalarAt (E.incoming.flow.base.metric (D.v n)) p,
      riemannianClosedBallOf (I := I3)
        (DifferentialGeometry.scaleMetric (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p)
          hQn (E.incoming.flow.base.metric (D.v n))) p (2 * C + 1) ⊆ (D.U : Set P.Carrier) := by
  have h1 : 0 < (ηout / 2)⁻¹ := inv_pos.mpr (by linarith)
  have h2 : 0 ≤ 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg C2)
  have h3 := D.one_le_C1
  exact recoveryFootprint_of_footprintData_P6PF D (by linarith)

end MetricCutCapEvent

namespace ObservedHistory

/-- 选点时刻 `σ = time i.succ`、`y ≍ q` ⇒ `R(σ, y) = R⁺(q)`。 -/
theorem scalar_eq_of_heq_P6PF (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {σ : Icc (0 : ℝ) H.horizon} (hσ : (σ : ℝ) = H.time i.succ) {y : (H.stageAt σ).Carrier}
    {q : (H.stage i.succ).Carrier} (hq : HEq y q) :
    metricScalarAt (H.stageMetric (H.activeStage σ) σ) y =
      metricScalarAt (H.event i).outputMetric q := by
  obtain rfl : σ = H.stageTime i.succ := Subtype.ext hσ
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  exact scalar_heq_P6ST2 hP hg hq

/-- **obstruction（history 层）**：`R(v, z) ≤ 0` ⇒ `¬ HasSpatialCanonicalTimeControl`
（witness 带 `Q_pos`）。 -/
theorem not_good_of_scalar_nonpos_P6PF (H : ObservedHistory.{u}) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (hle : metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ 0) :
    ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
  rintro ⟨⟨W, -⟩, -⟩
  exact absurd W.Q_pos (not_lt.mpr hle)

/-- **P-F reduction（单 history）**：crossing `p' ↦ q`、`Q₊ > 0`、record `Rc`（`δ_j ≤ 1/2`）、
`Lb` 低于 cut-neck 阈值、`R' > (17/16)c/√Q₊`、terminal BCD `R_ḡ ≤ Lb` 于 `B_ḡ(p', R')` ⇒
footprint 合同（STAB3 G3 单 binder 版）。 -/
theorem footprintData_of_terminalBCD_P6PF (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {ε C1f C2f m : ℝ} {kk : ℕ}
    (hε0 : 0 < ε) (hε : ε < 1 / 11) (hC1f : 1 ≤ C1f) (hC2f : 1 ≤ C2f) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hkk : max 2 ⌈ε⁻¹⌉₊ ≤ kk)
    {p' : (H.stage i.castSucc).Carrier} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p' q)
    (hQ : 0 < metricScalarAt (H.event i).outputMetric q)
    (hBCD : ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord H i pp) (Lb R' : ℝ),
      (∀ j, Rc.delta j ≤ 1 / 2) ∧ (∀ j, Lb < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale) ∧
      17 / 16 * ((8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f) /
        Real.sqrt (metricScalarAt (H.event i).outputMetric q)) < R' ∧
      ∀ z ∈ riemannianBallOf (H.event i).terminal.metric
          ⟨p', hcross.mem_terminalRegularRegion (H.event i)⟩ R',
        metricScalarAt (H.event i).terminal.metric z ≤ Lb) :
    Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) := by
  obtain ⟨pp, Rc, Lb, R', hδ, hsc, hR', hLb⟩ := hBCD
  exact Rc.nonempty_footprintData_of_scalarBound_P6ST3
    (p := ⟨p', hcross.mem_terminalRegularRegion (H.event i)⟩) hε0 hε hC1f hC2f hm0 hm1 hkk hδ hsc
    hcross hQ hR' hLb

/-- **obstruction（槽层，PROVED）**：冻结 `hfoot` 槽 ⇒ 每个 rescaled tower history 的每个 event 的每个
RegularCrossing 目标 `R⁺(q) > 0`（取 `σ := stageTime i.succ`、`y := cast q`；`R⁺(q) ≤ 0` 时 `¬Good` 自动成立而
合同要 `Q_pos`）。即 `hQF` 是 `hfoot` 的必要条件。 -/
theorem scalar_pos_of_hfoot_P6PF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hfoot :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk)) :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        0 < metricScalarAt (H.event i).outputMetric q := by
  intro nn cc hcc H i p' q hcross
  by_contra hneg
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  obtain ⟨y, hq⟩ : ∃ y : (H.stageAt (H.stageTime i.succ)).Carrier, HEq y q :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hP).symm q, cast_heq _ _⟩
  have hle : metricScalarAt (H.stageMetric (H.activeStage (H.stageTime i.succ))
      (H.stageTime i.succ)) y ≤ 0 :=
    (H.scalar_eq_of_heq_P6PF i rfl hq).trans_le (not_lt.mp hneg)
  obtain ⟨D⟩ := hfoot nn cc hcc i (H.stageTime i.succ) y rfl
    (H.not_good_of_scalar_nonpos_P6PF hle) p' q hq hcross
  exact hneg D.Q_pos

/-- **`hfoot` producer（槽层，PROVISIONAL）**：结论 = `hfoot` 槽逐字（`P6HbdLateP6HB2.lean` L170–176）。
binder：`hQF`（crossing 目标 `R⁺ > 0`；由 `scalar_pos_of_hfoot_P6PF` 它对 `hfoot` 必要；owner = lead 收窄裁定，
已裁为 `hfootE`）、`hBCDF`（record + terminal BCD，owner = 分析车道）；其余全部由 STAB3 生产。 -/
theorem hfoot_of_selection_P6PF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε0 : 0 < ε) (hε : ε < 1 / 11) (hC1f : 1 ≤ C1f) (hC2f : 1 ≤ C2f) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hkk : max 2 ⌈ε⁻¹⌉₊ ≤ kk)
    (hQF :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        0 < metricScalarAt (H.event i).outputMetric q)
    (hBCDF :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          ∀ hcross : (H.event i).RegularCrossing p' q,
          ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord H i pp) (Lb R' : ℝ),
            (∀ j, Rc.delta j ≤ 1 / 2) ∧
            (∀ j, Lb < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale) ∧
            17 / 16 * ((8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f) /
              Real.sqrt (metricScalarAt (H.event i).outputMetric q)) < R' ∧
            ∀ z ∈ riemannianBallOf (H.event i).terminal.metric
                ⟨p', hcross.mem_terminalRegularRegion (H.event i)⟩ R',
              metricScalarAt (H.event i).terminal.metric z ≤ Lb) :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) := by
  intro nn cc hcc H i σ y hσ hsel p' q hq hcross
  exact H.footprintData_of_terminalBCD_P6PF i hε0 hε hC1f hC2f hm0 hm1 hkk hcross
    (hQF nn cc hcc i p' q hcross) (hBCDF nn cc hcc i σ y hσ hsel p' q hq hcross)

/-- **桥（PROVED）**：旧 `hfoot` 槽 ⇒ lead 裁定的收窄槽 `hfootE`（hfootE.txt 逐字；selected family 上逐 `k`
实例化旧槽，`∀ᶠ k` 由 `Eventually.of_forall`）。 -/
theorem hfootE_of_hfoot_P6PF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hfoot :
      ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk)) :
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
          Nonempty (((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
    hL hsel hgood hwin hwin' hroom hradii i hi
  exact Eventually.of_forall fun k p' q hq hcross =>
    hfoot (ind k) (c k) (hc k) (i k) (σ k) (y k) (hi k) (hsel k) p' q hq hcross

/-- **`hfootE` producer（PROVISIONAL）**：结论 = `hfootE`（hfootE.txt 逐字）；唯一 binder `hBCDE`
（selected family 上 eventual：record `Rc`（`δ_j ≤ 1/2`）、`Lb` 低于 cut-neck 阈值、`R' > (17/16)c/√R_k`、
terminal BCD `R_ḡ ≤ Lb` 于 `B_ḡ(p', R')`）。`Q_pos` 免费：`R⁺(q) = R(σ_k, y_k) = R_k > 0`。 -/
theorem hfootE_of_terminalBCD_P6PF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε0 : 0 < ε) (hε : ε < 1 / 11) (hC1f : 1 ≤ C1f) (hC2f : 1 ≤ C2f) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hkk : max 2 ⌈ε⁻¹⌉₊ ≤ kk)
    (hBCDE :
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
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp) (Lb R' : ℝ),
            (∀ j, Rc.delta j ≤ 1 / 2) ∧
            (∀ j, Lb < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale) ∧
            17 / 16 * ((8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f) / Real.sqrt (R k)) < R' ∧
            ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
                ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ R',
              metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ Lb) :
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
          Nonempty (((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
    hL hsel hgood hwin hwin' hroom hradii i hi
  have hB := hBCDE ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  filter_upwards [hB] with k hk
  intro p' q hq hcross
  have hRq : R k = metricScalarAt ((Kh k).event (i k)).outputMetric q :=
    (hRdef k).trans ((Kh k).scalar_eq_of_heq_P6PF (i k) (hi k) hq)
  obtain ⟨pp, Rc, Lb, R', hδ, hsc, hR', hLb⟩ := hk p' q hq hcross
  rw [hRq] at hR'
  exact (Kh k).footprintData_of_terminalBCD_P6PF (i k) hε0 hε hC1f hC2f hm0 hm1 hkk hcross
    (lt_of_lt_of_eq (hRpos k) hRq) ⟨pp, Rc, Lb, R', hδ, hsc, hR', hLb⟩

/-- **`hBCDE` ⇐ 两条分析命题（PROVED 相对 binder）**：`hlocBCD`（incoming-slab terminal localized BCD，
`∀ A > 0, ∃ Q_A > 0`，selected family 上 eventually `R_ḡ ≤ Q_A·R_k` 于 `B_ḡ(p', A/√R_k)`）+ `hscaleSep`
（`∀ Q_A > 0`，eventually 有 record `Rc`，`δ_j ≤ 1/2` 且 `Q_A·R_k < (1 − 4323δ_j)·scale_j`）。取
`A := |17/16·c| + 1`、`Lb := Q_A·R_k`、`R' := A/√R_k`。 -/
theorem hBCDE_of_localBCD_P6PF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f : ℝ}
    (hlocBCD :
      ∀ A : ℝ, 0 < A → ∃ QA : ℝ, 0 < QA ∧
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
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
              ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ (A / Real.sqrt (R k)),
            metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ QA * R k)
    (hscaleSep :
      ∀ QA : ℝ, 0 < QA →
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
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale) :
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
          ∀ hcross : ((Kh k).event (i k)).RegularCrossing p' q,
          ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp) (Lb R' : ℝ),
            (∀ j, Rc.delta j ≤ 1 / 2) ∧
            (∀ j, Lb < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale) ∧
            17 / 16 * ((8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f) / Real.sqrt (R k)) < R' ∧
            ∀ z ∈ riemannianBallOf ((Kh k).event (i k)).terminal.metric
                ⟨p', hcross.mem_terminalRegularRegion ((Kh k).event (i k))⟩ R',
              metricScalarAt ((Kh k).event (i k)).terminal.metric z ≤ Lb := by
  obtain ⟨QA, hQA, hloc⟩ := hlocBCD
    (|17 / 16 * (8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f)| + 1) (by positivity)
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
    hL hsel hgood hwin hwin' hroom hradii i hi
  have hB := hloc ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hS := hscaleSep QA hQA ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  filter_upwards [hB, hS] with k hb hs
  intro p' q hq hcross
  obtain ⟨pp, Rc, hδ, hsc⟩ := hs
  have hsq : 0 < Real.sqrt (R k) := Real.sqrt_pos.mpr (hRpos k)
  refine ⟨pp, Rc, QA * R k,
    (|17 / 16 * (8 * C1f + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt C2f)| + 1) / Real.sqrt (R k),
    hδ, hsc, ?_, hb p' q hq hcross⟩
  rw [← mul_div_assoc]
  exact (div_lt_div_iff_of_pos_right hsq).mpr
    (lt_of_le_of_lt (le_abs_self _) (lt_add_one _))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
