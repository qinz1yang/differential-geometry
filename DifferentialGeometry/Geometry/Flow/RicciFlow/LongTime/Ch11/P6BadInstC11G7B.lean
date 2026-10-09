import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransHistoryCXHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HlocHProducerP6LH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB4

/-!
# htrans / hlocH 在两级坏点常数 `c(Γ)` 处的实例（O-CH11-GAPTOP7B G4a，后缀 `_C11G7B`）

R-C11-11 D-6 / Q4.4：`¬Good(η₁, c, c) ⇒ ¬Good(η₁, Cf, Cf)` 只给 rerun 槽的逆否适配；**htrans / hlocH 的坏性须在新常数
`c(Γ) = p6BadC_C11G2 Γ` 处重新生产**（旧 G4b 用 `Cf`，`P6HrestJointPrefixTopP6HP.lean` L747–755 / L803–832）。
* **`htrans_bad_C11G7B`**：CX-HTRANS G3 `htrans_D15_CXHT`（`P6HtransD15CXHT.lean` sha256
  08d2960bd9a4c323…）在 `C1₁ = C2₁ := c(Γ)` 处的重实例化：
  margin / footprint 参数 `C1f := max c 9 + √c`、`C2f := 1200 c`、`m := htransMBad_C11G7B Γ = min
  (1/20) (1/(10 c √c))`；
  数值前提 `2 C1f ≤ C1P6 std Γ`、`1000 C2f ≤ C2P6 std Γ` 由 G1 `hdomL_bad_C11G7B`（D-15″ 结构项）付；
  `13000 η₁ ≤ ηN`、`η₁ ≤ bJS` 由 CEIL3；唯一剩余 binder = `htube`（同 CX-HTRANS G3，PROVISIONAL）。
* **`hlocH_bad_C11G7B`**：HLOCH G2 `hlocH_ceiling_P6LH`（`P6HlocHD15P6LH.lean` sha256
  abd775dbfb2116f7…）的 `c(Γ)` 孪生——
  `hdomL` 由 G1 `hdomL_bad_C11G7B` 付，0 前提。
* consumer：`htrans_bad` 经 SFPFIX3 桥 `htransE_of_htrans_P6HB4` 填 HbdLate rev4 的 `htransE`（`c(Γ)` 处）。
陈述由 build-logs/scratch/O-CH11-GAPTOP7B/gen_g4.py 从上述两文件逐字抽取，只换常数。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow

universe u

/-- margin 参数 `m := min (1/20) (1/(10 c √c))`，`c := c(Γ)`。 -/
def htransMBad_C11G7B (Γ : ClosedBirthConstants) : ℝ :=
  min (1 / 20) (1 / (10 * p6BadC_C11G2.{u} Γ * Real.sqrt (p6BadC_C11G2.{u} Γ)))

theorem htransMBad_pos_C11G7B (Γ : ClosedBirthConstants) : 0 < htransMBad_C11G7B.{u} Γ := by
  have h1 := one_le_p6BadC_C11G7B.{u} Γ
  have hs : 0 < Real.sqrt (p6BadC_C11G2.{u} Γ) := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < 10 * p6BadC_C11G2.{u} Γ * Real.sqrt (p6BadC_C11G2.{u} Γ) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hs
  exact lt_min (by norm_num) (one_div_pos.mpr hc)

/-- **`htrans` 在 `c(Γ)` 处**（CX-HTRANS G3 重实例化）：见文件头。 -/
theorem htrans_bad_C11G7B (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {kk : ℕ}
    (htube : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q Γ.epsilon
          (max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ))
          (1200 * p6BadC_C11G2.{u} Γ) (htransMBad_C11G7B.{u} Γ) kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric Γ.epsilon
            (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
          W.capTubeHasNeckChart Γ.epsilon) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) (p6FineEta_C11GT6 Γ.epsilon)
          (p6BadC_C11G2.{u} Γ) (p6BadC_C11G2.{u} Γ) p',
          W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) :=
  htrans_of_transfers_CXHT (F := F) (kk := kk) Γ.epsilon_pos
    (p6FineEta_pos_C11GT6 Γ.epsilon_pos) (thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon)
    (fineEta_le_bJS_C11CL3 Γ.epsilon) (one_le_p6BadC_C11G7B.{u} Γ) (one_le_p6BadC_C11G7B.{u} Γ)
    le_rfl le_rfl (min_le_left _ _) (min_le_right _ _) (hdomL_bad_C11G7B.{u} Γ).1
    (by linarith [(hdomL_bad_C11G7B.{u} Γ).2]) htube

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

/-- **`hlocH` 在 `c(Γ)` 处**（HLOCH G2 孪生，0 前提）：见文件头。 -/
theorem hlocH_bad_C11G7B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (Γ : GC.GeneralFlow.ClosedBirthConstants) {Ctime : ℝ≥0} :
    let ε : ℝ := Γ.epsilon
    let C1 : ℝ := GC.LongTime.Ch11.C1P6_C11GT6.{u} GC.LongTime.Ch11.p6X1std_C11GT6.{u} Γ
    let C2 : ℝ := GC.LongTime.Ch11.C2P6_C11GT6.{u} GC.LongTime.Ch11.p6X2std_C11GT6.{u} Γ
    let ηf : ℝ := p6FineEta_C11GT6 ε
    let cb : ℝ := GC.LongTime.Ch11.p6BadC_C11G2.{u} Γ
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
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
            ηf cb cb z, W.capTubeHasNeckChart ηf)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y) := by
  intro ε C1 C2 ηf cb
  exact hlocH_of_transfers_P6LH (Ctime := Ctime) F (GC.LongTime.Ch11.epsilon_mem_C11GT6 Γ).1
    (GC.LongTime.Ch11.epsilon_mem_C11GT6 Γ).2 (GC.LongTime.Ch11.thirteenK_mul_fineEta_le_C11CL3 ε)
    (GC.LongTime.Ch11.fineEta_le_bJS_C11CL3 ε) (GC.LongTime.Ch11.hdomL_bad_C11G7B.{u} Γ).1
    (GC.LongTime.Ch11.hdomL_bad_C11G7B.{u} Γ).2

namespace ObservedHistory

/-- consumer：`htrans_bad_C11G7B` 经桥 `htransE_of_htrans_P6HB4` 填 rev4 `htransE`（`c(Γ)` 处；类型对齐）。 -/
example (Γ : GC.GeneralFlow.ClosedBirthConstants) {P : OrientedThreeStage.{0}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {kk : ℕ} {Ctime : ℝ≥0}
    (htube : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{0} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    True := by
  have _h := htransE_of_htrans_P6HB4 (F := F) (Ctime := Ctime) (ε := Γ.epsilon)
    (C1 := GC.LongTime.Ch11.C1P6_C11GT6.{0} GC.LongTime.Ch11.p6X1std_C11GT6.{0} Γ)
    (C2 := GC.LongTime.Ch11.C2P6_C11GT6.{0} GC.LongTime.Ch11.p6X2std_C11GT6.{0} Γ)
    (C1f := max (GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ) 9 +
      Real.sqrt (GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ))
    (C2f := 1200 * GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ)
    (m := GC.LongTime.Ch11.htransMBad_C11G7B.{0} Γ) (η₁ := p6FineEta_C11GT6 Γ.epsilon)
    (C1₁ := GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ) (C2₁ := GC.LongTime.Ch11.p6BadC_C11G2.{0} Γ)
    (kk := kk) (GC.LongTime.Ch11.htrans_bad_C11G7B.{0} Γ (F := F) (kk := kk) htube)
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
