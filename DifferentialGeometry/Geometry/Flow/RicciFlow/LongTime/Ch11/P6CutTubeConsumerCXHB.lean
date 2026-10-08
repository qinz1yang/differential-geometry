import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransHistoryCXHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CutTubeObstructionCXHB

/-!
# CX-HTUBE G1 consumer：`htrans_of_transfers_CXHT` 的 `htube` binder（tower 形）（`_CXHB`）

* `htube_tower_refuted_CXHB`：tower 里只要有一个 event 带 `GeometricCutoffRecord`、有切口、
  且 protected 点是 regular crossing（桥 `hPC`），`htrans_of_transfers_CXHT` 的 `htube` binder 就为假。
* `htrans_of_transfers_noCut_CXHB`：唯一能把 `htube` 喂给 `htrans_of_transfers_CXHT` 的情形——tower 中
  全部 event 无切口（`IsEmpty tubes.Index`）；输出是不带 `htube` 的 `htrans` 逐字。
这两条一起说明：`htube` 不是 record 数据能付的 binder（BLOCKED，repair target 见 DELIVERIES）。
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

/-- **tower 形 `htube` 被 record 反驳**（只要某个 rescaled history 的某个 event 真的切了 neck）。 -/
theorem htube_tower_refuted_CXHB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (nn : ℕ) (cc : ℝ) (hcc : 0 < cc) {H : ObservedHistory.{u}}
    (hH : ((F.tower.history nn).rescale_P6N cc hcc).toHistory = H) (i : Fin H.eventCount)
    {pp : CutoffParameters} (Rc : GeometricCutoffRecord H i pp)
    (hcut : Nonempty (H.event i).transition.trace.tubes.Index)
    (hPC : ∀ x : (H.event i).incoming.terminalRegularOpen,
      x.1 ∈ (H.event i).transition.trace.tubes.core →
      metricScalarAt (H.event i).terminal.metric x ≤
        ((pp.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      x.1 ∈ interior (Subtype.val '' (H.event i).transition.trace.retainedCore) →
      ∃ q, (H.event i).RegularCrossing x.1 q) :
    ¬ (∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p')
          (Set.range ((H.event i).transition.trace.tubes.tube j))) := by
  intro htube
  subst hH
  obtain ⟨α⟩ := hcut
  exact ((Rc.cutTubeDisjoint_iff_noCut_CXHB hPC).mp (htube nn cc hcc i)).false α

/-- **唯一可喂的情形**：全部 event 无切口 ⇒ `htrans_of_transfers_CXHT` 无 `htube` 地给出 `htrans`。 -/
theorem htrans_of_transfers_noCut_CXHB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hη₁ : 0 < η₁) (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (hnoCut : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ i : Fin H.eventCount, IsEmpty (H.event i).transition.trace.tubes.Index) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
          W.capTubeHasNeckChart ε) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁ :=
  htrans_of_transfers_CXHT (F := F) hε hη₁ hη hsmall hC1₁ hC2₁ hC1f hC2f hm hm' h1 h2
    (fun nn cc hcc i _ _ _ j => ((hnoCut nn cc hcc i).false j).elim)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
