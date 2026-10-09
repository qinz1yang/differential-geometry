import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransEventCXHT

/-!
# CX-HTRANS G2：`htrans` 槽逐字（history / tower 层，参数化常数，后缀 `_CXHT`）

* `htrans_history_CXHT`：`stage_localizedBad_trans_P6HB2` 里的单 history `htrans` 逐字；
* `htrans_of_transfers_CXHT`：`hbd_stage_late_P6HB2` 里的 tower 量化 `htrans`（`∀ nn cc hcc`）逐字。

两者仅多一个 binder `htube`（`comp(p')` 与 `(H.event i)` 的 cut tubes 不交；PROVISIONAL，owner =
STAB3/OPEN-C 的 cut-tube 数据），其余只有数值前提（`η₁ / C1₁ / C2₁ / C1f / C2f / m` 之间的不等式）。
D-15′ 赋值留给 `P6HtransD15CXHT`（需 ceiling v2 / SNAP root64）。
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

/-- **`htrans`（单 history 逐字）**。 -/
theorem htrans_history_CXHT (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} (hε : 0 < ε) (hη₁ : 0 < η₁)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (htube : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q → ∀ j,
      Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
        W.capTubeHasNeckChart ε) →
      ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
        ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁ :=
  fun p' q hc D hnot => MetricCutCapEvent.htrans_event_CXHT hc (htube p' q hc) D hε hη₁ hη hsmall
    hC1₁ hC2₁ hC1f hC2f hm hm' h1 h2 hnot

end ObservedHistory

/-- **`htrans`（tower 量化逐字）**：`hbd_stage_late_P6HB2` 的 `htrans` binder 的 producer。 -/
theorem htrans_of_transfers_CXHT {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hη₁ : 0 < η₁) (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (htube : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
          W.capTubeHasNeckChart ε) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁ :=
  fun nn cc hcc i =>
    ObservedHistory.htrans_history_CXHT _ i hε hη₁ hη hsmall hC1₁ hC2₁ hC1f hC2f hm hm' h1 h2
      (htube nn cc hcc i)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
