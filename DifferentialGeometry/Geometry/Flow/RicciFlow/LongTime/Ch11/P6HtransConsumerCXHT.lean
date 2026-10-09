import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransHistoryCXHT

/-!
# CX-HTRANS G2 consumer：`stage_localizedBad_trans_P6HB2` 的 `htrans` 由 `htrans_history_CXHT` 付

`htrans` binder 换成数值前提 + `htube`，其余 binder 原样；`example` 的类型由推断给出
（= `LeftLocalizedBadAt_CXST …` 结论）。
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

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

example (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime : ℝ≥0}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2
        ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier)
    (hσ : (σ : ℝ) = H.time i.succ) (haσ : aSeed < σ) {L : ℝ}
    (hfoot : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (hε : 0 < ε) (hη₁ : 0 < η₁) (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (htube : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q → ∀ j,
      Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j)))
    (hcenK : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
        (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t)
            (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / (4 * Real.sqrt (metricScalarAt
              (H.stageMetric (H.activeStage σ) σ) y))))
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y) :=
  stage_localizedBad_trans_P6HB2 Rc hcapW haT seedTrace hsT has y hσ haσ hfoot
    (ObservedHistory.htrans_history_CXHT H i hε hη₁ hη hsmall hC1₁ hC2₁ hC1f hC2f hm hm' h1 h2
      htube) hcenK hsel

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
