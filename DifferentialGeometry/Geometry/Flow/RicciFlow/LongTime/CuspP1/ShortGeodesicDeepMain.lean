import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepFinal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicClosedRange

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- **Deeper truncation, unconditional.** (`isClosed_range_cuspMap_CPA2` discharges the
properness hypothesis from the structure axioms.) -/
def deepenTruncationOf_CPA2 {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)
    {b : ℝ} (hb : 2 ≤ b) : HyperbolicTruncation H :=
  deepenTruncation_CPA2 T (isClosed_range_cuspMap_CPA2 T) hb

open GC.LongTime in
/-- **Deeper exterior, unconditional.** -/
def deepExteriorOf_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) : PersistentCuspExterior cores :=
  deepExterior_CPA2 E (fun i q => isClosed_range_cuspMap_CPA2 (E.truncation i) q) hb

open GC.LongTime in
/-- **`hshort`, geometric part, with no extra hypothesis.** For every persistent cusp exterior `E`
and every port `q` of the model `i` there are a depth `b ≥ 2`, a deeper exterior
`deepExteriorOf_CPA2 E hb` (starting no earlier than `E`; its truncations are
`deepenTruncationOf_CPA2 (E.truncation i) hb`) and an embedded smooth primitive closed geodesic of
the cusp torus of the port with speed `≤ L < 1`. -/
theorem exists_short_meridian_deepExteriorOf_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores) (i : Fin cores.count) (q : Fin (E.truncation i).count) :
    ∃ (b : ℝ) (hb : 2 ≤ b) (loop : freeLoop Torus),
      E.start ≤ (deepExteriorOf_CPA2 E hb).start ∧
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
        (((deepExteriorOf_CPA2 E hb).truncation i).cusp q).torusMetric (loopLift loop) ∧
      (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
      ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
        let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
        (((deepExteriorOf_CPA2 E hb).truncation i).cusp q).torusMetric.inner
          (loopLift loop s) v v ≤ L ^ 2 :=
  exists_short_meridian_deepExterior_CPA2 E
    (fun i q => isClosed_range_cuspMap_CPA2 (E.truncation i) q) i q

end GC.LongTime.CuspP1
