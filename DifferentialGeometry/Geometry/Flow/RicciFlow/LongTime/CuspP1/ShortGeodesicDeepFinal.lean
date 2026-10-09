import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepCusp

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

open GC.LongTime in
/-- **`hshort` (geometric part).** For a persistent cusp exterior `E` whose cusp ranges are closed,
and any port `q` of the model `i`, there are a depth `b ≥ 2`, a deeper exterior
`deepExterior_CPA2 E hclosed hb` (starting no earlier than `E`) and an embedded smooth primitive
closed geodesic of the cusp torus of the port that has speed `≤ L < 1`: the `loop`, `embedded`,
`smooth`, `geodesic`, `primitive`, `short` fields of `PrescribedCuspMeridian`. -/
theorem exists_short_meridian_deepExterior_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores)
    (hclosed : ∀ i (q : Fin (E.truncation i).count), IsClosed (range ((E.truncation i).cuspMap q)))
    (i : Fin cores.count) (q : Fin (E.truncation i).count) :
    ∃ (b : ℝ) (hb : 2 ≤ b) (loop : freeLoop Torus),
      E.start ≤ (deepExterior_CPA2 E hclosed hb).start ∧
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
        (((deepExterior_CPA2 E hclosed hb).truncation i).cusp q).torusMetric (loopLift loop) ∧
      (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
      ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ s : ℝ,
        let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
        (((deepExterior_CPA2 E hclosed hb).truncation i).cusp q).torusMetric.inner
          (loopLift loop s) v v ≤ L ^ 2 := by
  obtain ⟨loop, hemb, hsm, hprim, b₀, hb₀⟩ := exists_meridian_deepCusp_CPA2 ((E.truncation i).cusp q)
  have hb : 2 ≤ max 2 b₀ := le_max_left _ _
  obtain ⟨hgeo, hshort⟩ := hb₀ (max 2 b₀) (le_max_right _ _)
  exact ⟨max 2 b₀, hb, loop, deepExterior_start_CPA2 E hclosed hb, hemb, hsm, hgeo, hprim, hshort⟩

end GC.LongTime.CuspP1
