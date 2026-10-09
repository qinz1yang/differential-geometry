import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV5

/-!
# CP1-A3: Producer 1 assembly V6

V4 with `hloop := hloop_LTP4`, `hshort := hshort_CPA3`, `hpersist := hpersist_CPD8`: no remaining
inputs except the hypotheses of the original theorem.  The corollary keeps `hP2` only.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem exists_primitive_meridian_top_CPA3
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x)) :
    Nonempty (PrescribedCuspMeridianTop_CPQ L.cores) :=
  exists_primitive_meridian_top_CPH3 K hK δ hadm hdec L j hj C s x hcomp
    (hloop_LTP4 L j hj) (hshort_CPA3 L j hj) hpersist_CPD8

theorem exists_primitive_meridian_of_compressible_seam_via_top_CPA3
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hP2 : ∀ (M : PrescribedCuspMeridianTop_CPQ L.cores) (t : ℝ) (ht : M.exterior.start ≤ t),
      (∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        diskTrace u = M.transported t ht ∧ Set.range u ⊆ M.exterior.region t) →
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t ht) u) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  obtain ⟨M⟩ := exists_primitive_meridian_top_CPA3 K hK δ hadm hdec L j hj C s x hcomp
  exact ⟨M.toPrescribedCuspMeridian (hP2 M)⟩

end GC.LongTime.CuspP1
