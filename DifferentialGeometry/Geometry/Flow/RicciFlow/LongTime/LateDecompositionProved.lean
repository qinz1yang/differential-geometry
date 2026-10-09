import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RouteWLateSequenceC11R

/-!
# Original late-decomposition API from proved producers

The original declarations keep their exact statements. This downstream module uses the proved
Route W, enhanced-profile and A12' implementations without creating an import cycle in the
upstream definitions in `LateDecomposition`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Endpoint Set
namespace GC.LongTime
universe u

theorem hasExteriorAreaObstructionAfter_of_producers
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) :=
  CuspP1.hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j hj C

theorem hasLateSequenceTests_of_thick_thin_and_obstruction
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K :=
  Ch11.hasLateSequenceTests_of_thick_thin_and_obstruction_C11R F K hK δ henh hdec

theorem exists_admissible_surgery_with_late_sequence_tests
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K :=
  Ch11.exists_admissible_surgery_with_late_sequence_tests_C11R
    exists_surgery_with_decaying_accuracy_enhanced P g K hK

theorem exists_surgery_with_late_sequence_tests
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ t : ℝ, 0 ≤ t → 0 < δ t ∧ δ t < 1) ∧
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasCommonNeckAccuracy F δ ∧ hasLateSequenceTests F K :=
  Ch11.exists_surgery_with_late_sequence_tests_C11R
    exists_surgery_with_decaying_accuracy_enhanced P g K hK

theorem geometrizes_of_metric
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric) :
    Geometrizes M :=
  Ch11.geometrizes_of_metric_C11R exists_surgery_with_decaying_accuracy_enhanced M g

end GC.LongTime
