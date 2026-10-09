import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceData

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

/-- Transport only the indices of the same selected prepared class. -/
private theorem distance_extension_of_same_prepared_class
    {pBase : CutoffParameters} {C : ClosedBirthConstants} {Cdist : ℝ≥0}
    {P Q : OrientedThreeStage.{u}} {g : P.Metric} {g' : Q.Metric} {B B' : ℝ}
    {K : ClosedBirthPreparedClass pBase C P g B}
    {K' : ClosedBirthPreparedClass pBase C Q g' B'}
    (hP : P = Q) (hg : HEq g g') (hB : B = B') (hK : HEq K K')
    (h : K.HasDistanceExtension Cdist) : K'.HasDistanceExtension Cdist := by
  cases hP
  cases (eq_of_heq hg)
  cases hB
  cases (eq_of_heq hK)
  exact h

/-- The original marked zero state, retaining its actual prepared callback. -/
theorem exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin
    (Cdist : ℝ≥0) (cMax : ℝ) (hcMax : 0 < cMax)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist) :
    ∃ S : PreparedSpatialState pBase C P g 0 1, S.DistanceData Cdist ∧
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.radius * Real.sqrt S.prepared.Qall ≤ 100 * cMax ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  obtain ⟨S, hS⟩ :=
    exists_prepared_spatial_base_with_small_test_margin cMax hcMax pBase C P g prepared hbase
  refine ⟨S, ?_, hS⟩
  rcases hS with ⟨hHistory, _, hStage, hMetric, hNative, _, _, hPrepared,
    hShift, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi : i.val < 0 := by simpa only [hHistory] using i.isLt
    exact (Nat.not_lt_zero i.val hi).elim
  · intro i
    have hi : i.val < 0 := by simpa only [hNative] using i.isLt
    exact (Nat.not_lt_zero i.val hi).elim
  · exact distance_extension_of_same_prepared_class hStage.symm hMetric.symm
      (by rw [hShift, sub_zero]) hPrepared.symm hprepared

/-- Retain the original distance API by forgetting only the additional margin. -/
theorem exists_prepared_spatial_base_with_distance_scalars
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (prepared : ClosedBirthPreparedClass pBase C P g 1)
    (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist) :
    ∃ S : PreparedSpatialState pBase C P g 0 1, S.DistanceData Cdist ∧
      S.history = RetainedCoreHistory.atZero P g ∧
      HEq S.initial (InitialIdentification.atZero P g) ∧
      S.nativeStage = P ∧ HEq S.nativeMetric g ∧
      S.native = RetainedCoreHistory.atZero P g ∧
      HEq S.nativeInitial (InitialIdentification.atZero P g) ∧
      S.nativeParameters = prepared.parameters ∧ HEq S.prepared prepared ∧
      S.shift = 0 ∧ S.offset = 0 ∧ S.radius ≤ 1 ∧
      S.parameters.delta = (fun _ => (1 : ℝ) / 2) ∧
      (∀ t : ℝ, S.parameters.neckRadius t = S.radius) := by
  obtain ⟨S, hDistance, hHistory, hInitial, hStage, hMetric, hNative, hNativeInitial,
    hParameters, hPrepared, hShift, hOffset, hRadius, _, hDelta, hNeck⟩ :=
    exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin
      Cdist 1 one_pos pBase C P g prepared hbase hprepared
  exact ⟨S, hDistance, hHistory, hInitial, hStage, hMetric, hNative, hNativeInitial,
    hParameters, hPrepared, hShift, hOffset, hRadius, hDelta, hNeck⟩

end GC.GeneralFlow
