import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Parameters
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskComparisons
import DifferentialGeometry.Analysis.ODE.AreaUpperBarrier

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

theorem exists_primitive_meridian_of_compressible_seam
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x)) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  sorry

theorem exists_attained_leastExteriorDiskArea
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) ∧
      ∀ t ∈ Ici T, 0 < exteriorDiskArea F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) t := by
  sorry

theorem local_disk_comparisons_of_cusp_exterior
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) →
      hasExteriorDiskComparisonsAfter F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) := by
  sorry

theorem exists_local_upper_barrier_of_exteriorDiskArea
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) →
      ∀ t ∈ Ici T,
        hasLocalSmoothUpperBarrier
          (exteriorDiskArea F.observation M.exterior.region T (M.loopAfter T (h₀.trans h))) (Ici T) t
          (3 * exteriorDiskArea F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) t /
            (4 * (t + H.scalarShift)) - Real.pi) := by
  sorry

end GC.LongTime
