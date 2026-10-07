import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Parameters
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspIncompressibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry
import DifferentialGeometry.Geometry.Collapse.GraphThresholdDisjUL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12Enhanced
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A09OfEnhancedC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A13OfEnhancedC11M

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.MinimalSurface
open GC.Endpoint GC.GraphManifold Set
open GC.Topology
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

def hasExteriorAreaObstructionAfter {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) : Prop :=
  ∀ i : Fin D.boundary.count, ∀ x : GC.Endpoint.Torus,
    ¬ Function.Injective
      (FundamentalGroup.map (D.reconstructionAtlas.torusInPrime D.reconstruction i) x) →
    ∃ (T c : ℝ) (W : (t : ℝ) → Set (postStage F.observation t).Carrier)
      (γ : (t : ℝ) → T ≤ t → freeLoop (postStage F.observation t).Carrier),
      0 ≤ T ∧ 0 < c ∧
      ContinuousOn (exteriorDiskArea F.observation W T γ) (Ici T) ∧
      ∀ t ∈ Ici T,
        hasLocalSmoothUpperBarrier (exteriorDiskArea F.observation W T γ) (Ici T) t
          (3 * exteriorDiskArea F.observation W T γ t / (4 * (t + c)) - Real.pi)

def hasAttainedExteriorAreaObstructionAfter {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) : Prop :=
  ∀ i : Fin D.boundary.count, ∀ x : GC.Endpoint.Torus,
    ¬ Function.Injective
      (FundamentalGroup.map (D.reconstructionAtlas.torusInPrime D.reconstruction i) x) →
    ∃ (T c : ℝ) (W : (t : ℝ) → Set (postStage F.observation t).Carrier)
      (γ : (t : ℝ) → T ≤ t → freeLoop (postStage F.observation t).Carrier),
      0 ≤ T ∧ 0 < c ∧
      hasExteriorDiskMinimizersAfter F.observation W T γ ∧
      ContinuousOn (exteriorDiskArea F.observation W T γ) (Ici T) ∧
      ∀ t ∈ Ici T,
        hasLocalSmoothUpperBarrier (exteriorDiskArea F.observation W T γ) (Ici T) t
          (3 * exteriorDiskArea F.observation W T γ t / (4 * (t + c)) - Real.pi)

theorem hasAttainedExteriorAreaObstructionAfter.toObstruction
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {M : ConnectedClosedOrientedManifold.{u} 3}
    {D : TorusDecomposition M} (h : hasAttainedExteriorAreaObstructionAfter F D) :
    hasExteriorAreaObstructionAfter F D := by
  intro i x hi
  obtain ⟨T, c, W, γ, hT, hc, _, hcont, hb⟩ := h i x hi
  exact ⟨T, c, W, γ, hT, hc, hcont, hb⟩

theorem hasExteriorAreaObstructionAfter_iff
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {M : ConnectedClosedOrientedManifold.{u} 3}
    {D : TorusDecomposition M} :
    hasExteriorAreaObstructionAfter F D ↔ D.reconstructionAtlas.Incompressible D.reconstruction := by
  constructor
  · intro h
    apply GC.LongTime.incompressible_of_shifted_area_barriers
    intro i x hi
    obtain ⟨T, c, W, γ, hT, hc, hcont, hb⟩ := h i x hi
    exact ⟨T, c, exteriorDiskArea F.observation W T γ, hT, hc, hcont,
      fun t _ => exteriorDiskArea_nonneg F.observation W T γ t, hb⟩
  · intro h i x hi
    exact False.elim (hi (h i x))

def hasLateSequenceTests {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) : Prop :=
  ∀ slices : ℕ → RegularSlice F.observation,
    (∀ j : ℕ, (j : ℝ) < (slices j).time) →
    (∀ j : ℕ, Nonempty (slices j).stage.Carrier) →
    ∃ A : ℝ → ℝ,
      (∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) ∧
      ∀ w₀ : ℝ, 0 < w₀ → w₀ < euclideanThreeUnitBallVolume →
        ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
          ∀ C : ConnectedComponents (slices j).stage.Carrier,
            ∃ D : TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C),
              Nonempty ((i : Fin D.components.count) →
                HyperbolicOrCollapsed ((slices j).componentMetric C) D K A w₀ i) ∧
              hasAttainedExteriorAreaObstructionAfter F D

theorem hasExteriorAreaObstructionAfter_of_producers
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier) :
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C) := by
  intro s x hcomp
  obtain ⟨M⟩ := exists_primitive_meridian_of_compressible_seam K hK δ hadm hdec L j hj C s x hcomp
  obtain ⟨H⟩ := hadm
  obtain ⟨Tm, hm, hmin⟩ := exists_attained_leastExteriorDiskArea K hK δ ⟨H⟩ hdec M
  obtain ⟨Tc, hc, hcomparison⟩ := local_disk_comparisons_of_cusp_exterior K hK δ ⟨H⟩ hdec M
  obtain ⟨Tb, hb, hbarrier⟩ := exists_local_upper_barrier_of_exteriorDiskArea K hK δ H hdec M
  let T := max Tm (max Tc Tb)
  have hTm : Tm ≤ T := le_max_left _ _
  have hTc : Tc ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTb : Tb ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hstart : M.exterior.start ≤ T := hm.trans hTm
  let γ := M.loopAfter T hstart
  have hmin' : hasExteriorDiskMinimizersAfter F.observation M.exterior.region T γ := (hmin T hTm).1
  refine ⟨T, H.scalarShift, M.exterior.region, γ,
    (L.cores.start_pos.le.trans M.exterior.after_cores).trans hstart, H.scalarShift_pos, hmin', ?_, ?_⟩
  · exact continuousOn_exteriorDiskArea_of_local_comparisons _ _ _ _ hmin'
      (hcomparison T hTc hmin')
  · exact hbarrier T hTb hmin'

theorem hasLateSequenceTests_of_thick_thin_and_obstruction
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := Ch11.hasAnalyticAdmissibility_of_full_C11F henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := Ch11.exists_late_cut_family_of_enhanced_C11M F K hK δ henh hdec slices htimes
    hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (Ch11.late_derivative_tests_of_flow_of_enhanced_C11M F K hK δ henh hdec slices htimes
      hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    hasExteriorAreaObstructionAfter_of_producers K hK δ hadm hdec L j ((le_max_right _ _).trans hj) C⟩

theorem exists_admissible_surgery_with_late_sequence_tests
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile⟩ := exists_surgery_with_decaying_accuracy_enhanced P g
  exact ⟨δ, F, ha, hd, Ch11.hasAnalyticAdmissibility_of_full_C11F hprofile,
    hasLateSequenceTests_of_thick_thin_and_obstruction F K hK δ hprofile hd⟩

theorem exists_surgery_with_late_sequence_tests
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ t : ℝ, 0 ≤ t → 0 < δ t ∧ δ t < 1) ∧
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasCommonNeckAccuracy F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, ⟨H⟩, ht⟩ := exists_admissible_surgery_with_late_sequence_tests P g K hK
  exact ⟨δ, F, H.commonNeckAccuracy.bounds, ha, hd, H.commonNeckAccuracy, ht⟩

theorem components_geometrize_of_late_sequence_tests
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (hregions : hasLateSequenceTests F K) :
    ∃ B : ℝ, ∀ s : RegularSlice F.observation,
      B < s.time → Nonempty s.stage.Carrier →
        ComponentsGeometrize s.stage.toClosedOrientedManifold := by
  classical
  by_contra h
  push Not at h
  have bad : ∀ j : ℕ, ∃ s : RegularSlice F.observation,
      (j : ℝ) < s.time ∧ Nonempty s.stage.Carrier ∧
        ¬ ComponentsGeometrize s.stage.toClosedOrientedManifold := fun j => h (j : ℝ)
  choose slices htimes hnonempty hbad using bad
  obtain ⟨A, hA, tests⟩ := hregions slices htimes hnonempty
  obtain ⟨w₀, hw₀, hwupper, collapse⟩ := exists_graph_threshold_disj_univ_UL K hK A hA
  obtain ⟨N, hN⟩ := tests w₀ hw₀ hwupper
  apply hbad N
  intro C
  obtain ⟨D, ⟨pieces⟩, area⟩ := hN N le_rfl C
  apply geometrizes_of_hyperbolicOrCollapsed_disj _ ((slices N).componentMetric C)
    D K A w₀ collapse _ pieces
  exact hasExteriorAreaObstructionAfter_iff.mp area.toObstruction

theorem geometrizes_of_metric
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric) :
    Geometrizes M := by
  obtain ⟨δ, F, _, _, _, _, tests⟩ := exists_surgery_with_late_sequence_tests
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g lateDerivativeOrder le_rfl
  exact geometrizes_of_late_slice_supply M F
    (components_geometrize_of_late_sequence_tests F lateDerivativeOrder staticDerivativeOrder_le_lateDerivativeOrder tests)

end GC.LongTime
