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

/-! The original contracts remain here to avoid an import cycle. Their proved public
implementations are in `LateDecompositionProved`, downstream of Route W. -/

/-- Original public contract, kept independent of downstream proved implementations. -/
def ExteriorAreaObstructionStatement : Prop :=
  ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier),
    hasAttainedExteriorAreaObstructionAfter F (L.decomposition j C)

/-- Original public contract, kept independent of downstream proved implementations. -/
def LateSequenceTestsFromEnhancedStatement : Prop :=
  ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε),
    hasLateSequenceTests F K

/-- Original public contract, kept independent of downstream proved implementations. -/
def AdmissibleLateSequenceExistenceStatement : Prop :=
  ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K),
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K

/-- Original public contract, kept independent of downstream proved implementations. -/
def SurgeryLateSequenceExistenceStatement : Prop :=
  ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K),
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ t : ℝ, 0 ≤ t → 0 < δ t ∧ δ t < 1) ∧
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasCommonNeckAccuracy F δ ∧ hasLateSequenceTests F K

/-- Original public contract, kept independent of downstream proved implementations. -/
def GeometrizationFromMetricStatement : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric),
    Geometrizes M

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

end GC.LongTime
