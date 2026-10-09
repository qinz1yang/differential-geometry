import DifferentialGeometry.Geometry.Collapse.ThresholdDisjunctive
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateDecomposition

/-!
# Consumer of the V3 endpoint: late slices geometrize from the V3 static theorem

`GC.LongTime.components_geometrize_of_late_sequence_tests` (`LongTime/LateDecomposition.lean`)
consumes the Raw-form static theorem `exists_graph_threshold` and the Raw-form endpoint
`geometrizes_of_hyperbolicOrCollapsed`; both reach the admitted recognitions
`rawGraphPresentation_of_{sphericalSpaceForm, sphericalProduct, flat}` through
`exists_rawGraphPresentation_of_nonnegative`. The consumer here is the same proof with the static
theorem in V3 form as the explicit input and `geometrizes_of_hyperbolicOrCollapsed_disj` as the
endpoint; it is the shape the V3 patch installs in `LateDecomposition.lean`
(`build-logs/scratch/ASM-V3/threshold-v3.patch`). The derivative order hypothesis of the original
is only needed to produce the static theorem, so it is absent here.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

/-- Late regular slices geometrize componentwise, given the late sequence tests and the static
threshold theorem in V3 form (`Raw ∨ closed geometric`) at the derivative order `K`. -/
theorem components_geometrize_of_late_sequence_tests_of_static_disj
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (static : ∀ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
        ∀ (V : CompactCarrier.{u}) [ConnectedSpace V.Carrier]
          (h : SmoothRiemannianMetric V.model V.Carrier),
          staticCollapseHypotheses V h K A w₀ →
            Nonempty (RawGraphPresentation V) ∨
              (V.model.boundary V.Carrier = ∅ ∧
                ∃ G : GC.Geometry.GeometricStructure V.model V.Carrier,
                  G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean))
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
  obtain ⟨w₀, hw₀, hwupper, collapse⟩ := static A hA
  obtain ⟨N, hN⟩ := tests w₀ hw₀ hwupper
  apply hbad N
  intro C
  obtain ⟨D, ⟨pieces⟩, area⟩ := hN N le_rfl C
  apply geometrizes_of_hyperbolicOrCollapsed_disj _ ((slices N).componentMetric C)
    D K A w₀ collapse _ pieces
  exact hasExteriorAreaObstructionAfter_iff.mp area.toObstruction

end GC.LongTime
