import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ClosedThresholdUL
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdUL
import DifferentialGeometry.Geometry.Collapse.GraphThresholdDisj

/-!
# The endpoint threshold `exists_graph_threshold_disj` at every universe (lane S-ULIFT, G4)

`GC.Endpoint.geometrization.{u}` consumes `exists_graph_threshold_disj.{u}`
(`LongTime/LateDecomposition.lean`, `components_geometrize_of_late_sequence_tests`), which the tree
builds from the two admitted inputs `exists_closed_graph_threshold_of_finite_scales_disj` and
`exists_boundary_graph_threshold`. Here the same combination is built from the proved inputs
`a02_closed_univ_UL` (closed, G2) and `a01_boundary_univ_UL` (boundary, G3), at every `u`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **`exists_graph_threshold_disj.{u}` without the two admitted inputs.** -/
theorem exists_graph_threshold_disj_univ_UL (K : ℕ) (hK : staticDerivativeOrder ≤ K)
    (A : ℝ → ℝ) (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_closed_disj
    (exists_closed_graph_threshold_disj_of_finite_scales_disj (a02_closed_univ_UL.{u} K hK A))
    (a01_boundary_univ_UL.{u} K hK A hA)

/-- The theorem has the type of `exists_graph_threshold_disj.{u}`, the input of the endpoint. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (exists_graph_threshold_disj_univ_UL.{u} K hK A hA :
    type_of% (exists_graph_threshold_disj.{u} K hK A hA))

end DifferentialGeometry.Geometry.Collapse
