import DifferentialGeometry.Geometry.Collapse.AssemblyBindingThresholds

/-!
# Consumer of the ASM-BIND combinatorial part: the V3 static threshold from the two bindings

`exists_graph_threshold_disj_of_bindings` composes the closed binding (`∀ R` form) and the boundary
binding at `(K, A)` with the FC42 consumer into the static threshold in V3 form — the statement of
`exists_graph_threshold_disj` (the patched public threshold consumed by `LateDecomposition.lean`) —
using `exists_closed_graph_threshold_of_finite_scales_disj_of_binding`,
`exists_boundary_graph_threshold_of_boundary_binding` and the V3 lemmas of `ThresholdDisjunctive.lean`.
When ASM-FC42 and the analytic bindings land, this is the replacement of the two admitted thresholds
on the public path; no further combinatorics is needed.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold GC.GraphManifold.Assembly
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse.Assembly

universe u

/-- The static threshold in V3 form from the closed and boundary bindings and the FC42 consumer;
one uniform `w₀` before all `(W, g)`. -/
theorem exists_graph_threshold_disj_of_bindings (K : ℕ) (A : ℝ → ℝ)
    (closedBinding : ∃ D : ClosedEarlyData, ∃ T : ClosedThresholds D,
      ∀ (R : ClosedRegister D T) (n : ℕ), max 2 R.later.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier),
          (∀ p, curvatureRadius g p ≠ ⊤) →
          closedCollapseHypotheses W g K A (closedCounterexampleRatio n) →
          Nonempty (ClosedDecompositionCertificate W))
    (boundaryBinding : ∃ D : BoundaryEarlyData, ∃ T : BoundaryThresholds D,
      ∀ (R : BoundaryRegister D T) (n : ℕ), max 2 R.tail ≤ n →
        ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
          (g : SmoothRiemannianMetric W.model W.Carrier)
          (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar n)),
          boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar n) →
          curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar n) →
          ∃ E : BoundaryTori W B.count,
            Nonempty (DecompositionCertificate W E) ∧
            ∀ i, Set.range (E.torusMap i) = B.component i)
    (consumer : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n}, DecompositionCertificate W E →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0)) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        staticCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            (W.model.boundary W.Carrier = ∅ ∧
              ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
                G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) :=
  exists_graph_threshold_disj_of_closed_disj
    (exists_closed_graph_threshold_disj_of_finite_scales_disj
      (exists_closed_graph_threshold_of_finite_scales_disj_of_binding K A closedBinding consumer))
    (exists_boundary_graph_threshold_of_boundary_binding K A boundaryBinding consumer)

end DifferentialGeometry.Geometry.Collapse.Assembly
