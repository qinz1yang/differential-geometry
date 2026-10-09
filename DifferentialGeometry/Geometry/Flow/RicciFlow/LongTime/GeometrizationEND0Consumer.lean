import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.GeometrizationEND0
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Geometrization
import DifferentialGeometry.Geometry.Collapse.GraphThresholdDisj

/-!
# Consumer of `geometrization_zero_END0` (lane S-ENDPOINT0, G1)

Each `example` checks that an `_END0` theorem has exactly the type of the original at universe `0`
(`type_of%` of the original declaration instantiated at `0`), so that the `_END0` chain is a drop-in
replacement of the endpoint chain for `ConnectedClosedOrientedManifold.{0} 3`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff

/-- The static threshold: same type as `exists_graph_threshold_disj.{0}`. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (exists_graph_threshold_disj_END0 K hK A hA :
    type_of% (exists_graph_threshold_disj.{0} K hK A hA))

/-- The closed threshold (positivity hypothesis dropped): same conclusion as
`exists_closed_graph_threshold_disj.{0}`. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (exists_closed_graph_threshold_disj_END0 K hK A :
    type_of% (exists_closed_graph_threshold_disj.{0} K hK A hA))

/-- The endpoint: same type as `geometrization_certificate.{0}`. -/
example (M : ConnectedClosedOrientedManifold.{0} 3) :=
  (geometrization_zero_END0 M : type_of% (geometrization_certificate.{0} M))

/-- The conjecture at universe 0: same type as `geometrization_conjecture.{0}`. -/
example : type_of% geometrization_conjecture.{0} := geometrization_conjecture_zero_END0

/-- The smooth form at universe 0: same type as `smooth_geometrization_conjecture.{0}`. -/
example : type_of% smooth_geometrization_conjecture.{0} :=
  smooth_geometrization_conjecture_zero_END0

/-- The endpoint used as a function on a manifold of universe 0. -/
example (M : ConnectedClosedOrientedManifold.{0} 3) : Geometrizes M :=
  geometrization_conjecture_zero_END0 M
