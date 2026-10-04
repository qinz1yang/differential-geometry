import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectionalCarrier

/-!
# Consumer of B0: the data of a closed zero piece

A piece `P : PieceFold W` with empty boundary is a closed manifold in disguise: with the orientation
pulled back from `W` it is a carrier (`PieceFold.toCarrier`), and B0
(`exists_closedModel_of_boundary_eq_empty`) gives the closed oriented model `Q` and the actual
diffeomorphism `P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier` — the `Q` and `ident` fields of the frozen record
`ClosedZeroPiece` (assembly design §0 decision 3, §4 row §1). With a `C²` metric of nonnegative
sectional curvature on the piece, LFR50 in carrier form
(`NonnegativeSectionalCarrier.lean:186`) and the pull-back along the diffeomorphism also give the
`metric` and `nonneg` fields: `PieceFold.exists_closedZeroData_of_metric2`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace PieceFold

variable {W : CompactCarrier.{u}} (P : PieceFold W)

/-- A piece as a carrier of kind `withBoundary`, oriented by the pull-back from `W`. -/
def toCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := P.Piece
  charts := P.charts
  smooth := P.manifold
  hausdorff := P.hausdorff
  compact := P.compact
  secondCountable := P.secondCountable
  orientation := P.pullbackOrientation

instance connectedSpace_toCarrier_ASMB0B1 : ConnectedSpace P.toCarrier.Carrier :=
  P.connected

/-- **B0 for a piece.** A piece with empty boundary has a closed oriented model `Q` and an
actual diffeomorphism onto it, orientation preserving for the pulled-back orientation. -/
theorem exists_closedModel_of_boundary_eq_empty (h : (𝓡∂ 3).boundary P.Piece = ∅) :
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3) (ident : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier),
      ident.preservesOrientation P.pullbackOrientation Q.orientation :=
  GC.GraphManifold.Assembly.exists_closedModel_of_boundary_eq_empty P.toCarrier h

/-- **The closed zero piece data.** A piece with empty boundary carrying a `C²` metric with
nonnegative sectional curvature has a closed oriented model `Q` with a smooth metric of
nonnegative sectional curvature and an actual oriented diffeomorphism `P.Piece ≃ Q`: the fields
`Q`, `metric`, `nonneg`, `ident` of the frozen record `ClosedZeroPiece`. -/
theorem exists_closedZeroData_of_metric2 (h : (𝓡∂ 3).boundary P.Piece = ∅)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡∂ 3) (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡∂ 3) : P.Piece → Type _))
    (hsec : ∀ x (v w : TangentSpace (𝓡∂ 3) x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3) (metric : SmoothRiemannianMetric (𝓡 3) Q.Carrier),
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow metric 0 ∧
      ∃ ident : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier,
        ident.preservesOrientation P.pullbackOrientation Q.orientation := by
  obtain ⟨Q, ident, hident⟩ := P.exists_closedModel_of_boundary_eq_empty h
  obtain ⟨g', hg'⟩ :=
    P.toCarrier.exists_smooth_sectional_nonneg_of_metric2_of_boundary_eq_empty h g hsec
  obtain ⟨metric, hmetric⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_sectionalBoundedBelow_of_diffeomorph
      ident.symm g' hg'
  exact ⟨Q, metric, hmetric, ident, hident⟩

end PieceFold

end GC.GraphManifold.Assembly
