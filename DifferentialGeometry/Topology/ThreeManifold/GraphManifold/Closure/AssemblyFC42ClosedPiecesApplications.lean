import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPieces

/-!
# Consumers of B1 and B2: FC42 steps 1 and 2 on the certificate

The FC42 dry stubs `dry_closedZero_aux` and `dry_slimCircle_data` were stated for a certificate
vertex. These consumers read the vertex off the certificate and apply B1 / B2:

* `DecompositionCertificate.boundary_eq_empty_and_exists_nonneg_of_closedZero`: a certificate with a
  closed zero vertex is on a closed carrier with an auxiliary smooth `sec ≥ 0` metric (the right
  disjunct of `exists_rawGraphPresentation_or_aux_nonneg_of_certificate`, V2 §4);
* `DecompositionCertificate.nonempty_rawGraphPresentation_of_slimCircle`: a certificate with a slim
  vertex over the circle gives a raw presentation (the left disjunct).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **FC42 step 1.** A closed zero vertex gives the right disjunct of FC42. -/
theorem boundary_eq_empty_and_exists_nonneg_of_closedZero [ConnectedSpace W.Carrier]
    (h : ∃ (k : Fin D.vertexCount) (C : ClosedZeroPiece W), D.vertex k = .closedZero C) :
    W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0 := by
  obtain ⟨-, C, -⟩ := h
  exact C.boundary_eq_empty_and_exists_nonneg

/-- **FC42 step 2.** A slim vertex over the circle gives a raw presentation of `W`. -/
theorem nonempty_rawGraphPresentation_of_slimCircle [ConnectedSpace W.Carrier]
    (h : ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨-, P, p, hp, hsub, fib, hcl, -⟩ := h
  exact exists_rawGraphPresentation_of_slimCircle P p hp hsub fib hcl

end DecompositionCertificate

end GC.GraphManifold.Assembly
