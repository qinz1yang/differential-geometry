import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateFaces

/-!
# Consumers of B13 and B8 on the certificate

* `Vertex.rawPiece_of_torusFaced`: every torus-faced vertex model of the FC39 certificate (solid
  torus, twisted `I`-bundle, `T² × I` slim piece, cusp core) is in the `hpiece` format of B3's
  `exists_rawGraphPresentation_of_regularCutData` (B13 for the two product models).
* `DecompositionCertificate.orient_endDisk_subset_face`, `…orient_range_eq`: a certificate handle
  run in either direction (B8) keeps its end disks in the right faces and its image — the facts the
  cycle construction of FC42 needs after the degree-two decomposition, whose edges are unordered.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The torus-faced vertex models of the certificate give raw pieces in the format of B3. -/
theorem Vertex.rawPiece_of_torusFaced {W : CompactCarrier.{u}} (v : Vertex W)
    (hv : (∃ P e, v = .zero P (.solidTorus e)) ∨ (∃ P e, v = .zero P (.twistedIBundle e)) ∨
      (∃ P e, v = .slim P (.torusInterval e)) ∨ (∃ P e, v = .cuspCore P e)) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) := by
  rcases hv with ⟨P, e, rfl⟩ | ⟨P, e, rfl⟩ | ⟨P, e, rfl⟩ | ⟨P, e, rfl⟩
  · exact ⟨solidTorusCarrier.{u}, ⟨solidTorusRawPresentation.{u}⟩, ⟨e⟩⟩
  · exact ⟨mobiusBundleCarrier.{u}, ⟨twistedIBundleRawPresentation.{u}⟩, ⟨e⟩⟩
  · exact rawPiece_of_torusInterval P.toPieceFold e
  · exact rawPiece_of_torusInterval P.toPieceFold e

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- A certificate handle traversed in direction `σ`: its end disk `b` is the end disk `b xor σ` of
the handle, which lies in the face `handleFace h (b xor σ)`. -/
theorem orient_endDisk_subset_face (h : Fin D.handleCount) (σ b : Bool) :
    ((D.handle h).orient σ).endDisk b ⊆ D.face (D.handleFace h (xor b σ)) := by
  rw [EdgeHandle.orient_endDisk]
  exact D.handleEnd_face h (xor b σ)

/-- Reversing a certificate handle does not change its image. -/
theorem orient_range_eq (h : Fin D.handleCount) (σ : Bool) :
    range ((D.handle h).orient σ).map = range (D.handle h).map :=
  EdgeHandle.orient_range σ (D.handle h)

end DecompositionCertificate

end GC.GraphManifold.Assembly
