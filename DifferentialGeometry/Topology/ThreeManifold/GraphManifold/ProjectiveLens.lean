import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensLift

/-!
The actual L(2,1) quotient equals projective three-space with its orientation, and the lifted
lens presentation gives the explicit two-solid-torus Raw data on that projective model.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold

theorem lensSpaceLift_two_one_eq :
    lensSpaceLift.{u} 2 1 isCoprime_one_right = projectiveThreeSpaceLift.{u} := by
  exact congrArg (fun G : SphericalSpaceFormGroup => G.manifold.ulift.{0, u})
    (lensSpaceFormGroup_two_one_eq_antipodal isCoprime_one_right)

private def lensEqualityIdentification (A B : ConnectedClosedOrientedManifold.{u} 3)
    (h : A = B) : {e : A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ B.Carrier //
      e.preservesOrientation A.orientation B.orientation} := by
  subst B
  exact ⟨Diffeomorph.refl (𝓡 3) A.Carrier ∞,
    Diffeomorph.preservesOrientation_refl A.orientation⟩

def projectiveThreeSpaceLensDiffeomorph :
    (lensSpaceLift.{u} 2 1 isCoprime_one_right).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      projectiveThreeSpaceLift.{u}.Carrier := by
  exact (lensEqualityIdentification
    (lensSpaceLift.{u} 2 1 isCoprime_one_right) projectiveThreeSpaceLift.{u}
    lensSpaceLift_two_one_eq).val

theorem projectiveThreeSpaceLensDiffeomorph_preservesOrientation :
    projectiveThreeSpaceLensDiffeomorph.{u}.preservesOrientation
      (lensSpaceLift.{u} 2 1 isCoprime_one_right).orientation
      projectiveThreeSpaceLift.{u}.orientation := by
  exact (lensEqualityIdentification
    (lensSpaceLift.{u} 2 1 isCoprime_one_right) projectiveThreeSpaceLift.{u}
    lensSpaceLift_two_one_eq).property

def projectiveThreeSpaceLensRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier projectiveThreeSpaceLift.{u}) :=
  (lensSpaceLiftRawGraphPresentation.{u} 2 1 isCoprime_one_right).transport
    (W' := NoCuts.carrier projectiveThreeSpaceLift.{u})
    projectiveThreeSpaceLensDiffeomorph projectiveThreeSpaceLensDiffeomorph_preservesOrientation

theorem projectiveThreeSpaceLensRawGraphPresentation_counts :
    projectiveThreeSpaceLensRawGraphPresentation.{u}.components.count = 2 ∧
      projectiveThreeSpaceLensRawGraphPresentation.{u}.pairing.count = 1 ∧
      projectiveThreeSpaceLensRawGraphPresentation.{u}.externalCount = 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem projectiveThreeSpaceLensRawGraphPresentation_matching_eq :
    projectiveThreeSpaceLensRawGraphPresentation.{u}.pairing.matching (0 : Fin 1) =
      linearTorusDiffeomorph (lensMatrixUnit 2 1 isCoprime_one_right) := by
  rfl


theorem nonempty_rawGraphPresentation_projectiveThreeSpaceLift_lens :
    Nonempty (RawGraphPresentation (NoCuts.carrier projectiveThreeSpaceLift.{u})) := by
  exact ⟨projectiveThreeSpaceLensRawGraphPresentation.{u}⟩

theorem exists_rawGraphPresentation_of_projectiveThreeSpaceLift_diffeomorph
    {W : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 2 ∧ G.pairing.count = 1 ∧ G.externalCount = 0 := by
  obtain ⟨G, he, hc, hp, -⟩ :=
    exists_rawGraphPresentation_of_carrierDiffeomorph
      projectiveThreeSpaceLensRawGraphPresentation.{u} e.symm
  obtain ⟨hc₀, hp₀, he₀⟩ := projectiveThreeSpaceLensRawGraphPresentation_counts.{u}
  exact ⟨G, hc.trans hc₀, hp.trans hp₀, he.trans he₀⟩



end GC.GraphManifold
