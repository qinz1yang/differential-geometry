import DifferentialGeometry.Geometry.Thurston.SphericalProductRawRecognition

/-!
Actual universe lifts of lens Raw presentations retain two solid tori and their gluing matrix.
Any diffeomorphic compact carrier inherits the same presentation counts.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)


abbrev lensSpaceLift : ConnectedClosedOrientedManifold.{u} 3 :=
  (lensSpaceFormGroup p q hpq).manifold.ulift.{0, u}


def lensSpaceLiftRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier (lensSpaceLift.{u} p q hpq)) :=
  RawUniverseLift.raw.{u} _ (lensSpaceRawGraphPresentation p q hpq)

theorem lensSpaceLiftRawGraphPresentation_counts :
    (lensSpaceLiftRawGraphPresentation.{u} p q hpq).components.count = 2 ∧
      (lensSpaceLiftRawGraphPresentation.{u} p q hpq).pairing.count = 1 ∧
      (lensSpaceLiftRawGraphPresentation.{u} p q hpq).externalCount = 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem lensSpaceLiftRawGraphPresentation_matching_eq :
    (lensSpaceLiftRawGraphPresentation.{u} p q hpq).pairing.matching (0 : Fin 1) =
      linearTorusDiffeomorph (lensMatrixUnit p q hpq) := by
  rfl

theorem exists_rawGraphPresentation_of_lensSpaceLift_diffeomorph {W : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, 𝓡 3⟯ (lensSpaceLift.{u} p q hpq).Carrier) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 2 ∧ G.pairing.count = 1 ∧ G.externalCount = 0 := by
  obtain ⟨G, he, hc, hp, -⟩ :=
    exists_rawGraphPresentation_of_carrierDiffeomorph
      (lensSpaceLiftRawGraphPresentation.{u} p q hpq) e.symm
  obtain ⟨hc₀, hp₀, he₀⟩ := lensSpaceLiftRawGraphPresentation_counts.{u} p q hpq
  exact ⟨G, hc.trans hc₀, hp.trans hp₀, he.trans he₀⟩

end Lens

end GC.GraphManifold
