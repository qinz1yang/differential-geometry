import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

/-!
# Chapter-14 assembly, item L1, group G3c: from a parametrization of the union to a diffeomorphism

`nonempty_diffeomorph_of_range_eq`: a smooth injective map of the standard solid torus into the
carrier, with injective differential everywhere and the same image as a piece embedding, gives a
diffeomorphism of the solid torus onto the piece. Both maps are topological embeddings with injective
differential between manifolds with smooth boundary, so a map into either source is smooth as soon
as its composite into the carrier is (`contMDiff_iff_comp_of_fullRank_embedding`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **G3c, factorization.** A smooth injective immersion of the solid torus with the image of a
piece embedding is a diffeomorphism onto the piece. -/
theorem nonempty_diffeomorph_of_range_eq {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (F : solidTorusSet.{u} → W.Carrier) (hF : ContMDiff (𝓡∂ 3) W.model ∞ F) (hinj : Injective F)
    (hd : ∀ p, Injective (mfderiv (𝓡∂ 3) W.model F p)) (hrange : range F = range P.map) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ P.Piece) := by
  have hFemb : Topology.IsEmbedding F := (hF.continuous.isClosedEmbedding hinj).isEmbedding
  have hPemb : Topology.IsEmbedding P.map := P.isClosedEmbedding_map.isEmbedding
  let e : solidTorusSet.{u} ≃ₜ P.Piece :=
    hFemb.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans P.homeomorphRange.symm)
  have he (x : solidTorusSet.{u}) : P.map (e x) = F x := by
    have hx := P.homeomorphRange.apply_symm_apply
      ((Homeomorph.setCongr hrange) (hFemb.toHomeomorph x))
    exact congrArg Subtype.val hx
  have hei (y : P.Piece) : F (e.symm y) = P.map y := by
    rw [← he, e.apply_symm_apply]
  have hFe : P.map ∘ e = F := funext he
  have hPe : F ∘ e.symm = P.map := funext hei
  let D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) solidTorusSet.{u} P.Piece ∞ :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := by
        apply (DifferentialGeometry.Geometry.Boundary.contMDiff_iff_comp_of_fullRank_embedding
          P.smooth hPemb (fun x => (P.mfderiv_bijective x).1) rfl
          (e : solidTorusSet.{u} → P.Piece)).mpr
        rw [show P.map ∘ (e : solidTorusSet.{u} → P.Piece) = F from hFe]
        exact hF
      contMDiff_invFun := by
        apply (DifferentialGeometry.Geometry.Boundary.contMDiff_iff_comp_of_fullRank_embedding
          hF hFemb hd rfl (e.symm : P.Piece → solidTorusSet.{u})).mpr
        rw [show F ∘ (e.symm : P.Piece → solidTorusSet.{u}) = P.map from hPe]
        exact P.smooth }
  exact ⟨D⟩

end GC.GraphManifold.Assembly
