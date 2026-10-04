import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# Standard product structures near a split seam

Lane N2c, tier 0. A product fibred piece of kind `k` of an elementary presentation is
re-trivialised over any planar base `B` with `k` boundary circles: the bases are identified
through their embeddings onto `planarModel k` (`baseDiffeo`), which match the boundary circles
on the nose, so the piece collars and the collars of `B` agree on the zero section
(`pieceCollar_standardPort_zero`). Collar straightening (`exists_germ_trivialization`) then
gives a trivialisation over `B` whose collars agree with the piece collars on a sub-collar
(`exists_standardTriv`). For a split seam this exhibits the solid torus over the round disc
`discPlanarBase 1` (collar `(t, s) ↦ (3 - 3s/2) t`) and the host over the round pants
`pantsPlanarBase` (collars `c_l + (r_l ∓ s/4) τ_l t`), near all their boundary tori
(`exists_standardSplit`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem planarCircleMap_cast {k k' : ℕ} (hk : k = k') (j : Fin k) (t : Circle) :
    planarCircleMap k' (Fin.cast hk j) t = planarCircleMap k j t := by
  subst hk
  rfl

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def baseDiffeo {k : ℕ} (B : PlanarBase.{u} k) (i : Fin E.toTorus.components.count)
    (hk : E.kind i = k) :
    B.surface.Carrier ≃ₘ⟮SurfaceModel.model B.surface.kind,
      SurfaceModel.model (E.piece i).base.surface.kind⟯ (E.piece i).base.surface.Carrier :=
  B.isSmoothEmbedding.diffeomorphOfRangeEq (E.piece i).base.isSmoothEmbedding (by
    rw [B.range_embedding, (E.piece i).base.range_embedding, hk])

theorem embedding_baseDiffeo {k : ℕ} (B : PlanarBase.{u} k)
    (i : Fin E.toTorus.components.count) (hk : E.kind i = k) (x : B.surface.Carrier) :
    (E.piece i).base.embedding (E.baseDiffeo B i hk x) = B.embedding x :=
  B.isSmoothEmbedding.comp_diffeomorphOfRangeEq (E.piece i).base.isSmoothEmbedding _ x

def standardTriv {k : ℕ} (B : PlanarBase.{u} k) (i : Fin E.toTorus.components.count)
    (hk : E.kind i = k) :
    (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      E.toTorus.cutCarrier.model⟯ E.toTorus.components.piece i :=
  ((E.baseDiffeo B i hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (E.piece i).trivialization

def standardPort {k : ℕ} (i : Fin E.toTorus.components.count) (hk : E.kind i = k) :
    Fin k ≃ E.toTorus.OwnedSide i :=
  (finCongr hk.symm).trans (E.piece i).port

theorem baseDiffeo_collar_zero {k : ℕ} (B : PlanarBase.{u} k)
    (i : Fin E.toTorus.components.count) (hk : E.kind i = k) (l : Fin k) (t : Circle) :
    E.baseDiffeo B i hk (B.collar l (t, halfZero)) =
      (E.piece i).base.collar (Fin.cast hk.symm l) (t, halfZero) := by
  apply (E.piece i).base.isSmoothEmbedding.isEmbedding.injective
  rw [embedding_baseDiffeo, B.embedding_collar, (E.piece i).base.embedding_collar,
    planarCircleMap_cast]

theorem pieceCollar_standardPort_zero {k : ℕ} (B : PlanarBase.{u} k)
    (i : Fin E.toTorus.components.count) (hk : E.kind i = k) (l : Fin k) (t : Torus) :
    E.toTorus.pieceCollar i (E.standardPort i hk l) (t, halfZero) =
      E.standardTriv B i hk (B.collar l (t.1, halfZero), t.2) := by
  have h := (E.piece i).collar_eq (Fin.cast hk.symm l) (t, halfZero)
    (zero_mem_halfCollarSource t)
  refine h.trans ?_
  change _ = (E.piece i).trivialization (E.baseDiffeo B i hk (B.collar l (t.1, halfZero)), t.2)
  rw [baseDiffeo_collar_zero]

theorem exists_standardTriv {k : ℕ} (B : PlanarBase.{u} k)
    (i : Fin E.toTorus.components.count) (hk : E.kind i = k) :
    ∃ δ > (0 : ℝ), ∃ Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      B.surface.kind).prod (𝓡 1), E.toTorus.cutCarrier.model⟯ E.toTorus.components.piece i,
        ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          E.toTorus.pieceCollar i (E.standardPort i hk l) p =
            Θ (B.collar l (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, Θ, hΘ⟩ := E.toTorus.exists_germ_trivialization i B (E.standardPort i hk)
    (fun _ => Diffeomorph.refl torusModel Torus ∞) (E.standardTriv B i hk)
    (fun l t => E.pieceCollar_standardPort_zero B i hk l t)
  exact ⟨δ, hδ, Θ, fun l p hp hlt => hΘ l p hp hlt⟩

theorem exists_standardSplit {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsSplitSeam j b) :
    ∃ δ > (0 : ℝ),
      ∃ ΘV : ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
        (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1), E.toTorus.cutCarrier.model⟯
          E.toTorus.components.piece (E.seamPiece j b),
      ∃ ΘH : (pantsPlanarBase.{u}.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
        pantsPlanarBase.{u}.surface.kind).prod (𝓡 1), E.toTorus.cutCarrier.model⟯
          E.toTorus.components.piece (E.hostPiece j b),
        (∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          E.toTorus.pieceCollar (E.seamPiece j b) (E.standardPort (E.seamPiece j b) h.1 l) p =
            ΘV ((discPlanarBase.{u} 1).collar l (p.1.1, p.2), p.1.2)) ∧
        ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          E.toTorus.pieceCollar (E.hostPiece j b) (E.standardPort (E.hostPiece j b) h.2.1 l)
            p = ΘH (pantsPlanarBase.{u}.collar l (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ₁, hδ₁, ΘV, hV⟩ := E.exists_standardTriv (discPlanarBase.{u} 1) _ h.1
  obtain ⟨δ₂, hδ₂, ΘH, hH⟩ := E.exists_standardTriv pantsPlanarBase.{u} _ h.2.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ΘV, ΘH, fun l p hp hlt => ?_, fun l p hp hlt => ?_⟩
  · exact hV l p hp (lt_of_lt_of_le hlt (min_le_left _ _))
  · exact hH l p hp (lt_of_lt_of_le hlt (min_le_right _ _))

end ElementaryPresentation

end GC.Seifert
