import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitLinear
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedStandard
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFlip

/-!
# The split site of a mixed stage

Lane MS, tier MS2 (design `handoffs/20261004-design-ms-mixed-split.md` §1.2). The facts of the
split chain of lane N2c that only read the torus presentation and the product fibred pieces of
the solid torus `V` and the host `H` of a split seam, restated for a mixed stage. Both pieces are
not frozen (`seamPiece_not_frozen`, `hostPiece_not_frozen`), so their product structures exist.
The texts follow `Seifert/MoveSplit.lean` (owned sides, `V ≠ H`; `seamSide`,
`sidePiece_seamSide`, `seamSide_eq_seamSide_iff` and `fillingDistance_false` are Codex X57's, from
`RelativeTerminalBlocksSolid` and `RelativeTerminalBlocksFlip`),
`Seifert/LinearSeams.lean` (`crossMap`, `crossUnit`, `leftOfSide`, `cutMap_sideCollar_eq_seam`)
and `Seifert/MoveSplitCappedStandard.lean` (`standardPort`, the re-trivialisation over a given
planar base agreeing with the piece collars on a sub-collar, `exists_standardSplit`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (sideHeight)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

section Seams

variable {j : Fin σ.toTorus.pairing.count} {b : Bool}

theorem seamPiece_not_frozen (h : σ.IsSplitSeam j b) : σ.seamPiece j b ∉ σ.frozen :=
  σ.seamPiece_not_mem_frozen h.1 b

theorem hostPiece_not_frozen (h : σ.IsSplitSeam j b) : σ.hostPiece j b ∉ σ.frozen :=
  σ.hostPiece_not_mem_frozen h.1 b

theorem exists_seamSide_eq (s : σ.toTorus.Side) : ∃ c β, σ.seamSide c β = s := by
  rcases s with c | c | i
  · exact ⟨c, true, rfl⟩
  · exact ⟨c, false, rfl⟩
  · exact absurd i.2 (by simp [σ.toTorus.externalCount_eq_zero])

theorem card_ownedSide_seamPiece (h : σ.IsSplitSeam j b) :
    Fintype.card (σ.toTorus.OwnedSide (σ.seamPiece j b)) = 1 := by
  rw [(σ.piece _ (σ.seamPiece_not_frozen h)).card_ownedSide, h.2.1]

theorem card_ownedSide_hostPiece (h : σ.IsSplitSeam j b) :
    Fintype.card (σ.toTorus.OwnedSide (σ.hostPiece j b)) = 3 := by
  rw [(σ.piece _ (σ.hostPiece_not_frozen h)).card_ownedSide, h.2.2.1]

theorem seamPiece_ne_hostPiece (h : σ.IsSplitSeam j b) : σ.seamPiece j b ≠ σ.hostPiece j b := by
  intro he
  have h1 := h.2.1
  have h3 := h.2.2.1
  rw [he] at h1
  omega

theorem eq_of_seamPiece_eq_of_isSplitSeam {j' : Fin σ.toTorus.pairing.count} {b' : Bool}
    (h : σ.IsSplitSeam j b) (h' : σ.seamPiece j' b' = σ.seamPiece j b) : j' = j ∧ b' = b := by
  have hs : Subsingleton (σ.toTorus.OwnedSide (σ.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (σ.card_ownedSide_seamPiece h).le
  have he := congrArg Subtype.val (Subsingleton.elim
    (⟨σ.seamSide j' b', (σ.sidePiece_seamSide j' b').trans h'⟩ :
      σ.toTorus.OwnedSide (σ.seamPiece j b))
    ⟨σ.seamSide j b, σ.sidePiece_seamSide j b⟩)
  exact (σ.seamSide_eq_seamSide_iff).1 he

end Seams

section Cross

variable (j : Fin σ.toTorus.pairing.count)

def crossMap : Bool → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus
  | true => σ.toTorus.pairing.matching j
  | false => (σ.toTorus.pairing.matching j).symm

def crossUnit : Bool → GL (Fin 2) ℤ
  | true => torusUnit (σ.toTorus.pairing.matching j)
  | false => (torusUnit (σ.toTorus.pairing.matching j))⁻¹

theorem fillingDistance_eq_crossUnit :
    ∀ b, σ.fillingDistance j b = PrimitiveSlope.delta (σ.crossUnit j b • meridianSlope) fiberSlope
  | true => rfl
  | false => σ.fillingDistance_false j

variable {σ j} in
theorem IsLinearSeam.crossMap_apply (h : σ.IsLinearSeam j) :
    ∀ b t, σ.crossMap j b t = linearTorusMap (σ.crossUnit j b) t
  | true, t => congrArg (fun φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus => φ t) h
  | false, t => congrArg (fun φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus => φ.symm t) h

def leftOfSide : Bool → Torus → Torus
  | true => id
  | false => (σ.toTorus.pairing.matching j).symm

theorem leftOfSide_not_crossMap :
    ∀ (b : Bool) (t : Torus), σ.leftOfSide j (!b) (σ.crossMap j b t) = σ.leftOfSide j b t
  | true, t => (σ.toTorus.pairing.matching j).symm_apply_apply t
  | false, _ => rfl

theorem cutMap_sideCollar_eq_seam :
    ∀ (b : Bool) (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
      σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide j b) (t, halfPoint s hs)) =
        σ.toTorus.seam j (σ.leftOfSide j b t, sideHeight b s)
  | true, t, s, hs, hs1 => σ.toTorus.cutMap_leftCollar j (p := (t, halfPoint s hs)) hs1
  | false, t, s, hs, hs1 => σ.toTorus.cutMap_rightCollar j (p := (t, halfPoint s hs)) hs1

end Cross

section Standard

variable {k : ℕ} (B : PlanarBase.{u} k) (i : Fin σ.toTorus.components.count) (hi : i ∉ σ.frozen)
  (hk : σ.kind i = k)

def baseDiffeo :
    B.surface.Carrier ≃ₘ⟮SurfaceModel.model B.surface.kind,
      SurfaceModel.model (σ.piece i hi).base.surface.kind⟯ (σ.piece i hi).base.surface.Carrier :=
  B.isSmoothEmbedding.diffeomorphOfRangeEq (σ.piece i hi).base.isSmoothEmbedding (by
    rw [B.range_embedding, (σ.piece i hi).base.range_embedding, hk])

theorem embedding_baseDiffeo (x : B.surface.Carrier) :
    (σ.piece i hi).base.embedding (σ.baseDiffeo B i hi hk x) = B.embedding x :=
  B.isSmoothEmbedding.comp_diffeomorphOfRangeEq (σ.piece i hi).base.isSmoothEmbedding _ x

def standardTriv :
    (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      σ.toTorus.cutCarrier.model⟯ σ.toTorus.components.piece i :=
  ((σ.baseDiffeo B i hi hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (σ.piece i hi).trivialization

variable {B} in
def standardPort : Fin k ≃ σ.toTorus.OwnedSide i :=
  (finCongr hk.symm).trans (σ.piece i hi).port

theorem baseDiffeo_collar_zero (l : Fin k) (t : Circle) :
    σ.baseDiffeo B i hi hk (B.collar l (t, halfZero)) =
      (σ.piece i hi).base.collar (Fin.cast hk.symm l) (t, halfZero) := by
  apply (σ.piece i hi).base.isSmoothEmbedding.isEmbedding.injective
  rw [embedding_baseDiffeo, B.embedding_collar, (σ.piece i hi).base.embedding_collar,
    planarCircleMap_cast]

theorem pieceCollar_standardPort_zero (l : Fin k) (t : Torus) :
    σ.toTorus.pieceCollar i (σ.standardPort i hi hk l) (t, halfZero) =
      σ.standardTriv B i hi hk (B.collar l (t.1, halfZero), t.2) := by
  have h := (σ.piece i hi).collar_eq (Fin.cast hk.symm l) (t, halfZero)
    (zero_mem_halfCollarSource t)
  refine h.trans ?_
  change _ = (σ.piece i hi).trivialization
    (σ.baseDiffeo B i hi hk (B.collar l (t.1, halfZero)), t.2)
  rw [baseDiffeo_collar_zero]

theorem exists_standardTriv :
    ∃ δ > (0 : ℝ), ∃ Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      B.surface.kind).prod (𝓡 1), σ.toTorus.cutCarrier.model⟯ σ.toTorus.components.piece i,
        ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          σ.toTorus.pieceCollar i (σ.standardPort i hi hk l) p =
            Θ (B.collar l (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, Θ, hΘ⟩ := σ.toTorus.exists_germ_trivialization i B (σ.standardPort i hi hk)
    (fun _ => Diffeomorph.refl torusModel Torus ∞) (σ.standardTriv B i hi hk)
    (fun l t => σ.pieceCollar_standardPort_zero B i hi hk l t)
  exact ⟨δ, hδ, Θ, fun l p hp hlt => hΘ l p hp hlt⟩

end Standard

section Split

variable {j : Fin σ.toTorus.pairing.count} {b : Bool}

theorem exists_standardSplit (h : σ.IsSplitSeam j b) :
    ∃ δ > (0 : ℝ),
      ∃ ΘV : ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
        (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1), σ.toTorus.cutCarrier.model⟯
          σ.toTorus.components.piece (σ.seamPiece j b),
      ∃ ΘH : (pantsPlanarBase.{u}.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
        pantsPlanarBase.{u}.surface.kind).prod (𝓡 1), σ.toTorus.cutCarrier.model⟯
          σ.toTorus.components.piece (σ.hostPiece j b),
        (∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          σ.toTorus.pieceCollar (σ.seamPiece j b)
            (σ.standardPort (σ.seamPiece j b) (σ.seamPiece_not_frozen h) h.2.1 l) p =
            ΘV ((discPlanarBase.{u} 1).collar l (p.1.1, p.2), p.1.2)) ∧
        ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
          σ.toTorus.pieceCollar (σ.hostPiece j b)
            (σ.standardPort (σ.hostPiece j b) (σ.hostPiece_not_frozen h) h.2.2.1 l) p =
            ΘH (pantsPlanarBase.{u}.collar l (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ₁, hδ₁, ΘV, hV⟩ := σ.exists_standardTriv (discPlanarBase.{u} 1) _
    (σ.seamPiece_not_frozen h) h.2.1
  obtain ⟨δ₂, hδ₂, ΘH, hH⟩ := σ.exists_standardTriv pantsPlanarBase.{u} _
    (σ.hostPiece_not_frozen h) h.2.2.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ΘV, ΘH, fun l p hp hlt => ?_, fun l p hp hlt => ?_⟩
  · exact hV l p hp (lt_of_lt_of_le hlt (min_le_left _ _))
  · exact hH l p hp (lt_of_lt_of_le hlt (min_le_right _ _))

end Split

end GC.Seifert.RelativeNormalization.MixedStage
