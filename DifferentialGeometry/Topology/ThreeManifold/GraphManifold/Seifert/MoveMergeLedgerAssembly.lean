import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMoves
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
# Mixed-stage assembly from actual whole product models

Actual compact product maps and boundary counts determine port parameters and genuine collar
germs. A finite common positive width supplies strict product pieces. Reparameterization and
shrinking keep the actual cut carrier, its orientation and every frozen compact piece unchanged.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization

structure MixedProductModels (Q : ConnectedClosedOrientedManifold.{u} 3) where
  T : TorusPresentation (NoCuts.carrier Q)
  prot : Finset (Fin T.pairing.count)
  frozen : Finset (Fin T.components.count)
  hyperbolic : ∀ i ∈ frozen,
    ∃ g : T.cutCarrier.InteriorGeometry (T.components.piece i),
      letI := Manifold.interiorChartedSpace T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      letI := Manifold.interiorIsManifold T.cutCarrier.model ∞
        (M := T.cutCarrier.pieceInterior (T.components.piece i))
      g.model = .hyperbolic
  kind : Fin T.components.count → ℕ
  kind_mem : ∀ i, i ∉ frozen → kind i ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ i : {i : Fin T.components.count // i ∉ frozen}, PlanarBase.{u} (kind i.val)
  theta : ∀ i : {i : Fin T.components.count // i ∉ frozen},
    ((base i).surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i.val
  card_owned : ∀ i : {i : Fin T.components.count // i ∉ frozen},
    Fintype.card (T.OwnedSide i.val) = kind i.val
  left_prot : ∀ j, T.leftPiece j ∈ frozen → j ∈ prot
  right_prot : ∀ j, T.rightPiece j ∈ frozen → j ∈ prot

namespace MixedProductModels

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (D : MixedProductModels Q)

abbrev GraphPiece : Type := {i : Fin D.T.components.count // i ∉ D.frozen}

end MixedProductModels

structure MixedProductAssembly {Q : ConnectedClosedOrientedManifold.{u} 3}
    (D : MixedProductModels Q) where
  psi : D.T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  piece : ∀ i : D.GraphPiece,
    ProductFibredPiece ((D.T.reparam psi).shrink delta_pos delta_le_one) i.val (D.kind i.val)

namespace MixedProductAssembly

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {D : MixedProductModels Q}
  (A : MixedProductAssembly D)

def stage : MixedStage Q where
  toTorus := (D.T.reparam A.psi).shrink A.delta_pos A.delta_le_one
  prot := D.prot
  frozen := D.frozen
  hyperbolic := D.hyperbolic
  kind := D.kind
  kind_mem := D.kind_mem
  piece i hi := A.piece ⟨i, hi⟩
  left_prot := D.left_prot
  right_prot := D.right_prot

theorem stage_toTorus : A.stage.toTorus =
    (D.T.reparam A.psi).shrink A.delta_pos A.delta_le_one := rfl

theorem stage_prot : A.stage.prot = D.prot := rfl

theorem stage_frozen : A.stage.frozen = D.frozen := rfl

theorem stage_kind : A.stage.kind = D.kind := rfl

theorem stage_innerCount : A.stage.innerCount = D.protᶜ.card := rfl

def collarLedger (k : Fin D.T.pairing.count) :
    CollarLedger Eq (D.T.seam k) (A.stage.toTorus.seam k) where
  reparam := A.psi (.inl k)
  scale := A.delta
  scale_pos := A.delta_pos
  scale_le_one := A.delta_le_one
  tracked p _hp := Eq.refl (D.T.seam k (A.psi (.inl k) p.1, A.delta * p.2))

def frozenDiffeomorph (i : Fin D.T.components.count) :
    (componentCarrier D.T.cutCarrier D.T.components i).Carrier
      ≃ₘ⟮(componentCarrier D.T.cutCarrier D.T.components i).model,
        (componentCarrier A.stage.toTorus.cutCarrier A.stage.toTorus.components i).model⟯
        (componentCarrier A.stage.toTorus.cutCarrier A.stage.toTorus.components i).Carrier :=
  Diffeomorph.refl (componentCarrier D.T.cutCarrier D.T.components i).model
    (componentCarrier D.T.cutCarrier D.T.components i).Carrier ∞

theorem frozen_oriented (i : Fin D.T.components.count) :
    (A.frozenDiffeomorph i).preservesOrientation
      (componentCarrier D.T.cutCarrier D.T.components i).orientation
      (componentCarrier A.stage.toTorus.cutCarrier A.stage.toTorus.components i).orientation :=
  Diffeomorph.preservesOrientation_refl
    (componentCarrier D.T.cutCarrier D.T.components i).orientation

theorem frozen_map (i : Fin D.T.components.count)
    (x : (componentCarrier D.T.cutCarrier D.T.components i).Carrier) :
    D.T.cutMap x.val = A.stage.toTorus.cutMap (A.frozenDiffeomorph i x).val := rfl

end MixedProductAssembly

namespace MixedProductModels

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (D : MixedProductModels Q)

def assembleWithGerms
    (psi : D.T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (port : ∀ i : D.GraphPiece, Fin (D.kind i.val) ≃ D.T.OwnedSide i.val)
    (theta : ∀ i : D.GraphPiece, ((D.base i).surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model (D.base i).surface.kind).prod (𝓡 1), D.T.cutCarrier.model⟯
        D.T.components.piece i.val)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcollar : ∀ i j p, p ∈ halfCollarSource → p.2.val 0 < delta →
      D.T.pieceCollar i.val (port i j) (psi (port i j).val p.1, p.2) =
        theta i ((D.base i).collar j (p.1.1, p.2), p.1.2)) :
    MixedProductAssembly D where
  psi := psi
  delta := delta
  delta_pos := hdelta
  delta_le_one := hdelta1
  piece i := (D.T.reparam psi).shrinkPiece i.val (D.base i)
    ((port i).trans (D.T.reparamOwnedSide psi i.val)) (theta i) hdelta hdelta1
      fun j p hp hlt => Subtype.ext
        ((TorusPresentation.pieceCollar_apply _ _ _ hp).trans
          ((congrArg (fun c => c p)
            (TorusPresentation.reparam_sideCollar D.T psi (port i j).val)).trans
              ((TorusPresentation.pieceCollar_apply D.T i.val (port i j)
                (p := (psi (port i j).val p.1, p.2)) hp).symm.trans
                  (congrArg Subtype.val (hcollar i j p hp hlt)))))

theorem exists_mixedProductAssembly : Nonempty (MixedProductAssembly D) := by
  classical
  have hport := fun i : D.GraphPiece => D.T.exists_port_of_diffeomorph
    i.val (D.base i) (D.card_owned i) (D.theta i)
  choose port localPsi hzero using hport
  let psi : D.T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun s =>
    if hi : D.T.sidePiece s ∉ D.frozen then
      localPsi ⟨D.T.sidePiece s, hi⟩
        ((port ⟨D.T.sidePiece s, hi⟩).symm ⟨s, rfl⟩)
    else Diffeomorph.refl torusModel Torus ∞
  have hpsi : ∀ (i : D.GraphPiece) (s : D.T.OwnedSide i.val),
      psi s.val = localPsi i ((port i).symm s) := by
    rintro ⟨i, hi⟩ ⟨s, hs⟩
    change D.T.sidePiece s = i at hs
    subst i
    simp only [psi, dite_eq_left hi]
  have hgerm := fun i : D.GraphPiece => D.T.exists_germ_trivialization
    i.val (D.base i) (port i) (localPsi i) (D.theta i) (hzero i)
  choose epsilon hepsilon theta htheta using hgerm
  let width : D.GraphPiece ⊕ Unit → ℝ := Sum.elim epsilon (fun _stub => 1)
  have hw : ∀ a, 0 < width a := by
    rintro (i | stub)
    · exact hepsilon i
    · exact one_pos
  have hne : (Finset.univ : Finset (D.GraphPiece ⊕ Unit)).Nonempty :=
    ⟨.inr (), Finset.mem_univ _⟩
  let delta := Finset.univ.inf' hne width
  have hdelta : 0 < delta := (Finset.lt_inf'_iff hne).mpr fun a _ha => hw a
  have hdelta1 : delta ≤ 1 := by
    change delta ≤ width (.inr ())
    exact Finset.inf'_le width (Finset.mem_univ (.inr ()))
  have hdeltae (i : D.GraphPiece) : delta ≤ epsilon i := by
    change delta ≤ width (.inl i)
    exact Finset.inf'_le width (Finset.mem_univ (.inl i))
  refine ⟨D.assembleWithGerms psi port theta hdelta hdelta1 ?_⟩
  intro i j p hp hlt
  rw [hpsi i (port i j), Equiv.symm_apply_apply]
  exact htheta i j p hp (lt_of_lt_of_le hlt (hdeltae i))

end MixedProductModels
end GC.Seifert.RelativeNormalization
