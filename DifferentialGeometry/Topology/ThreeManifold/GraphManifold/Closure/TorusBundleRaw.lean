import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BasicModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ClosedQuotient
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy

/-!
Actual oriented raw presentations of smooth torus mapping tori, with one piece and one self-seam.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def torusBundleRawComponents : annulusCircleCarrier.{u}.Components :=
  annulusRawPresentation.components

def torusBundleRawFibration (i : Fin torusBundleRawComponents.{u}.count) :
    CircleFibration annulusCircleCarrier (torusBundleRawComponents.piece i) :=
  annulusRawPresentation.fibration i

private theorem components_count_transport (C C' : CompactCarrier.{u})
    (h : C' = C) (D : C'.Components) : (h ▸ D).count = D.count := by
  cases h
  rfl

private theorem pairing_count_transport (C C' : CompactCarrier.{u})
    (h : C' = C) (P : TorusPairing C') : (h ▸ P).count = P.count := by
  cases h
  rfl

private theorem pairing_matching_transport (C C' : CompactCarrier.{u})
    (h : C' = C) (P : TorusPairing C')
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hm : ∀ j, (h ▸ P).matching j = f) : ∀ j, P.matching j = f := by
  cases h
  exact hm

theorem exists_torusBundleRawPresentation
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
      (Q : ConnectedClosedOrientedManifold.{u} 3)
      (G : RawGraphPresentation (NoCuts.carrier Q))
      (hC : G.cutCarrier = annulusCircleCarrier),
      (hC ▸ G.components) = torusBundleRawComponents ∧
      (hC ▸ G.pairing) = (torusMonodromyPairing f hf).shrink hδ hδ1 ∧
      G.components.count = 1 ∧ G.pairing.count = 1 ∧ G.externalCount = 0 ∧
      (∀ j, G.leftPiece j = G.rightPiece j) ∧
      ∃ s : Fin 1 ≃ Fin G.pairing.count,
        (∀ i, G.pairing.matching (s i) = f) ∧
        ∃ e : Quotient (monodromyIntervalGluing f).setoid ≃ₜ Q.Carrier,
          (∀ x : annulusCircleCarrier.Carrier,
            e (Quotient.mk'' (torusMonodromyPolar x)) =
              G.reconstruction (G.pairing.quotientMap (hC.symm ▸ x))) ∧
          ∀ p : Torus × unitInterval, e (Quotient.mk'' p) =
            G.reconstruction (G.pairing.quotientMap
              (hC.symm ▸ torusMonodromyPolar.symm p)) := by
  let P := torusMonodromyPairing.{u} f hf
  let : ConnectedSpace P.QuotientSpace := torusMonodromyPairing_connected f hf
  have hb : annulusCircleCarrier.{u}.model.boundary annulusCircleCarrier.Carrier =
      ⋃ j, P.gluing.block j := torusMonodromyGluing_boundary f
  let left : Fin P.count → Fin torusBundleRawComponents.{u}.count :=
    Function.const (Fin P.count) ⟨0, Nat.one_pos⟩
  let right : Fin P.count → Fin torusBundleRawComponents.{u}.count := left
  have hl : ∀ j, P.gluing.left j ⊆ torusBundleRawComponents.piece (left j) :=
    fun j => Set.subset_univ (P.gluing.left j)
  have hr : ∀ j, P.gluing.right j ⊆ torusBundleRawComponents.piece (right j) :=
    fun j => Set.subset_univ (P.gluing.right j)
  obtain ⟨δ, hδ, hδ1, Q, G, hC, hD, hP, eP, he⟩ :=
    exists_closedRawTorusQuotient annulusCircleCarrier torusBundleRawComponents
      torusBundleRawFibration P hb left right hl hr
  have hc : G.components.count = 1 := by
    have h := congrArg (fun D : annulusCircleCarrier.{u}.Components => D.count) hD
    rw [components_count_transport] at h
    exact h
  have hp : G.pairing.count = 1 := by
    have h := congrArg (fun R : TorusPairing annulusCircleCarrier.{u} => R.count) hP
    rw [pairing_count_transport] at h
    exact h
  have hmatch : ∀ j, G.pairing.matching j = f := by
    apply pairing_matching_transport annulusCircleCarrier G.cutCarrier hC G.pairing f
    rw [hP]
    intro j
    rfl
  have hself : ∀ j, G.leftPiece j = G.rightPiece j := by
    intro j
    apply Fin.ext
    have hl0 := (G.leftPiece j).isLt
    have hr0 := (G.rightPiece j).isLt
    omega
  let H := torusMonodromyPairingQuotientHomeomorph.{u} f hf
  let e : Quotient (monodromyIntervalGluing f).setoid ≃ₜ Q.Carrier := H.symm.trans eP
  have hx : ∀ x : annulusCircleCarrier.{u}.Carrier,
      e (Quotient.mk'' (torusMonodromyPolar x)) =
        G.reconstruction (G.pairing.quotientMap (hC.symm ▸ x)) := by
    intro x
    change eP (H.symm (Quotient.mk'' (torusMonodromyPolar x))) = _
    rw [← torusMonodromyPairingQuotientHomeomorph_apply f hf x]
    rw [Homeomorph.symm_apply_apply]
    exact he x
  refine ⟨δ, hδ, hδ1, Q, G, hC, hD, hP, hc, hp,
    G.toTorusPresentation.externalCount_eq_zero, hself, finCongr hp.symm,
    fun i => hmatch (finCongr hp.symm i), e, hx, ?_⟩
  intro p
  have h := hx (torusMonodromyPolar.{u}.symm p)
  rw [Homeomorph.apply_symm_apply] at h
  exact h

end GC.GraphManifold
