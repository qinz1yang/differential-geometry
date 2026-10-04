import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStep
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.HyperbolicPieceGroupFI

/-!
# Frozen vertices in a relative terminal stage

The protected branch of BR's existing stage invariant makes every port of a frozen piece
incompressible. With a positive seam count, its actual interior hyperbolic geometry gives a
freely indecomposable, noncyclic vertex group at every basepoint. If protected seams are empty
and frozen pieces are present, the seam count is zero and the positive-port argument does not
apply.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

theorem frozen_pairing_count_eq_zero (hp : σ.prot = ∅) (hf : σ.frozen ≠ ∅) :
    σ.toTorus.pairing.count = 0 := by
  by_contra hn
  exact hf (σ.frozen_eq_empty_of_prot_eq_empty hp (Nat.pos_of_ne_zero hn))

theorem pieceBoundaryTori_incompressible_of_incident_protected
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (i : Fin σ.toTorus.components.count)
    (hl : ∀ j, σ.toTorus.leftPiece j = i → j ∈ σ.prot)
    (hr : ∀ j, σ.toTorus.rightPiece j = i → j ∈ σ.prot) :
    (σ.toTorus.pieceBoundaryTori i).incompressible := by
  intro m x
  apply GC.Topology.injective_inner_of_composite _ (σ.toTorus.pieceToCarrier i) x
  let s := (Fintype.equivFin (σ.toTorus.OwnedSide i)).symm m
  obtain ⟨f, hf, hfeq⟩ : ∃ f : C(Torus, (NoCuts.carrier Q).Carrier),
      (∀ t, Function.Injective (FundamentalGroup.map f t)) ∧ ∀ t,
        σ.toTorus.cutMap (σ.toTorus.sideCollar s.val (t, halfZero)) = f t := by
    rcases hs : s.val with j | j | j
    · have hj : σ.toTorus.leftPiece j = i := by
        have ho := s.property
        rw [hs] at ho
        exact ho
      refine ⟨σ.toTorus.seamTorus j, hInc ⟨j, hl j hj⟩, ?_⟩
      intro t
      change σ.toTorus.cutMap (σ.toTorus.pairing.leftCollar j (t, halfZero)) = _
      rw [σ.toTorus.pairing.left_zero]
      exact (σ.toTorus.seamTorus_eq_cutMap j t).symm
    · have hj : σ.toTorus.rightPiece j = i := by
        have ho := s.property
        rw [hs] at ho
        exact ho
      let ψ := (σ.toTorus.pairing.matching j).symm.toHomeomorph
      refine ⟨(σ.toTorus.seamTorus j).comp (ψ : C(Torus, Torus)),
        (forall_injective_comp_homeomorph_iff _ ψ).mpr (hInc ⟨j, hr j hj⟩), ?_⟩
      intro t
      change σ.toTorus.cutMap (σ.toTorus.pairing.rightCollar j (t, halfZero)) = _
      rw [σ.toTorus.pairing.right_zero]
      change σ.toTorus.cutMap (σ.toTorus.pairing.rightParam j t) =
        σ.toTorus.seamTorus j ((σ.toTorus.pairing.matching j).symm t)
      simpa only [Diffeomorph.apply_symm_apply] using
        (σ.toTorus.seamTorus_eq_cutMap_right j
          ((σ.toTorus.pairing.matching j).symm t)).symm
    · exact (Fin.cast σ.toTorus.externalCount_eq_zero j).elim0
  have heq : (σ.toTorus.pieceToCarrier i).comp
      ((σ.toTorus.pieceBoundaryTori i).boundaryMap m) = f := by
    ext t
    change σ.toTorus.cutMap ((σ.toTorus.pieceBoundaryTori i).torusMap m t).val = f t
    rw [σ.toTorus.pieceBoundaryTori_torusMap]
    exact hfeq t
  rw [heq]
  exact hf x

theorem frozen_ports_incompressible
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (i : Fin σ.toTorus.components.count) (hi : i ∈ σ.frozen) :
    (σ.toTorus.pieceBoundaryTori i).incompressible :=
  σ.pieceBoundaryTori_incompressible_of_incident_protected hInc i
    (fun j hj => σ.left_prot j (hj.symm ▸ hi))
    (fun j hj => σ.right_prot j (hj.symm ▸ hi))

theorem frozen_indecomposableNoncyclic
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    (hn : 0 < σ.toTorus.pairing.count) (i : Fin σ.toTorus.components.count)
    (hi : i ∈ σ.frozen) (x : σ.toTorus.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (σ.toTorus.components.piece i) x) := by
  obtain ⟨g, hg⟩ := σ.hyperbolic i hi
  exact σ.toTorus.indecomposableNoncyclic_of_hyperbolic i
    (σ.frozen_ports_incompressible hInc i hi) (σ.toTorus.card_ownedSide_pos hn i) g hg x

end GC.Seifert.RelativeNormalization.MixedStage
