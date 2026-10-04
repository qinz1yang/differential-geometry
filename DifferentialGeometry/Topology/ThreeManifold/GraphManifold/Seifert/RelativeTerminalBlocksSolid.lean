import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFrozen
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoSolidTori

/-!
# Solid vertices in relative terminal stages

A solid product piece has one actual owned side. Its incident seam cannot be protected:
incompressibility would inject the noncyclic torus group into its cyclic fundamental group.
At an inner seam, terminality excludes an annulus host and filling distances zero and one
on a pants host. The argument uses only actual local pieces and the protected seam ledger.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

def seamSide (j : Fin σ.toTorus.pairing.count) : Bool → σ.toTorus.Side
  | true => .inl j
  | false => .inr (.inl j)

theorem sidePiece_seamSide (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    σ.toTorus.sidePiece (σ.seamSide j b) = σ.seamPiece j b := by
  cases b <;> rfl

theorem seamSide_eq_seamSide_iff {j j' : Fin σ.toTorus.pairing.count} {b b' : Bool} :
    σ.seamSide j b = σ.seamSide j' b' ↔ j = j' ∧ b = b' := by
  cases b <;> cases b' <;> simp [seamSide]

theorem solid_ownedSide_subsingleton {i : Fin σ.toTorus.components.count}
    (hi : i ∉ σ.frozen) (hk : σ.kind i = 1) : Subsingleton (σ.toTorus.OwnedSide i) := by
  apply Fintype.card_le_one_iff_subsingleton.mp
  rw [(σ.piece i hi).card_ownedSide, hk]

theorem eq_of_solid_seamPiece_eq {j : Fin σ.toTorus.pairing.count} {b : Bool}
    (hi : σ.seamPiece j b ∉ σ.frozen) (hk : σ.kind (σ.seamPiece j b) = 1)
    {j' : Fin σ.toTorus.pairing.count} {b' : Bool}
    (he : σ.seamPiece j' b' = σ.seamPiece j b) : j' = j ∧ b' = b := by
  have hs := σ.solid_ownedSide_subsingleton hi hk
  have h := congrArg Subtype.val (hs.elim
    (⟨σ.seamSide j' b', (σ.sidePiece_seamSide j' b').trans he⟩ :
      σ.toTorus.OwnedSide (σ.seamPiece j b))
    ⟨σ.seamSide j b, σ.sidePiece_seamSide j b⟩)
  exact σ.seamSide_eq_seamSide_iff.mp h

theorem solid_seamPiece_ne_hostPiece {j : Fin σ.toTorus.pairing.count} (b : Bool)
    (hi : σ.seamPiece j b ∉ σ.frozen) (hk : σ.kind (σ.seamPiece j b) = 1) :
    σ.seamPiece j b ≠ σ.hostPiece j b := by
  intro he
  have h := σ.eq_of_solid_seamPiece_eq hi hk he.symm
  cases b <;> simp at h

theorem solid_seam_not_protected
    (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
    {j : Fin σ.toTorus.pairing.count} (b : Bool)
    (hi : σ.seamPiece j b ∉ σ.frozen) (hk : σ.kind (σ.seamPiece j b) = 1) :
    j ∉ σ.prot := by
  intro hj
  let i := σ.seamPiece j b
  let P : SolidTorusPiece σ.toTorus i := by
    have hp := σ.piece i hi
    have hki : σ.kind i = 1 := hk
    rw [hki] at hp
    exact hp
  have hin : (σ.toTorus.pieceBoundaryTori i).incompressible :=
    σ.pieceBoundaryTori_incompressible_of_incident_protected hInc i
      (fun k h => (σ.eq_of_solid_seamPiece_eq hi hk
        (show σ.seamPiece k true = σ.seamPiece j b from h)).1 ▸ hj)
      (fun k h => (σ.eq_of_solid_seamPiece_eq hi hk
        (show σ.seamPiece k false = σ.seamPiece j b from h)).1 ▸ hj)
  let m : Fin (Fintype.card (σ.toTorus.OwnedSide i)) :=
    ⟨0, by rw [P.card_ownedSide]; decide⟩
  have hnon := not_isCyclic_of_injective
    (FundamentalGroup.map ((σ.toTorus.pieceBoundaryTori i).boundaryMap m) (1, 1))
    (hin m (1, 1)) (indecomposableNoncyclic_torus (1, 1)).2
  exact hnon (P.isCyclic_fundamentalGroup
    ((σ.toTorus.pieceBoundaryTori i).boundaryMap m (1, 1)))

theorem solid_incident_seam_not_injective
    {T : TorusPresentation (NoCuts.carrier Q)} {i : Fin T.components.count}
    {j : Fin T.pairing.count} (P : SolidTorusPiece T i)
    (hside : T.leftPiece j = i ∨ T.rightPiece j = i) :
    ¬ ∀ t, Function.Injective (FundamentalGroup.map (T.seamTorus j) t) := by
  intro hinj
  obtain ⟨s, f, hf, hs⟩ : ∃ (s : T.OwnedSide i) (f : C(Torus, (NoCuts.carrier Q).Carrier)),
      (∀ t, Function.Injective (FundamentalGroup.map f t)) ∧
        ∀ t, T.cutMap (T.sideCollar s.val (t, halfZero)) = f t := by
    rcases hside with hl | hr
    · refine ⟨⟨.inl j, hl⟩, T.seamTorus j, hinj, ?_⟩
      intro t
      change T.cutMap (T.pairing.leftCollar j (t, halfZero)) = _
      rw [T.pairing.left_zero]
      exact (T.seamTorus_eq_cutMap j t).symm
    · let ψ := (T.pairing.matching j).symm.toHomeomorph
      refine ⟨⟨.inr (.inl j), hr⟩, (T.seamTorus j).comp (ψ : C(Torus, Torus)),
        (forall_injective_comp_homeomorph_iff _ ψ).mpr hinj, ?_⟩
      intro t
      change T.cutMap (T.pairing.rightCollar j (t, halfZero)) = _
      rw [T.pairing.right_zero]
      change T.cutMap (T.pairing.rightParam j t) =
        T.seamTorus j ((T.pairing.matching j).symm t)
      simpa only [Diffeomorph.apply_symm_apply] using
        (T.seamTorus_eq_cutMap_right j ((T.pairing.matching j).symm t)).symm
  let m := Fintype.equivFin (T.OwnedSide i) s
  have heq : (T.pieceToCarrier i).comp ((T.pieceBoundaryTori i).boundaryMap m) = f := by
    ext t
    change T.cutMap ((T.pieceBoundaryTori i).torusMap m t).val = f t
    rw [T.pieceBoundaryTori_torusMap]
    simpa only [m, Equiv.symm_apply_apply] using hs t
  have hport : Function.Injective
      (FundamentalGroup.map ((T.pieceBoundaryTori i).boundaryMap m) (1, 1)) := by
    apply GC.Topology.injective_inner_of_composite _ (T.pieceToCarrier i) (1, 1)
    rw [heq]
    exact hf (1, 1)
  exact (not_isCyclic_of_injective _ hport (indecomposableNoncyclic_torus (1, 1)).2)
    (P.isCyclic_fundamentalGroup ((T.pieceBoundaryTori i).boundaryMap m (1, 1)))

theorem terminal_inner_solid_host_ne_two (ht : σ.IsTerminal)
    {j : Fin σ.toTorus.pairing.count} (b : Bool) (hj : j ∉ σ.prot)
    (hk : σ.kind (σ.seamPiece j b) = 1) : σ.kind (σ.hostPiece j b) ≠ 2 := by
  intro hh
  exact (ht j b).2.2 ⟨hj, hk, hh⟩

theorem terminal_inner_solid_distance_ge_two (ht : σ.IsTerminal)
    {j : Fin σ.toTorus.pairing.count} (b : Bool) (hj : j ∉ σ.prot)
    (hk : σ.kind (σ.seamPiece j b) = 1) (hhost : σ.kind (σ.hostPiece j b) = 3) :
    2 ≤ σ.fillingDistance j b := by
  have hzero : σ.fillingDistance j b ≠ 0 := fun h => (ht j b).2.1 ⟨hj, hk, hhost, h⟩
  have hone : σ.fillingDistance j b ≠ 1 :=
    fun h => (ht j b).1 ⟨hj, hk, by omega, h⟩
  omega

end GC.Seifert.RelativeNormalization.MixedStage
