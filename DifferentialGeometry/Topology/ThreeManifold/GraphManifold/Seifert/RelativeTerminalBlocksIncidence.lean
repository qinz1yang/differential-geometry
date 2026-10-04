import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSolid

/-!
# Solid incidence in the positive protected branch

Two solid endpoints have no other ports. Connectedness of the original closed carrier then
makes their seam pair contain every component. Such a configuration is incompatible with an
actual protected injective seam. A terminal inner solid filling therefore has a pants host in
the branch with a protected seam.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem twoSolid_components_in_pair (T : TorusPresentation (NoCuts.carrier Q))
    (j : Fin T.pairing.count) (PL : SolidTorusPiece T (T.leftPiece j))
    (PR : SolidTorusPiece T (T.rightPiece j)) (i : Fin T.components.count) :
    i ∈ T.seamPair j := by
  have hL : Subsingleton (T.OwnedSide (T.leftPiece j)) :=
    Fintype.card_le_one_iff_subsingleton.mp PL.card_ownedSide.le
  have hR : Subsingleton (T.OwnedSide (T.rightPiece j)) :=
    Fintype.card_le_one_iff_subsingleton.mp PR.card_ownedSide.le
  refine T.mem_of_not_isCrossing (T.seamPair j) ⟨_, T.left_mem_seamPair j⟩ (fun k hk => ?_) i
  rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rcases T.eq_or_eq_of_mem_seamPair hl with he | he
    · have hs := congrArg Subtype.val
        (hL.elim (⟨.inl k, he⟩ : T.OwnedSide _) ⟨.inl j, rfl⟩)
      obtain rfl : k = j := Sum.inl_injective hs
      exact hr (T.right_mem_seamPair k)
    · have hs := congrArg Subtype.val
        (hR.elim (⟨.inl k, he⟩ : T.OwnedSide _) ⟨.inr (.inl j), rfl⟩)
      exact absurd hs (by simp)
  · rcases T.eq_or_eq_of_mem_seamPair hr with he | he
    · have hs := congrArg Subtype.val
        (hL.elim (⟨.inr (.inl k), he⟩ : T.OwnedSide _) ⟨.inl j, rfl⟩)
      exact absurd hs (by simp)
    · have hs := congrArg Subtype.val
        (hR.elim (⟨.inr (.inl k), he⟩ : T.OwnedSide _) ⟨.inr (.inl j), rfl⟩)
      obtain rfl : k = j := Sum.inl_injective (Sum.inr_injective hs)
      exact hl (T.left_mem_seamPair k)

variable (σ : MixedStage Q)
  (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
    Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))
  (hp : σ.prot.Nonempty)

include hInc hp in
theorem inner_solid_host_not_one {j : Fin σ.toTorus.pairing.count} (b : Bool)
    (hj : j ∉ σ.prot) (hk : σ.kind (σ.seamPiece j b) = 1) :
    σ.kind (σ.hostPiece j b) ≠ 1 := by
  intro hh
  have hl : σ.kind (σ.toTorus.leftPiece j) = 1 := by cases b <;> first | exact hh | exact hk
  have hr : σ.kind (σ.toTorus.rightPiece j) = 1 := by cases b <;> first | exact hk | exact hh
  let PL : SolidTorusPiece σ.toTorus (σ.toTorus.leftPiece j) := by
    have P : ProductFibredPiece σ.toTorus (σ.toTorus.leftPiece j)
        (σ.kind (σ.toTorus.leftPiece j)) :=
      σ.piece _ (σ.seamPiece_not_mem_frozen hj true)
    rw [hl] at P
    exact P
  let PR : SolidTorusPiece σ.toTorus (σ.toTorus.rightPiece j) := by
    have P : ProductFibredPiece σ.toTorus (σ.toTorus.rightPiece j)
        (σ.kind (σ.toTorus.rightPiece j)) :=
      σ.piece _ (σ.seamPiece_not_mem_frozen hj false)
    rw [hr] at P
    exact P
  obtain ⟨k, hkP⟩ := hp
  have hi := twoSolid_components_in_pair σ.toTorus j PL PR (σ.toTorus.leftPiece k)
  rcases σ.toTorus.eq_or_eq_of_mem_seamPair hi with he | he
  · have hk1 : σ.kind (σ.toTorus.leftPiece k) = 1 := by rw [he]; exact hl
    have hf : σ.toTorus.leftPiece k ∉ σ.frozen := by
      rw [he]; exact σ.seamPiece_not_mem_frozen hj true
    exact σ.solid_seam_not_protected hInc true hf hk1 hkP
  · have hk1 : σ.kind (σ.toTorus.leftPiece k) = 1 := by rw [he]; exact hr
    have hf : σ.toTorus.leftPiece k ∉ σ.frozen := by
      rw [he]; exact σ.seamPiece_not_mem_frozen hj false
    exact σ.solid_seam_not_protected hInc true hf hk1 hkP

include hInc hp in
theorem terminal_inner_solid_host_eq_three (ht : σ.IsTerminal)
    {j : Fin σ.toTorus.pairing.count} (b : Bool) (hj : j ∉ σ.prot)
    (hk : σ.kind (σ.seamPiece j b) = 1) : σ.kind (σ.hostPiece j b) = 3 := by
  have hm := σ.kind_mem (σ.hostPiece j b) (σ.hostPiece_not_mem_frozen hj b)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have h1 := σ.inner_solid_host_not_one hInc hp b hj hk
  have h2 := σ.terminal_inner_solid_host_ne_two ht b hj hk
  omega

end GC.Seifert.RelativeNormalization.MixedStage
