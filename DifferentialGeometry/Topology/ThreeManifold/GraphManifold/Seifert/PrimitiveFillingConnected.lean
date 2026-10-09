import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PrimitiveFillingData

/-!
# Connectivity of an actual primitive filling

Every filling solid meets the host along its actual seam in the reconstructed carrier. The
finite union of these connected images is the whole carrier. Connectivity therefore follows
from the filling presentation, without a separate connectedness hypothesis on the output.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert.PrimitiveFillingPresentation

variable {W : CompactCarrier.{u}} {n r : ℕ} (B : PrimitiveFillingPresentation W n r)

theorem left_piece (m : Fin n) :
    B.presentation.leftPiece (B.seam m) = B.piece (some m) := by
  have h := ((B.solid m).port 0).property
  rw [B.solid_port] at h
  exact h

theorem right_piece (m : Fin n) : B.presentation.rightPiece (B.seam m) = B.piece none := by
  have h := (B.product.port (B.port (.inr m))).property
  rw [B.filled_port] at h
  exact h

theorem external_piece (a : Fin r) :
    B.presentation.externalPiece (B.free a) = B.piece none := by
  have h := (B.product.port (B.port (.inl a))).property
  rw [B.free_port] at h
  exact h

include B in
theorem connectedSpace : ConnectedSpace W.Carrier := by
  let T := B.presentation
  have hcut : Continuous T.cutMap := T.quotient_smooth.continuous
  let I : Option (Fin n) → Set W.Carrier := fun i =>
    T.cutMap '' (T.components.piece (B.piece i) : Set T.cutCarrier.Carrier)
  have hI (i : Option (Fin n)) : IsConnected (I i) :=
    (isConnected_iff_connectedSpace.mpr (T.components.connected (B.piece i))).image _
      hcut.continuousOn
  obtain ⟨z, hz⟩ := (hI none).nonempty
  have hmeet (i : Option (Fin n)) : (I none ∩ I i).Nonempty := by
    cases i with
    | none => exact ⟨z, hz, hz⟩
    | some m =>
      let j := B.seam m
      let t : Torus := 1
      have hl : (T.pairing.leftParam j t).val ∈ T.components.piece (B.piece (some m)) := by
        rw [← B.left_piece m]
        exact T.left_owned j (T.pairing.leftParam j t).property
      have hr : (T.pairing.rightParam j (T.pairing.matching j t)).val ∈
          T.components.piece (B.piece none) := by
        rw [← B.right_piece m]
        exact T.right_owned j (T.pairing.rightParam j (T.pairing.matching j t)).property
      have he : T.cutMap (T.pairing.leftParam j t).val =
          T.cutMap (T.pairing.rightParam j (T.pairing.matching j t)).val := by
        apply congrArg T.reconstruction
        change T.pairing.quotientMap (T.pairing.leftParam j t) =
          T.pairing.quotientMap (T.pairing.rightParam j (T.pairing.matching j t))
        rw [← T.pairing.matching_eq]
        exact Quotient.sound
          (T.pairing.gluing.rel_of_mem_left (T.pairing.leftParam j t).property)
      exact ⟨T.cutMap (T.pairing.leftParam j t).val,
        ⟨(T.pairing.rightParam j (T.pairing.matching j t)).val, hr, he.symm⟩,
        ⟨(T.pairing.leftParam j t).val, hl, rfl⟩⟩
  have hu : (⋃ i : Option (Fin n), I none ∪ I i) = univ := by
    apply eq_univ_of_forall
    intro w
    obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm w)
    have hw : T.cutMap x = w := by
      change T.reconstruction (Quotient.mk _ x) = w
      rw [hx, Homeomorph.apply_symm_apply]
    have hx' : x ∈ ⋃ i, (T.components.piece i : Set T.cutCarrier.Carrier) := by
      rw [T.components.covers]
      exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    apply mem_iUnion.mpr
    refine ⟨B.piece.symm i, Or.inr ?_⟩
    exact ⟨x, by simpa only [Equiv.apply_symm_apply] using hi, hw⟩
  apply connectedSpace_iff_univ.mpr
  refine ⟨⟨z, mem_univ z⟩, ?_⟩
  rw [← hu]
  exact isPreconnected_iUnion ⟨z, mem_iInter.mpr fun i => Or.inl hz⟩ fun i =>
    (hI none).isPreconnected.union' (hmeet i) (hI i).isPreconnected

end GC.Seifert.PrimitiveFillingPresentation
