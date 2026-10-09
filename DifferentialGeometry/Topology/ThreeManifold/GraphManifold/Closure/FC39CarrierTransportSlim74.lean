import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportCusp74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportCircle74

/-!
# Draft 74, D74-6: transport of the slim pieces (closes the "pieces / bundles" half)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G22. `SlimPiecesV2.mapCarrier74 e S :
SlimPiecesV2 W₁ (Z.mapCarrier74 e) (C.mapCarrier74 e)`: pieces `e ∘ (piece j).map`, models by the
tree's `SlimModel.ofMap` (interval / circle branches kept: the circle branch `overCircle` and its
monodromy are untouched), ends / end faces / end kinds read through the end equivalence
`slimEndOfMap74` (interval models stay interval models, `slimModelIsInterval_mapCarrier74`, with
the same end slices, `slimModelEnd_mapCarrier74`; `SlimModel.mapCarrier74` = the tree's `ofMap`),
end defining functions `endFn ∘ e⁻¹` on `e(endNear)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- A slim model of a piece, carried to the transported piece (the tree's `SlimModel.ofMap`). -/
def _root_.GC.GraphManifold.Assembly.SlimModel.mapCarrier74
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {P : PieceEmbedding W₀} (m : SlimModel P) : SlimModel (P.mapCarrier74 e) :=
  m.ofMap

/-- The transported slim model keeps the interval / circle shape. -/
theorem slimModelIsInterval_mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {P : PieceEmbedding W₀} {m : SlimModel P} :
    slimModelIsInterval (m.mapCarrier74 e) ↔ slimModelIsInterval m := by
  cases m <;> exact Iff.rfl

/-- The transported slim model keeps the end slices. -/
theorem slimModelEnd_mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {P : PieceEmbedding W₀} (m : SlimModel P) (b : Bool) :
    slimModelEnd (m.mapCarrier74 e) b = slimModelEnd m b := by
  cases m <;> rfl

/-- The ends of the transported slim models are the ends of the original ones. -/
def slimEndOfMap74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) {count : ℕ}
    {piece : Fin count → PieceEmbedding W₀} (model : ∀ j, SlimModel (piece j))
    (x : SlimEnd (fun j => (model j).mapCarrier74 e)) : SlimEnd model :=
  ⟨x.1, (slimModelIsInterval_mapCarrier74 e (m := model x.1.1)).mp x.2⟩

/-- **The slim pieces transported along `e`** (onto the transported zero domains and cusp
cores). -/
def SlimPiecesV2.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) :
    SlimPiecesV2 W₁ (Z.mapCarrier74 e) (C.mapCarrier74 e) where
  count := S.count
  piece j := (S.piece j).mapCarrier74 e
  model j := (S.model j).mapCarrier74 e
  disjoint j j' hjj' := by
    change Disjoint (range ((S.piece j).mapCarrier74 e).map)
      (range ((S.piece j').mapCarrier74 e).map)
    rw [PieceEmbedding.range_mapCarrier74, PieceEmbedding.range_mapCarrier74]
    exact (disjoint_image_iff e.injective).mpr (S.disjoint hjj')
  endFace x := S.endFace (slimEndOfMap74 e S.model x)
  endFace_eq x := by
    rw [S.endFace_eq, slimModelEnd_mapCarrier74]
    rfl
  endFace_exhausted j F := by
    obtain ⟨b, h, hF⟩ := S.endFace_exhausted j F
    exact ⟨b, (slimModelIsInterval_mapCarrier74 e (m := S.model j)).mpr h, hF⟩
  endKind x := S.endKind (slimEndOfMap74 e S.model x)
  endFn x := S.endFn ⟨slimEndOfMap74 e S.model x.1, x.2⟩ ∘ e.symm
  endNear x := e.imageOpens74 (S.endNear ⟨slimEndOfMap74 e S.model x.1, x.2⟩)
  endNear_interior x := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono (S.endNear_interior _)
  endFn_smooth x := (S.endFn_smooth _).comp e.symm.contMDiff.contMDiffOn fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    change e.symm (e z) ∈ S.endNear _
    rw [e.symm_apply_apply]
    exact hz
  endFn_regular x y hy h0 := by
    obtain ⟨z, hz, rfl⟩ := hy
    have hz0 : S.endFn ⟨slimEndOfMap74 e S.model x.1, x.2⟩ z = 0 := by
      change S.endFn _ (e.symm (e z)) = 0 at h0
      rwa [e.symm_apply_apply] at h0
    have hd : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ)
        (S.endFn ⟨slimEndOfMap74 e S.model x.1, x.2⟩) z :=
      ((S.endFn_smooth _ z hz).contMDiffAt ((S.endNear _).isOpen.mem_nhds hz)).mdifferentiableAt
        (by simp)
    refine mfderiv_comp_symm_ne_zero_at_R74 e ?_ ?_
    · rw [e.symm_apply_apply]
      exact hd
    · rw [e.symm_apply_apply]
      exact S.endFn_regular _ z hz hz0
  endFn_level x := by
    have h := S.endFn_level ⟨slimEndOfMap74 e S.model x.1, x.2⟩
    have hA := (image_setOf_R74 e (S.endNear ⟨slimEndOfMap74 e S.model x.1, x.2⟩)
      (S.endFn ⟨slimEndOfMap74 e S.model x.1, x.2⟩) (fun r => r = 0)).trans
      (congrArg (fun s => e '' s) h.symm)
    refine Eq.trans ?_ hA.symm
    rw [slimModelEnd_mapCarrier74]
    exact image_comp e _ _
  endFn_eq x := by
    have h := S.endFn_eq ⟨slimEndOfMap74 e S.model x.1, x.2⟩
    have hA := (image_setOf_R74 e (S.endNear ⟨slimEndOfMap74 e S.model x.1, x.2⟩)
      (S.endFn ⟨slimEndOfMap74 e S.model x.1, x.2⟩) (fun r => r ≤ 0)).trans
      (congrArg (fun s => e '' s) h.symm)
    refine Eq.trans ?_ hA.symm
    change range (e ∘ (S.piece x.1.1.1).map) ∩
        e '' (S.endNear ⟨slimEndOfMap74 e S.model x.1, x.2⟩ : Set W₀.Carrier) = _
    rw [range_comp, image_inter (f := (e : W₀.Carrier → W₁.Carrier)) e.injective]
    rfl

/-- The transported slim union is the image of the slim union (`M^slim_W = e(M^slim)`). -/
theorem SlimPiecesV2.mapCarrier74_union (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) :
    (S.mapCarrier74 e).union = e '' S.union := by
  rw [SlimPiecesV2.union, SlimPiecesV2.union, image_iUnion]
  exact iUnion_congr fun j => PieceEmbedding.range_mapCarrier74 e (S.piece j)

end GC.GraphManifold.Assembly.FC39P0
