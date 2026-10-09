import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerDescentJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube

/-!
# Draft 74, the whole-fibre patch of a corner

Lane S-JUNCTIONS (by S-JUNCTIONS3), G19 part 1 (suffix `_JN74`). For an actual endpoint `e` there
is an open patch `N ∋ rimBase e` of the circle base whose whole preimage lies in the edge source and
in the face neighbourhood of `horizontal e` (whole-tube shrinking, `exists_open_tube_subset_EFC`
along the closed circle projection; the rim fibre `rim e = fibre (rimBase e)` lies in the edge source
and in the face `horizontal_disk`):

* `SlimPiecesV2.residualSet_subset_residualNear_JN74`;
* **`exists_cornerPatch_JN74`**: the `hsrc` input of `cornerDescent_ofFibreConst_JN74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

/-- **A face lies in its neighbourhood.** -/
theorem residualSet_subset_residualNear_JN74 (F : S.ResidualFace) :
    S.residualSet F ⊆ (S.residualNear F : Set W.Carrier) := by
  rcases F with ⟨F | F, hF⟩ | e
  · rintro _ ⟨p, hp, rfl⟩
    have hb : (Z.piece F.1).map p ∈ pieceBoundary (Z.piece F.1) :=
      ⟨p, F.2.subset hp, rfl⟩
    have h0 : Z.ratio F.1 ((Z.piece F.1).map p) = 0 := by
      have := Z.boundary_eq F.1 ▸ hb
      exact this
    exact Z.zero_subset_near F.1 h0
  · obtain ⟨b, F', hF'⟩ := F
    subst hF'
    rintro _ ⟨p, hp, rfl⟩
    rw [C.internalModelFace_eq b] at hp
    obtain ⟨t, rfl⟩ := hp
    have h2 : (C.piece b).map (C.product b (t, iccEnd true)) ∈ range fun t =>
        (C.piece b).map (C.product b (t, iccEnd true)) := ⟨t, rfl⟩
    rw [C.internal_eq b] at h2
    exact h2.1
  · intro x hx
    have h := S.endFn_level e
    have hx' : x ∈ (S.piece e.1.1.1).map '' slimModelEnd (S.model e.1.1.1) e.1.1.2 := hx
    rw [h] at hx'
    exact hx'.1

end SlimPiecesV2

section Patch

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **The whole-fibre patch of a corner**: over an open patch `N ∋ rimBase e`, the whole preimage lies
in the edge source and in the face neighbourhood of `horizontal e`. -/
theorem exists_cornerPatch_JN74 (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R)
    (e : R.edge.EdgeEnd) :
    ∃ N : TopologicalSpace.Opens R.circle.Base, G.rimBase e.1 ∈ N ∧
      ∀ x : R.circle.domain, R.circle.proj x ∈ N → (x : W.Carrier) ∈ R.edge.source ∧
        (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e) := by
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  let U : Set W.Carrier := (R.edge.source : Set W.Carrier) ∩
    (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier)
  have hU : IsOpen U := R.edge.source.isOpen.inter (R.slimPieces.residualNear _).isOpen
  have hfib : R.circle.proj ⁻¹' {G.rimBase e.1} ⊆ (Subtype.val ⁻¹' U : Set R.circle.domain) := by
    intro x hx
    have hxf : (x : W.Carrier) ∈ R.circle.fibre (G.rimBase e.1) := ⟨x, hx, rfl⟩
    rw [← G.rim_fibre e.1 (R.edge.frontier_cbase_subset e.2)] at hxf
    obtain ⟨z, ⟨hzp, hzh⟩, hzx⟩ := hxf
    refine ⟨hzx ▸ z.2, ?_⟩
    have hd : (x : W.Carrier) ∈ R.edge.disk e.1 := ⟨z, ⟨hzp, le_of_eq hzh⟩, hzx⟩
    exact R.slimPieces.residualSet_subset_residualNear_JN74 (F.horizontal e)
      (F.horizontal_disk e hd)
  obtain ⟨V, hV, hbV, -, hVsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC hcl
    (N := (Subtype.val ⁻¹' U : Set R.circle.domain)) (hU.preimage continuous_subtype_val) hfib
    (V := Set.univ) isOpen_univ trivial
  exact ⟨⟨V, hV⟩, hbV, fun x hx => hVsub hx⟩

end Patch

end GC.GraphManifold.Assembly.FC39P0
