import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PresentationUniverseLift
import DifferentialGeometry.Topology.Attachment.BoundaryGluing

/-!
# Actual boundary gluing under a universe lift

The faces are literal down preimages and the attaching homeomorphisms are conjugated
by the actual face restrictions. The same up/down maps descend to a quotient homeomorphism
with an exact quotient representative square.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.Topology

universe u

namespace GC.GraphManifold.RawUniverseLift

variable {X : Type} [topX : TopologicalSpace X] {n : ℕ}

abbrev boundarySetDown (S : Set X) : (ULift.down ⁻¹' S : Set (ULift.{u} X)) ≃ₜ S :=
  setDown S

def boundaryGluing (G : BoundaryGluing X (Fin n)) : BoundaryGluing (ULift.{u} X) (Fin n) where
  left i := ULift.down ⁻¹' G.left i
  right i := ULift.down ⁻¹' G.right i
  attaching i := ((boundarySetDown (G.left i)).trans (G.attaching i)).trans
    (boundarySetDown (G.right i)).symm
  isClosed_left i := (G.isClosed_left i).preimage continuous_uliftDown
  isClosed_right i := (G.isClosed_right i).preimage continuous_uliftDown
  disjoint_left_right i := (G.disjoint_left_right i).preimage ULift.down
  disjoint_blocks i j hij := by
    exact (G.disjoint_blocks i j hij).preimage ULift.down

theorem boundaryGluing_left (G : BoundaryGluing X (Fin n)) (i : Fin n) :
    (boundaryGluing.{u} G).left i = ULift.down ⁻¹' G.left i := rfl

theorem boundaryGluing_right (G : BoundaryGluing X (Fin n)) (i : Fin n) :
    (boundaryGluing.{u} G).right i = ULift.down ⁻¹' G.right i := rfl

theorem boundaryGluing_attaching_down (G : BoundaryGluing X (Fin n)) (i : Fin n)
    (x : (boundaryGluing.{u} G).left i) :
    ((boundaryGluing.{u} G).attaching i x).val.down =
      (G.attaching i (boundarySetDown (G.left i) x)).val := rfl

private theorem boundaryGluing_flip_down (G : BoundaryGluing X (Fin n)) (i : Fin n)
    (x : ULift.{u} X) : ((boundaryGluing G).flip i x).down = G.flip i x.down := by
  classical
  by_cases hl : x.down ∈ G.left i
  · rw [(boundaryGluing G).flip_of_mem_left hl, G.flip_of_mem_left hl]
    rfl
  · by_cases hr : x.down ∈ G.right i
    · rw [(boundaryGluing G).flip_of_mem_right hr, G.flip_of_mem_right hr]
      rfl
    · rw [(boundaryGluing G).flip_of_notMem (fun h => h.elim hl hr),
        G.flip_of_notMem (fun h => h.elim hl hr)]

theorem boundaryGluing_rel_down {G : BoundaryGluing X (Fin n)} {x y : ULift.{u} X} :
    (boundaryGluing G).rel x y ↔ G.rel x.down y.down := by
  change (x = y ∨ ∃ i, x.down ∈ G.block i ∧ y = (boundaryGluing G).flip i x) ↔
    (x.down = y.down ∨ ∃ i, x.down ∈ G.block i ∧ y.down = G.flip i x.down)
  constructor
  · rintro (hxy | ⟨i, hx, hy⟩)
    · exact Or.inl (congrArg ULift.down hxy)
    · exact Or.inr ⟨i, hx, by rw [hy, boundaryGluing_flip_down]⟩
  · rintro (hxy | ⟨i, hx, hy⟩)
    · exact Or.inl (ULift.ext hxy)
    · exact Or.inr ⟨i, hx, ULift.ext (hy.trans (boundaryGluing_flip_down G i x).symm)⟩

theorem boundaryGluing_rel_up {G : BoundaryGluing X (Fin n)} {x y : X} :
    (boundaryGluing.{u} G).rel (ULift.up x) (ULift.up y) ↔ G.rel x y :=
  boundaryGluing_rel_down

def quotientDown (G : BoundaryGluing X (Fin n)) :
    Quotient (boundaryGluing.{u} G).setoid ≃ₜ Quotient G.setoid :=
  (boundaryGluing G).congrHomeomorph G Homeomorph.ulift
    (fun x y => boundaryGluing_rel_down (x := x) (y := y))

theorem quotientDown_mk (G : BoundaryGluing X (Fin n)) (x : X) :
    quotientDown.{u} G (Quotient.mk (boundaryGluing G).setoid (ULift.up x)) =
      Quotient.mk G.setoid x := rfl

end GC.GraphManifold.RawUniverseLift
