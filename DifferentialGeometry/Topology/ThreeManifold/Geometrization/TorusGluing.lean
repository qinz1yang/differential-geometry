import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.Attachment.BoundaryGluing
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

abbrev Torus := Circle × Circle
abbrev torusModel := (𝓡 1).prod (𝓡 1)
abbrev halfCollarModel := torusModel.prod (𝓡∂ 1)
abbrev signedCollarModel := torusModel.prod 𝓘(ℝ, ℝ)

def halfPoint (s : ℝ) (hs : 0 ≤ s) : EuclideanHalfSpace 1 :=
  ⟨WithLp.toLp 2 (fun _ => s), hs⟩

def halfZero : EuclideanHalfSpace 1 := halfPoint 0 le_rfl

def halfCollarSource : Set (Torus × EuclideanHalfSpace 1) :=
  {p | p.2.val 0 < 1}

def signedCollarSource : Set (Torus × ℝ) := {p | -1 < p.2 ∧ p.2 < 1}

structure TorusGluing (C : CompactCarrier.{u}) where
  count : ℕ
  gluing : BoundaryGluing C.Carrier (Fin count)
  leftParam : (i : Fin count) → Torus ≃ₜ gluing.left i
  rightParam : (i : Fin count) → Torus ≃ₜ gluing.right i
  matching : Fin count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  matching_eq : ∀ i t, gluing.attaching i (leftParam i t) = rightParam i (matching i t)
  torusOrientation : Fin count → ManifoldOrientation torusModel Torus 2
  leftCollar : Fin count →
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞
  rightCollar : Fin count →
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞
  left_source : ∀ i, (leftCollar i).source = halfCollarSource
  right_source : ∀ i, (rightCollar i).source = halfCollarSource
  left_zero : ∀ i t, leftCollar i (t, halfZero) = (leftParam i t).val
  right_zero : ∀ i t, rightCollar i (t, halfZero) = (rightParam i t).val
  boundary_exhausted : C.model.boundary C.Carrier = ⋃ i, gluing.block i

namespace TorusGluing
variable {C : CompactCarrier.{u}}

abbrev Assembled (G : TorusGluing C) := Quotient G.gluing.setoid

instance (G : TorusGluing C) : T2Space G.Assembled :=
  BoundaryGluing.instT2SpaceQuotient G.gluing

def quotientMap (G : TorusGluing C) : C(C.Carrier, G.Assembled) :=
  ⟨Quotient.mk'', continuous_quotient_mk'⟩

def torusMap (G : TorusGluing C) (i : Fin G.count) : C(Torus, G.Assembled) :=
  G.quotientMap.comp ⟨fun t => (G.leftParam i t).val,
    continuous_subtype_val.comp (G.leftParam i).continuous⟩

theorem quotientMap_eq_iff (G : TorusGluing C) (x y : C.Carrier) :
    G.quotientMap x = G.quotientMap y ↔ G.gluing.rel x y := Quotient.eq'

theorem matched_sides_equal (G : TorusGluing C) (i : Fin G.count) (t : Torus) :
    G.quotientMap (G.leftParam i t) = G.quotientMap (G.rightParam i (G.matching i t)) := by
  rw [← G.matching_eq]
  exact Quotient.sound' (G.gluing.rel_of_mem_left (G.leftParam i t).property)

theorem interior_fiber_singleton (G : TorusGluing C) {x y : C.Carrier}
    (hx : C.model.IsInteriorPoint x) (h : G.quotientMap x = G.quotientMap y) : x = y := by
  apply G.gluing.eq_of_rel_of_notMem _ ((G.quotientMap_eq_iff x y).mp h)
  intro i hi
  have hb : x ∈ C.model.boundary C.Carrier := by
    rw [G.boundary_exhausted]
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  exact C.model.disjoint_interior_boundary.le_bot ⟨hx, hb⟩

theorem related_mem_block (G : TorusGluing C) (i : Fin G.count) {x y : C.Carrier}
    (hx : x ∈ G.gluing.block i) (h : G.gluing.rel x y) : y ∈ G.gluing.block i := by
  rcases h with rfl | ⟨j, hxj, rfl⟩
  · exact hx
  · have hij : i = j := by
      by_contra hij
      exact (G.gluing.disjoint_blocks i j hij).le_bot ⟨hx, hxj⟩
    subst j
    exact G.gluing.flip_mem_block hx

theorem torusMap_injective (G : TorusGluing C) (i : Fin G.count) :
    Function.Injective (G.torusMap i) := by
  intro t s h
  have hr := (G.quotientMap_eq_iff (G.leftParam i t) (G.leftParam i s)).mp h
  rcases hr with h | ⟨j, hx, hy⟩
  · exact (G.leftParam i).injective (Subtype.ext h)
  · have hij : i = j := by
      by_contra hij
      exact (G.gluing.disjoint_blocks i j hij).le_bot
        ⟨Or.inl (G.leftParam i t).property, hx⟩
    subst j
    have hyR : (G.leftParam i s).val ∈ G.gluing.right i := by
      rw [hy, G.gluing.flip_of_mem_left (G.leftParam i t).property]
      exact (G.gluing.attaching i (G.leftParam i t)).property
    exact ((G.gluing.disjoint_left_right i).le_bot
      ⟨(G.leftParam i s).property, hyR⟩).elim

theorem torusMap_pairwise_disjoint (G : TorusGluing C) :
    Pairwise (fun i j => Disjoint (Set.range (G.torusMap i)) (Set.range (G.torusMap j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro q ⟨t, rfl⟩ ⟨s, hs⟩
  have hr := (G.quotientMap_eq_iff (G.leftParam i t) (G.leftParam j s)).mp hs.symm
  have hb := G.related_mem_block i (Or.inl (G.leftParam i t).property) hr
  exact (G.gluing.disjoint_blocks i j hij).le_bot
    ⟨hb, Or.inl (G.leftParam j s).property⟩

theorem torusMap_isEmbedding (G : TorusGluing C) (i : Fin G.count) :
    _root_.Topology.IsEmbedding (G.torusMap i) :=
  ((G.torusMap i).continuous.isClosedEmbedding (G.torusMap_injective i)).isEmbedding

theorem boundary_maps_to_torus (G : TorusGluing C) {x : C.Carrier}
    (hx : C.model.IsBoundaryPoint x) :
    ∃ i t, G.quotientMap x = G.torusMap i t := by
  have hx' : x ∈ ⋃ i, G.gluing.block i := G.boundary_exhausted ▸ hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
  rcases hi with hl | hr
  · refine ⟨i, (G.leftParam i).symm ⟨x, hl⟩, ?_⟩
    change G.quotientMap x = G.quotientMap ((G.leftParam i) ((G.leftParam i).symm ⟨x, hl⟩)).val
    rw [Homeomorph.apply_symm_apply]
  · let b := (G.gluing.attaching i).symm ⟨x, hr⟩
    refine ⟨i, (G.leftParam i).symm b, ?_⟩
    change G.quotientMap x = G.quotientMap ((G.leftParam i) ((G.leftParam i).symm b)).val
    rw [Homeomorph.apply_symm_apply]
    have h : G.quotientMap (G.gluing.attaching i b) = G.quotientMap b :=
      Quotient.sound' (G.gluing.rel_of_attaching i b)
    simpa only [b, Homeomorph.apply_symm_apply] using h

theorem interior_or_torus (G : TorusGluing C) (q : G.Assembled) :
    (∃ x : C.interior, G.quotientMap x.val = q) ∨ ∃ i t, G.torusMap i t = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    by_cases hx : C.model.IsInteriorPoint x
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · obtain ⟨i, t, ht⟩ := G.boundary_maps_to_torus
        ((C.model.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx)
      exact Or.inr ⟨i, t, ht.symm⟩

def descend (G : TorusGluing C) {Y : Type*} (f : C.Carrier → Y)
    (hf : ∀ x y, G.gluing.rel x y → f x = f y) : G.Assembled → Y :=
  Quotient.lift f hf

@[simp] theorem descend_quotientMap (G : TorusGluing C) {Y : Type*}
    (f : C.Carrier → Y) (hf : ∀ x y, G.gluing.rel x y → f x = f y) (x : C.Carrier) :
    G.descend f hf (G.quotientMap x) = f x := rfl

theorem descend_unique (G : TorusGluing C) {Y : Type*} (f : C.Carrier → Y)
    (hf : ∀ x y, G.gluing.rel x y → f x = f y) (g : G.Assembled → Y)
    (hg : ∀ x, g (G.quotientMap x) = f x) : g = G.descend f hf := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact hg x

end TorusGluing
end GC.Endpoint
