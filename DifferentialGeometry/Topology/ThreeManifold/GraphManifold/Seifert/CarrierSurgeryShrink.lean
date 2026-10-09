import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryQuotientAtlas

/-!
One common shrink separates every paired and retained half collar without changing the actual
cut carrier, quotient relation, matching maps, zero tori or retained external boundary image.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

theorem exists_surgeryCommonShrink (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (hd : Disjoint (⋃ j, P.gluing.block j) E.image) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      Pairwise (fun i j => Disjoint ((P.shrink hδ hδ1).surgerySideCollar i).target
        ((P.shrink hδ hδ1).surgerySideCollar j).target) ∧
      ∀ i j, Disjoint ((E.shrink hδ hδ1).collar i).target
        ((P.shrink hδ hδ1).surgerySideCollar j).target := by
  obtain ⟨δ, hδ, hδ1, hdis⟩ := P.exists_disjoint_surgeryBoundaryCollars E hd
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · intro i j hij
    have hh := hdis (Sum.inl_injective.ne hij)
    rcases i with i | i <;> rcases j with j | j <;> exact hh
  · intro i j
    have hh := hdis (Sum.inr_ne_inl : Sum.inr i ≠ Sum.inl j)
    rcases j with j | j <;> exact hh

theorem surgeryShrink_boundary (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image) :
    C.model.boundary C.Carrier =
      (⋃ j, (P.shrink hδ hδ1).gluing.block j) ∪ (E.shrink hδ hδ1).image := by
  rw [BoundaryTori.shrink_image]
  exact hb

theorem surgeryShrink_external_owned {n : ℕ} (E : BoundaryTori C n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (D : C.Components)
    (external : Fin n → Fin D.count)
    (he : ∀ i, range (E.torusMap i) ⊆ D.piece (external i)) :
    ∀ i, range ((E.shrink hδ hδ1).torusMap i) ⊆ D.piece (external i) := by
  intro i
  rw [BoundaryTori.shrink_torusMap]
  exact he i

end GC.GraphManifold.TorusPairing
