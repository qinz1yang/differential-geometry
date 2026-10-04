import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.InteriorPatchTransport

/-!
Actual component charts transport through their clopen inclusion and the original reconstruction,
keeping the same partial chart source and literal component inclusion square.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u v w z

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (i : Fin T.components.count) (D : CompactCarrier.{u})
  (e : D.Carrier ≃ₘ⟮D.model,
    (GC.Topology.componentCarrier T.cutCarrier T.components i).model⟯
    (GC.Topology.componentCarrier T.cutCarrier T.components i).Carrier)

private def componentPatchInclusion (d : D.Carrier) :
    PartialDiffeomorph D.model T.cutCarrier.model D.Carrier T.cutCarrier.Carrier ∞ :=
  e.toPartialDiffeomorph.trans (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    T.cutCarrier.model (T.components.piece i) ⟨e d⟩)

private theorem componentPatchInclusion_source (d : D.Carrier) :
    (T.componentPatchInclusion i D e d).source = univ := by
  ext y
  change (y ∈ (Set.univ : Set D.Carrier) ∧
    e y ∈ (Set.univ : Set (T.components.piece i))) ↔ y ∈ Set.univ
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ (e y)⟩⟩

private theorem componentPatchInclusion_apply (d y : D.Carrier) :
    T.componentPatchInclusion i D e d y = (e y).val := rfl

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {X : Type z} [TopologicalSpace X] [ChartedSpace H X]
  (p : PartialDiffeomorph I D.model X D.Carrier ∞)
  (x : X) (hx : x ∈ p.source) (hI : p.target ⊆ D.interior)

private def componentInteriorPatch :
    PartialDiffeomorph I T.cutCarrier.model X T.cutCarrier.Carrier ∞ :=
  p.trans (T.componentPatchInclusion i D e (p x))

private theorem componentInteriorPatch_source :
    (T.componentInteriorPatch i D e I p x).source = p.source := by
  ext y
  change (y ∈ p.source ∧ p y ∈ (T.componentPatchInclusion i D e (p x)).source) ↔ _
  rw [T.componentPatchInclusion_source]
  simp

include hI in
private theorem componentInteriorPatch_interior :
    (T.componentInteriorPatch i D e I p x).target ⊆ T.cutCarrier.interior := by
  intro y hy
  let r := T.componentPatchInclusion i D e (p x)
  have hr : r.symm y ∈ r.source := r.toPartialEquiv.map_target hy.1
  have hi : D.model.IsInteriorPoint (r.symm y) := hI hy.2
  have hl := r.isLocalDiffeomorphAt D.model T.cutCarrier.model ∞ hr
  have ht := (hl.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp hi
  have heq : r.toPartialEquiv (r.symm.toPartialEquiv y) = y :=
    r.toPartialEquiv.right_inv hy.1
  exact heq ▸ ht

def transportComponentPatch : PartialDiffeomorph I W.model X W.Carrier ∞ :=
  T.transportInteriorPatch I (T.componentInteriorPatch i D e I p x) x
    ((T.componentInteriorPatch_source i D e I p x).symm.subset hx)
    (T.componentInteriorPatch_interior i D e I p x hI)

theorem transportComponentPatch_source :
    (T.transportComponentPatch i D e I p x hx hI).source = p.source :=
  (T.transportInteriorPatch_source I (T.componentInteriorPatch i D e I p x) x
    ((T.componentInteriorPatch_source i D e I p x).symm.subset hx)
    (T.componentInteriorPatch_interior i D e I p x hI)).trans
    (T.componentInteriorPatch_source i D e I p x)

theorem transportComponentPatch_apply (y : X) (hy : y ∈ p.source) :
    T.transportComponentPatch i D e I p x hx hI y = T.cutMap (e (p y)).val := by
  exact T.transportInteriorPatch_apply I (T.componentInteriorPatch i D e I p x) x
    ((T.componentInteriorPatch_source i D e I p x).symm.subset hx)
    (T.componentInteriorPatch_interior i D e I p x hI) y
    ((T.componentInteriorPatch_source i D e I p x).symm.subset hy)

theorem transportComponentPatch_interior :
    (T.transportComponentPatch i D e I p x hx hI).target ⊆ W.interior :=
  T.transportInteriorPatch_interior I (T.componentInteriorPatch i D e I p x) x
    ((T.componentInteriorPatch_source i D e I p x).symm.subset hx)
    (T.componentInteriorPatch_interior i D e I p x hI)

theorem transportComponentPatch_image (A : Set X) (hA : A ⊆ p.source) :
    (T.transportComponentPatch i D e I p x hx hI) '' A =
      T.cutMap '' ((fun y => (e (p y)).val) '' A) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(e (p a)).val, ⟨a, ha, rfl⟩,
      (T.transportComponentPatch_apply i D e I p x hx hI a (hA ha)).symm⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, T.transportComponentPatch_apply i D e I p x hx hI a (hA ha)⟩

end GC.Seifert.TorusPresentation
