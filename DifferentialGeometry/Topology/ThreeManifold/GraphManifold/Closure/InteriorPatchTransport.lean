import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusPresentation
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
Actual partial charts in a cut carrier's interior transport through its intrinsic reconstruction,
with their original source and literal quotient square retained.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u v w z

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

private def interiorPatchFold (x : T.cutCarrier.interior) :
    PartialDiffeomorph T.cutCarrier.model W.model T.cutCarrier.Carrier W.Carrier ∞ :=
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    T.cutCarrier.model T.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model T.interiorImage ⟨T.interiorDiffeomorph x⟩
  (a.symm.trans T.interiorDiffeomorph.toPartialDiffeomorph).trans b

private theorem interiorPatchFold_source (x : T.cutCarrier.interior) :
    (T.interiorPatchFold x).source = T.cutCarrier.interior := by
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    T.cutCarrier.model T.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model T.interiorImage ⟨T.interiorDiffeomorph x⟩
  ext y
  change ((y ∈ a.target ∧ a.symm y ∈ univ) ∧
    T.interiorDiffeomorph (a.symm y) ∈ b.source) ↔ y ∈ T.cutCarrier.interior
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target,
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source]
  simp only [mem_univ, and_true]
  rfl

private theorem interiorPatchFold_apply (x : T.cutCarrier.interior)
    (y : T.cutCarrier.Carrier) (hy : y ∈ T.cutCarrier.interior) :
    T.interiorPatchFold x y = T.cutMap y := by
  change (T.interiorDiffeomorph
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
      T.cutCarrier.model T.cutCarrier.interior ⟨x⟩).symm y)).val = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply]
  exact T.interior_map ⟨y, hy⟩

private theorem interiorPatchFold_interior (x : T.cutCarrier.interior) :
    (T.interiorPatchFold x).target ⊆ W.interior := by
  intro y hy
  let p := T.interiorPatchFold x
  have hx : p.symm y ∈ p.source := p.toPartialEquiv.map_target hy
  have hI : T.cutCarrier.model.IsInteriorPoint (p.symm y) := by
    rw [T.interiorPatchFold_source] at hx
    exact hx
  have hl := p.isLocalDiffeomorphAt T.cutCarrier.model W.model ∞ hx
  have hi := (hl.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp hI
  have heq : p.toPartialEquiv (p.symm.toPartialEquiv y) = y :=
    p.toPartialEquiv.right_inv hy
  exact heq ▸ hi

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {X : Type z} [TopologicalSpace X] [ChartedSpace H X]
  (p : PartialDiffeomorph I T.cutCarrier.model X T.cutCarrier.Carrier ∞)
  (x : X) (hx : x ∈ p.source) (hI : p.target ⊆ T.cutCarrier.interior)

def transportInteriorPatch : PartialDiffeomorph I W.model X W.Carrier ∞ :=
  p.trans (T.interiorPatchFold ⟨p x, hI (p.map_source hx)⟩)

theorem transportInteriorPatch_source :
    (T.transportInteriorPatch I p x hx hI).source = p.source := by
  ext y
  change (y ∈ p.source ∧ p y ∈
    (T.interiorPatchFold ⟨p x, hI (p.map_source hx)⟩).source) ↔ y ∈ p.source
  rw [T.interiorPatchFold_source]
  exact ⟨And.left, fun hy => ⟨hy, hI (p.map_source hy)⟩⟩

theorem transportInteriorPatch_apply (y : X) (hy : y ∈ p.source) :
    T.transportInteriorPatch I p x hx hI y = T.cutMap (p y) :=
  T.interiorPatchFold_apply ⟨p x, hI (p.map_source hx)⟩ (p y) (hI (p.map_source hy))

theorem transportInteriorPatch_interior :
    (T.transportInteriorPatch I p x hx hI).target ⊆ W.interior := by
  intro y hy
  exact T.interiorPatchFold_interior ⟨p x, hI (p.map_source hx)⟩ hy.1

theorem transportInteriorPatch_image (A : Set X) (hA : A ⊆ p.source) :
    (T.transportInteriorPatch I p x hx hI) '' A = T.cutMap '' (p '' A) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨p a, ⟨a, ha, rfl⟩, (T.transportInteriorPatch_apply I p x hx hI a (hA ha)).symm⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, T.transportInteriorPatch_apply I p x hx hI a (hA ha)⟩

end GC.Seifert.TorusPresentation
