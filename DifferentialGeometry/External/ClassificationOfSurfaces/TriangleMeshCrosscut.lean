/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Adapted mesh-side arguments from PolygonalCrosscut.lean at
 e3c7230fe78d7b056a415d9ecae6f77887046b32 to native crosscuts and inside regions.
See MODIFICATIONS.md and CROSSCUT_PROVENANCE.json for the source and local changes.
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.FreeTriangle
import DifferentialGeometry.External.Schoenflies.JordanClosed

open LeanEval.Topology.ClassificationOfSurfaces.Moise (TriangleMesh)

namespace Schoenflies

private theorem interior_closure_inside_of_separating {C : Set Plane}
    (hC : IsSeparating C) : interior (closure (inside C)) = inside C := by
  have hd₀ : Disjoint (closure (inside C)) (outside C) :=
    disjoint_inside_outside.closure_left hC.isOpen_outside
  have hd : Disjoint (interior (closure (inside C))) (closure (outside C)) :=
    (hd₀.mono_left interior_subset).closure_right isOpen_interior
  apply Set.Subset.antisymm ?_ hC.isOpen_inside.subset_interior_closure
  intro x hx
  have hxC : x ∉ C := fun hxc => Set.disjoint_left.mp hd hx
    ((IsRegionOf.outside C).subset_closure hC hxc)
  have hxSplit : x ∈ inside C ∪ outside C := (inside_union_outside C).symm ▸ hxC
  exact hxSplit.resolve_right fun hxo => Set.disjoint_left.mp hd hx (subset_closure hxo)

variable (M : TriangleMesh) {C A₁ A₂ : Set Plane} {p q : Plane}
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    {e : Finset M.Vertex} (he : e ∈ M.edges)
    (hcarrier : convexHull ℝ (M.position '' (e : Set M.Vertex)) = segment ℝ p q)
    (h : IsCrosscut C (segment ℝ p q) p q) (hcut : IsCutPair C p q A₁ A₂)

include hsupport he hcarrier h hcut

/-- A mesh triangle lies wholly on one side of a realized crosscut. -/
private theorem triangle_interior_crosscut_side (T : M.Triangle) :
    interior (M.triangleCarrier T.1) ⊆ inside (A₁ ∪ segment ℝ p q) ∨
      interior (M.triangleCarrier T.1) ⊆ inside (A₂ ∪ segment ℝ p q) := by
  have htriangleSupport : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hinside : interior (M.triangleCarrier T.1) ⊆ inside C := by
    have hi := interior_mono htriangleSupport
    rw [hsupport, interior_closure_inside_of_separating (jordan_curve_theorem h.curve)] at hi
    exact hi
  have hdisjointChord : Disjoint (interior (M.triangleCarrier T.1)) (segment ℝ p q) := by
    rw [← hcarrier]
    exact M.disjoint_interior_triangleCarrier_edgeCarrier T he
  have hcross := crosscut_theorem h hcut
  have hsplit : interior (M.triangleCarrier T.1) ⊆
      inside (A₁ ∪ segment ℝ p q) ∪ inside (A₂ ∪ segment ℝ p q) := by
    intro x hx
    exact hcross.1 ▸ ⟨hinside hx, fun hxChord => Set.disjoint_left.mp hdisjointChord hx hxChord⟩
  have hopen₁ := (jordan_curve_theorem (h.isJordanCurve_union hcut)).isOpen_inside
  have hopen₂ := (jordan_curve_theorem (h.isJordanCurve_union hcut.symm)).isOpen_inside
  have hconnected : IsPreconnected (interior (M.triangleCarrier T.1)) :=
    (convex_convexHull ℝ (M.position '' (T.1 : Set M.Vertex))).interior.isPreconnected
  obtain ⟨x, hx⟩ := M.interior_triangleCarrier_nonempty T
  rcases hsplit hx with hx₁ | hx₂
  · exact Or.inl (hconnected.subset_left_of_subset_union
      hopen₁ hopen₂ hcross.2.1 hsplit ⟨x, hx, hx₁⟩)
  · exact Or.inr (hconnected.subset_right_of_subset_union
      hopen₁ hopen₂ hcross.2.1 hsplit ⟨x, hx, hx₂⟩)

private theorem triangle_interior_subset_crosscut_side_of_meet (T : M.Triangle)
    (hmeet : (interior (M.triangleCarrier T.1) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty) :
    interior (M.triangleCarrier T.1) ⊆ inside (A₁ ∪ segment ℝ p q) := by
  rcases triangle_interior_crosscut_side M hsupport he hcarrier h hcut T with h₁ | h₂
  · exact h₁
  · obtain ⟨x, hxT, hx₁⟩ := hmeet
    exact False.elim (Set.disjoint_left.mp (crosscut_theorem h hcut).2.1 hx₁ (h₂ hxT))

open scoped Classical in
/-- Restricting along a realized crosscut gives exactly the first closed polygonal subdisk. -/
private theorem restrict_triangles_crosscut_support :
    (M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty)).toPlaneComplex.support =
        closure (inside (A₁ ∪ segment ℝ p q)) := by
  classical
  let U := inside (A₁ ∪ segment ℝ p q)
  let f := fun t : Finset M.Vertex => (interior (M.triangleCarrier t) ∩ U).Nonempty
  let N := M.restrictTriangles f
  change N.toPlaneComplex.support = closure U
  have hNsupport : N.toPlaneComplex.support =
      ⋃ t ∈ M.triangles.filter f, M.triangleCarrier t := N.toPlaneComplex_support
  apply Set.Subset.antisymm
  · intro x hx
    rw [hNsupport] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨htM, hmeet⟩ := Finset.mem_filter.mp ht
    let T : M.Triangle := ⟨t, htM⟩
    have hside : interior (M.triangleCarrier t) ⊆ U :=
      triangle_interior_subset_crosscut_side_of_meet M hsupport he hcarrier h hcut T hmeet
    have hclosed := closure_mono hside
    rw [M.closure_interior_triangleCarrier T] at hclosed
    exact hclosed hxt
  · apply closure_minimal _ N.toPlaneComplex.isCompact_support.isClosed
    intro x hx
    have hxC : x ∈ inside C :=
      (h.side_subset (fun _ hJ => jordan_curve_theorem hJ) hcut hx).1
    have hxSupport : x ∈ M.toPlaneComplex.support := hsupport.symm ▸ subset_closure hxC
    rw [M.toPlaneComplex_support] at hxSupport
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxSupport
    let T : M.Triangle := ⟨t, ht⟩
    have hxClosure : x ∈ closure (interior (M.triangleCarrier t)) :=
      (M.closure_interior_triangleCarrier T).symm ▸ hxt
    have hopen : IsOpen U := (jordan_curve_theorem (h.isJordanCurve_union hcut)).isOpen_inside
    have hxInter : x ∈ closure (U ∩ interior (M.triangleCarrier t)) :=
      hopen.inter_closure ⟨hx, hxClosure⟩
    obtain ⟨y, hyU, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxInter⟩
    have hmeet : f t := ⟨y, hyt, hyU⟩
    rw [hNsupport]
    exact Set.mem_iUnion₂.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hmeet⟩, hxt⟩

open scoped Classical in
/-- The two restricted triangle sets partition the original mesh.
No maximal triangle occurs on both sides of the crosscut.
Each side of a proper realized crosscut has strictly fewer maximal triangles. -/
theorem restrict_triangles_crosscut_partition :
    let N₁ := M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty)
    let N₂ := M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₂ ∪ segment ℝ p q)).Nonempty)
    N₁.toPlaneComplex.support = closure (inside (A₁ ∪ segment ℝ p q)) ∧
      N₂.toPlaneComplex.support = closure (inside (A₂ ∪ segment ℝ p q)) ∧
      N₁.triangles ∪ N₂.triangles = M.triangles ∧ Disjoint N₁.triangles N₂.triangles ∧
      N₁.triangles.Nonempty ∧ N₂.triangles.Nonempty ∧
      N₁.triangles.card < M.triangles.card ∧ N₂.triangles.card < M.triangles.card := by
  classical
  let U₁ := inside (A₁ ∪ segment ℝ p q)
  let U₂ := inside (A₂ ∪ segment ℝ p q)
  let f₁ := fun t : Finset M.Vertex => (interior (M.triangleCarrier t) ∩ U₁).Nonempty
  let f₂ := fun t : Finset M.Vertex => (interior (M.triangleCarrier t) ∩ U₂).Nonempty
  let N₁ := M.restrictTriangles f₁
  let N₂ := M.restrictTriangles f₂
  let F₁ := M.triangles.filter f₁
  let F₂ := M.triangles.filter f₂
  have hs₁ : N₁.toPlaneComplex.support = closure U₁ :=
    restrict_triangles_crosscut_support M hsupport he hcarrier h hcut
  have hs₂ : N₂.toPlaneComplex.support = closure U₂ :=
    restrict_triangles_crosscut_support M hsupport he hcarrier h hcut.symm
  refine ⟨hs₁, hs₂, ?_⟩
  change F₁ ∪ F₂ = M.triangles ∧ Disjoint F₁ F₂ ∧ F₁.Nonempty ∧ F₂.Nonempty ∧
    F₁.card < M.triangles.card ∧ F₂.card < M.triangles.card
  have hmember₁ (t : Finset M.Vertex) : t ∈ F₁ ↔ t ∈ M.triangles ∧ f₁ t :=
    Finset.mem_filter
  have hmember₂ (t : Finset M.Vertex) : t ∈ F₂ ↔ t ∈ M.triangles ∧ f₂ t :=
    Finset.mem_filter
  have hunion : F₁ ∪ F₂ = M.triangles := by
    apply Finset.ext
    intro t
    constructor
    · intro ht
      rcases Finset.mem_union.mp ht with ht₁ | ht₂
      · exact (hmember₁ t).mp ht₁ |>.1
      · exact (hmember₂ t).mp ht₂ |>.1
    · intro ht
      let T : M.Triangle := ⟨t, ht⟩
      obtain ⟨x, hx⟩ := M.interior_triangleCarrier_nonempty T
      rcases triangle_interior_crosscut_side M hsupport he hcarrier h hcut T with h₁ | h₂
      · exact Finset.mem_union_left _ ((hmember₁ t).mpr ⟨ht, x, hx, h₁ hx⟩)
      · exact Finset.mem_union_right _ ((hmember₂ t).mpr ⟨ht, x, hx, h₂ hx⟩)
  have hdisjoint : Disjoint F₁ F₂ := by
    apply Finset.disjoint_left.mpr
    intro t ht₁ ht₂
    obtain ⟨htM, hmeet₁⟩ := (hmember₁ t).mp ht₁
    have hmeet₂ := (hmember₂ t).mp ht₂ |>.2
    let T : M.Triangle := ⟨t, htM⟩
    have hside := triangle_interior_subset_crosscut_side_of_meet
      M hsupport he hcarrier h hcut T hmeet₁
    obtain ⟨x, hxT, hx₂⟩ := hmeet₂
    exact Set.disjoint_left.mp (crosscut_theorem h hcut).2.1 (hside hxT) hx₂
  have hn₁ : F₁.Nonempty := by
    obtain ⟨x, hx⟩ := (crosscut_theorem h hcut).2.2.1
    have hxN : x ∈ N₁.toPlaneComplex.support := hs₁.symm ▸ subset_closure hx
    have hs : N₁.toPlaneComplex.support = ⋃ t ∈ F₁, M.triangleCarrier t :=
      N₁.toPlaneComplex_support
    rw [hs] at hxN
    obtain ⟨t, ht, _⟩ := Set.mem_iUnion₂.mp hxN
    exact ⟨t, ht⟩
  have hn₂ : F₂.Nonempty := by
    obtain ⟨x, hx⟩ := (crosscut_theorem h hcut).2.2.2.1
    have hxN : x ∈ N₂.toPlaneComplex.support := hs₂.symm ▸ subset_closure hx
    have hs : N₂.toPlaneComplex.support = ⋃ t ∈ F₂, M.triangleCarrier t :=
      N₂.toPlaneComplex_support
    rw [hs] at hxN
    obtain ⟨t, ht, _⟩ := Set.mem_iUnion₂.mp hxN
    exact ⟨t, ht⟩
  have hcard : F₁.card + F₂.card = M.triangles.card :=
    (Finset.card_union_of_disjoint hdisjoint).symm.trans (congrArg Finset.card hunion)
  have hpos₁ := Finset.card_pos.mpr hn₁
  have hpos₂ := Finset.card_pos.mpr hn₂
  exact ⟨hunion, hdisjoint, hn₁, hn₂, by omega, by omega⟩

end Schoenflies
