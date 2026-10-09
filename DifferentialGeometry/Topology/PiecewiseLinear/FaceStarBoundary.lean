/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem mem_faceStarComplex_faces_of_subset (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (ht : t ∈ K.faces) (hst : s ⊆ t) :
    t ∈ (faceStarComplex K s).faces :=
  ⟨ht, (Finset.union_eq_left.mpr hst).symm ▸ ht⟩

def faceAvoidingUnion (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) : Set E :=
  ⋃ t ∈ {t ∈ K.faces | ¬s ⊆ t}, convexHull ℝ (t : Set E)

theorem isClosed_faceAvoidingUnion (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (s : Finset E) : IsClosed (faceAvoidingUnion K s) :=
  ((Set.toFinite K.faces).subset (Set.sep_subset _ _)).isClosed_biUnion fun t _ =>
    (t.finite_toSet.isCompact_convexHull ℝ).isClosed

open Classical in
theorem faceAvoidingUnion_inter_convexHull
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E} (ht : t ∈ K.faces) :
    faceAvoidingUnion K s ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E) := by
  ext x
  constructor
  · rintro ⟨hxA, hxt⟩
    obtain ⟨u, ⟨hu, hsu⟩, hxu⟩ := mem_iUnion₂.mp hxA
    obtain ⟨v, hvs, hvu⟩ := Finset.not_subset.mp hsu
    have hxut : x ∈ convexHull ℝ (((u ∩ t : Finset E) : Set E)) := by
      rw [Finset.coe_inter]
      exact K.inter_subset_convexHull hu ht ⟨hxu, hxt⟩
    refine mem_iUnion₂.mpr ⟨v, hvs, convexHull_mono ?_ hxut⟩
    exact Finset.coe_subset.mpr fun w hw =>
      Finset.mem_erase.mpr ⟨fun hwv => hvu (hwv ▸ (Finset.mem_inter.mp hw).1),
        (Finset.mem_inter.mp hw).2⟩
  · intro hx
    obtain ⟨v, hvs, hxv⟩ := mem_iUnion₂.mp hx
    have hne : (t.erase v).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty, convexHull_empty] at hxv
      exact hxv
    have hface : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset v t) hne
    refine ⟨mem_iUnion₂.mpr ⟨t.erase v, ⟨hface, ?_⟩, hxv⟩,
      convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v t)) hxv⟩
    intro hsub
    exact Finset.notMem_erase v t (hsub hvs)

open Classical in
theorem space_sdiff_faceAvoidingUnion_subset_faceStarComplex_space
    (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    K.space \ faceAvoidingUnion K s ⊆ (faceStarComplex K s).space := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K hx.1
  have hst : s ⊆ t := by
    by_contra h
    exact hx.2 (mem_iUnion₂.mpr
      ⟨t, ⟨ht, h⟩, openSimplex_subset_convexHull t hxt⟩)
  exact (faceStarComplex K s).convexHull_subset_space
    ⟨ht, by rwa [Finset.union_eq_left.mpr hst]⟩ (openSimplex_subset_convexHull t hxt)

open Classical in
theorem frontier_faceStarComplex_inter_convexHull
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : Finset E} (ht : t ∈ K.faces) (hst : s ⊆ t)
    (htrace : frontier K.space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    frontier (faceStarComplex K s).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E) := by
  let P := (faceStarComplex K s).space
  let A := ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)
  let _ : Finite (faceStarComplex K s).faces := (faceStarComplex_faces_finite K s).to_subtype
  have hPclosed : IsClosed P := (isPolyhedron_space (faceStarComplex K s)).isCompact.isClosed
  have hKclosed : IsClosed K.space := (isPolyhedron_space K).isCompact.isClosed
  have hPK : P ⊆ K.space := space_mono_of_faces_subset (faceStarComplex_faces_subset K s)
  have htP : t ∈ (faceStarComplex K s).faces := ⟨ht, by rwa [Finset.union_eq_left.mpr hst]⟩
  have havoid : faceAvoidingUnion K s ∩ convexHull ℝ (t : Set E) = A :=
    faceAvoidingUnion_inter_convexHull K ht
  apply Subset.antisymm
  · rintro y ⟨hyPfront, hyt⟩
    by_contra hyA
    have hyP : y ∈ P := hPclosed.frontier_subset hyPfront
    have hyK : y ∈ K.space := hPK hyP
    have hyKfront : y ∉ frontier K.space := by
      intro hy
      exact hyA (show y ∈ A by simpa only [A] using htrace ▸ ⟨hy, hyt⟩)
    have hyKint : y ∈ interior K.space := by
      rw [hKclosed.frontier_eq] at hyKfront
      exact Classical.byContradiction fun h => hyKfront ⟨hyK, h⟩
    have hyAvoid : y ∉ faceAvoidingUnion K s := by
      intro hy
      exact hyA (show y ∈ A by rw [← havoid]; exact ⟨hy, hyt⟩)
    have hopen : IsOpen (interior K.space ∩ (faceAvoidingUnion K s)ᶜ) :=
      isOpen_interior.inter (isClosed_faceAvoidingUnion K s).isOpen_compl
    have hsub : interior K.space ∩ (faceAvoidingUnion K s)ᶜ ⊆ P :=
      fun z hz => space_sdiff_faceAvoidingUnion_subset_faceStarComplex_space K s
        ⟨interior_subset hz.1, hz.2⟩
    have hyPint : y ∈ interior P := interior_maximal hsub hopen ⟨hyKint, hyAvoid⟩
    have hyPdiff : y ∈ P \ interior P := by rwa [← hPclosed.frontier_eq]
    exact hyPdiff.2 hyPint
  · rintro y hyA
    have hyAvoid : y ∈ faceAvoidingUnion K s ∩ convexHull ℝ (t : Set E) := by
      rwa [havoid]
    have hyKfront : y ∈ frontier K.space := by
      have : y ∈ frontier K.space ∩ convexHull ℝ (t : Set E) := by
        rw [htrace]
        simpa only [A] using hyA
      exact this.1
    have hyP : y ∈ P := (faceStarComplex K s).convexHull_subset_space htP hyAvoid.2
    have hyPnotInt : y ∉ interior P := by
      intro hyint
      have hyKint : y ∈ interior K.space := interior_mono hPK hyint
      have hyKdiff : y ∈ K.space \ interior K.space := by rwa [← hKclosed.frontier_eq]
      exact hyKdiff.2 hyKint
    refine ⟨?_, hyAvoid.2⟩
    rw [hPclosed.frontier_eq]
    exact ⟨hyP, hyPnotInt⟩

open Classical in
theorem openSimplex_subset_interior_of_frontier_inter_eq
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : Finset E} (ht : t ∈ K.faces) (hst : s ⊆ t)
    (htrace : frontier K.space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    openSimplex s ⊆ interior K.space := by
  have hclosed : IsClosed K.space := (isPolyhedron_space K).isCompact.isClosed
  intro x hx
  have hxt : x ∈ convexHull ℝ (t : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hst) (openSimplex_subset_convexHull s hx)
  have hxK := K.convexHull_subset_space ht hxt
  have hxnot : x ∉ frontier K.space := by
    intro hxfront
    have hxunion : x ∈ ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E) := by
      rw [← htrace]
      exact ⟨hxfront, hxt⟩
    obtain ⟨v, hvs, hxv⟩ := mem_iUnion₂.mp hxunion
    have hsub : s ⊆ t.erase v := subset_of_mem_openSimplex_of_mem_convexHull
      (K.indep ht) hst (Finset.erase_subset v t) hx hxv
    exact Finset.notMem_erase v t (hsub hvs)
  rw [hclosed.frontier_eq] at hxnot
  exact Classical.byContradiction fun h => hxnot ⟨hxK, h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
