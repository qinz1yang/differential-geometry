/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def triangleSubcomplexIn (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    Geometry.SimplicialComplex ℝ E :=
  subcomplexGeneratedBy K {t | t.card = 3 ∧ convexHull ℝ (t : Set E) ⊆ U}

theorem triangleSubcomplexIn_faces_subset (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    (triangleSubcomplexIn K U).faces ⊆ K.faces := subcomplexGeneratedBy_faces_subset K _

theorem triangleSubcomplexIn_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (U : Set E) : (triangleSubcomplexIn K U).faces.Finite := subcomplexGeneratedBy_faces_finite K _

theorem triangleSubcomplexIn_space_subset (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    (triangleSubcomplexIn K U).space ⊆ U := by
  rw [triangleSubcomplexIn, subcomplexGeneratedBy_space]
  exact iUnion₂_subset fun t ht => ht.2.2

theorem exists_face_superset_card_eq_triangleSubcomplexIn
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) {s : Finset E}
    (hs : s ∈ (triangleSubcomplexIn K U).faces) :
    ∃ t ∈ (triangleSubcomplexIn K U).faces, s ⊆ t ∧ t.card = 3 :=
  exists_face_superset_card_eq_subcomplexGeneratedBy K _ (fun _ ht => ht.2.1) hs

theorem mem_triangleSubcomplexIn_triangle_iff
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) {s : Finset E} (hscard : s.card = 3) :
    s ∈ (triangleSubcomplexIn K U).faces ↔ s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ U := by
  change s ∈ (subcomplexGeneratedBy K _).faces ↔ _
  rw [mem_subcomplexGeneratedBy_faces_of_card K _ (fun _ ht => ht.2.1) hscard]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hscard, h.2⟩⟩

open Classical in
theorem faceStarComplex_triangleSubcomplexIn_eq
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) (s : Finset E)
    (hpure : ∀ u ∈ (faceStarComplex K s).faces,
      ∃ v ∈ (faceStarComplex K s).faces, u ⊆ v ∧ v.card = 3)
    (hU : (faceStarComplex K s).space ⊆ U) :
    faceStarComplex (triangleSubcomplexIn K U) s = faceStarComplex K s := by
  have hsub : (faceStarComplex K s).faces ⊆ (triangleSubcomplexIn K U).faces := by
    intro u hu
    obtain ⟨v, hv, huv, hvcard⟩ := hpure u hu
    exact ⟨v, ⟨hv.1, hvcard, ((faceStarComplex K s).convexHull_subset_space hv).trans hU⟩,
      huv, K.nonempty_of_mem_faces hu.1⟩
  ext u
  constructor
  · intro hu
    exact ⟨triangleSubcomplexIn_faces_subset K U hu.1,
      triangleSubcomplexIn_faces_subset K U hu.2⟩
  · intro hu
    refine ⟨hsub hu, hsub ⟨hu.2, ?_⟩⟩
    simpa only [Finset.union_assoc, Finset.union_self] using hu.2

theorem space_eq_triangleSubcomplexIn_union
    (K : Geometry.SimplicialComplex ℝ E) (U B : Set E)
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    (hcover : ∀ t ∈ K.faces, t.card = 3 →
      convexHull ℝ (t : Set E) ⊆ U ∨ convexHull ℝ (t : Set E) ⊆ B) :
    K.space = (triangleSubcomplexIn K U).space ∪ (K.space ∩ B) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := K.mem_space_iff.mp hx
    obtain ⟨t, ht, hut, htcard⟩ := hpure u hu
    have hxt := convexHull_mono (Finset.coe_subset.mpr hut) hxu
    rcases hcover t ht htcard with htU | htB
    · exact Or.inl ((triangleSubcomplexIn K U).convexHull_subset_space
        ((mem_triangleSubcomplexIn_triangle_iff K U htcard).mpr ⟨ht, htU⟩) hxt)
    · exact Or.inr ⟨hx, htB hxt⟩
  · exact union_subset (space_mono_of_faces_subset (triangleSubcomplexIn_faces_subset K U))
      inter_subset_left

open Classical in
theorem eraseTriangleComplex_space_eq_triangleSubcomplexIn_union
    (K : Geometry.SimplicialComplex ℝ E) (U B : Set E)
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    (hcover : ∀ u ∈ K.faces, u.card = 3 →
      convexHull ℝ (u : Set E) ⊆ U ∨ convexHull ℝ (u : Set E) ⊆ B)
    {t : Finset E} (htB : Disjoint (convexHull ℝ (t : Set E)) B) :
    (eraseTriangleComplex K t).space =
      (eraseTriangleComplex (triangleSubcomplexIn K U) t).space ∪ (K.space ∩ B) := by
  rw [eraseTriangleComplex_space K t, eraseTriangleComplex_space (triangleSubcomplexIn K U) t]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, ⟨hu, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
    rcases hcover u hu hucard with huU | huB
    · exact Or.inl (mem_iUnion₂.mpr ⟨u,
        ⟨(mem_triangleSubcomplexIn_triangle_iff K U hucard).mpr ⟨hu, huU⟩, hucard, hut⟩, hxu⟩)
    · exact Or.inr ⟨K.convexHull_subset_space hu hxu, huB hxu⟩
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨u, ⟨hu, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨u, ⟨triangleSubcomplexIn_faces_subset K U hu, hucard, hut⟩, hxu⟩
    · obtain ⟨u, hu, hxu⟩ := K.mem_space_iff.mp hx.1
      obtain ⟨v, hv, huv, hvcard⟩ := hpure u hu
      have hxv := convexHull_mono (Finset.coe_subset.mpr huv) hxu
      refine mem_iUnion₂.mpr ⟨v, ⟨hv, hvcard, ?_⟩, hxv⟩
      intro hvt
      exact Set.disjoint_left.mp htB (hvt ▸ hxv) hx.2

end DifferentialGeometry.Topology.PiecewiseLinear
