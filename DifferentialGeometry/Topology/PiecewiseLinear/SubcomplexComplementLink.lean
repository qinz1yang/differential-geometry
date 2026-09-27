/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_restrict_faces_iff_of_faces_subset
    (K A B : Geometry.SimplicialComplex ℝ E) (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    {s : Finset E} : s ∈ (restrict A B.space).faces ↔ s ∈ A.faces ∧ s ∈ B.faces := by
  constructor
  · rintro ⟨hs, hsub⟩
    refine ⟨hs, ?_⟩
    by_contra hnot
    exact notMem_space_of_notMem_faces hB (hA hs) hnot
      (centroid_mem_openSimplex (A.nonempty_of_mem_faces hs))
      (hsub (s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs)))
  · rintro ⟨hsA, hsB⟩
    exact ⟨hsA, B.convexHull_subset_space hsB⟩

theorem restrict_space_eq_inter_of_faces_subset
    (K A B : Geometry.SimplicialComplex ℝ E) (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces) :
    (restrict A B.space).space = A.space ∩ B.space := by
  refine Subset.antisymm (fun x hx => ⟨space_mono_of_faces_subset (restrict_faces_subset _ _) hx,
    restrict_space_subset _ _ hx⟩) ?_
  rintro x ⟨hxA, hxB⟩
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex A hxA
  have hsB : s ∈ B.faces := by
    by_contra hnot
    exact notMem_space_of_notMem_faces hB (hA hs) hnot hxs hxB
  exact (restrict A B.space).convexHull_subset_space
    ⟨hs, B.convexHull_subset_space hsB⟩ (openSimplex_subset_convexHull _ hxs)

open Classical in
theorem geometricLink_restrict_space_of_faces_subset
    (K A B : Geometry.SimplicialComplex ℝ E) (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    (v : E) :
    SimplicialComplex.geometricLink (restrict A B.space) {v} =
      restrict (SimplicialComplex.geometricLink A {v})
        (SimplicialComplex.geometricLink B {v}).space := by
  have hAL : (SimplicialComplex.geometricLink A {v}).faces ⊆
      (SimplicialComplex.geometricLink K {v}).faces := fun _ ht => ⟨ht.1, ht.2.1, hA ht.2.2⟩
  have hBL : (SimplicialComplex.geometricLink B {v}).faces ⊆
      (SimplicialComplex.geometricLink K {v}).faces := fun _ ht => ⟨ht.1, ht.2.1, hB ht.2.2⟩
  ext s
  rw [SimplicialComplex.mem_geometricLink_singleton,
    mem_restrict_faces_iff_of_faces_subset K A B hA hB,
    mem_restrict_faces_iff_of_faces_subset (SimplicialComplex.geometricLink K {v})
      (SimplicialComplex.geometricLink A {v}) (SimplicialComplex.geometricLink B {v}) hAL hBL,
    SimplicialComplex.mem_geometricLink_singleton, SimplicialComplex.mem_geometricLink_singleton]
  tauto

open Classical in
theorem geometricLink_subcomplexGeneratedBy_compl
    (K A : Geometry.SimplicialComplex ℝ E) (v : E) :
    SimplicialComplex.geometricLink (subcomplexGeneratedBy K A.facesᶜ) {v} =
      subcomplexGeneratedBy (SimplicialComplex.geometricLink K {v})
        (SimplicialComplex.geometricLink A {v}).facesᶜ := by
  classical
  ext s
  rw [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hs, hvs, t, ⟨htK, htA⟩, hst, _⟩
    have hvt : v ∈ t := hst (Finset.mem_insert_self _ _)
    have hst' : s ⊆ t.erase v := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hvs (h ▸ hx), hst (Finset.mem_insert_of_mem hx)⟩
    refine ⟨t.erase v, ⟨?_, ?_⟩, hst', hs⟩
    · exact (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
        ⟨hs.mono hst', Finset.notMem_erase _ _, by rwa [Finset.insert_erase hvt]⟩
    · intro ht
      have hi := (SimplicialComplex.mem_geometricLink_singleton A v _).mp ht |>.2.2
      exact htA (Finset.insert_erase hvt ▸ hi)
  · rintro ⟨t, ⟨htK, htA⟩, hst, hs⟩
    obtain ⟨ht, hvt, hiK⟩ := (SimplicialComplex.mem_geometricLink_singleton K v t).mp htK
    refine ⟨hs, fun hv => hvt (hst hv), insert v t, ⟨hiK, ?_⟩,
      Finset.insert_subset_insert _ hst, Finset.insert_nonempty _ _⟩
    intro hiA
    exact htA ((SimplicialComplex.mem_geometricLink_singleton A v t).mpr ⟨ht, hvt, hiA⟩)

open Classical in
theorem geometricLink_subcomplexGeneratedBy_compl_of_notMem
    (K A : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∉ A.faces) :
    SimplicialComplex.geometricLink (subcomplexGeneratedBy K A.facesᶜ) {v} =
      SimplicialComplex.geometricLink K {v} := by
  ext s
  rw [SimplicialComplex.mem_geometricLink_singleton, SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hs, hvs, ht⟩
    exact ⟨hs, hvs, subcomplexGeneratedBy_faces_subset K A.facesᶜ ht⟩
  · rintro ⟨hs, hvs, hiK⟩
    refine ⟨hs, hvs, insert v s, ⟨hiK, ?_⟩, Finset.Subset.rfl, Finset.insert_nonempty _ _⟩
    intro hiA
    exact hv (A.down_closed hiA (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_nonempty _))

open Classical in
theorem not_geometricLink_space_subset_of_mem_subcomplexGeneratedBy_compl
    (K A : Geometry.SimplicialComplex ℝ E) (hA : A.faces ⊆ K.faces) {v : E}
    (hvA : {v} ∈ A.faces) (hv : {v} ∈ (subcomplexGeneratedBy K A.facesᶜ).faces) :
    ¬(SimplicialComplex.geometricLink K {v}).space ⊆
      (SimplicialComplex.geometricLink A {v}).space := by
  classical
  obtain ⟨t, ⟨htK, htA⟩, hvt, _⟩ := hv
  have hvt' : v ∈ t := Finset.singleton_subset_iff.mp hvt
  have hne : (t.erase v).Nonempty := by
    rcases (t.erase v).eq_empty_or_nonempty with he | he
    · have ht : t = {v} := (Finset.erase_eq_empty_iff t v).mp he |>.resolve_left
        (K.nonempty_of_mem_faces htK).ne_empty
      exact (htA (ht.symm ▸ hvA)).elim
    · exact he
  have htL : t.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces :=
    (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
      ⟨hne, Finset.notMem_erase _ _, by rwa [Finset.insert_erase hvt']⟩
  have htL' : t.erase v ∉ (SimplicialComplex.geometricLink A {v}).faces := by
    intro ht
    have hi := (SimplicialComplex.mem_geometricLink_singleton A v _).mp ht |>.2.2
    exact htA (Finset.insert_erase hvt' ▸ hi)
  have hAL : (SimplicialComplex.geometricLink A {v}).faces ⊆
      (SimplicialComplex.geometricLink K {v}).faces := fun _ ht => ⟨ht.1, ht.2.1, hA ht.2.2⟩
  intro hsub
  exact notMem_space_of_notMem_faces hAL htL htL'
    (centroid_mem_openSimplex hne)
    (hsub ((SimplicialComplex.geometricLink K {v}).convexHull_subset_space htL
      ((t.erase v).centroid_mem_convexHull hne)))

open Classical in
theorem geometricLink_subcomplexGeneratedBy_compl_space [FiniteDimensional ℝ E]
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hA : A.faces ⊆ K.faces) (v : E) :
    (SimplicialComplex.geometricLink (subcomplexGeneratedBy K A.facesᶜ) {v}).space =
      closure ((SimplicialComplex.geometricLink K {v}).space \
        (SimplicialComplex.geometricLink A {v}).space) := by
  have hAL : (SimplicialComplex.geometricLink A {v}).faces ⊆
      (SimplicialComplex.geometricLink K {v}).faces := fun _ ht => ⟨ht.1, ht.2.1, hA ht.2.2⟩
  rw [geometricLink_subcomplexGeneratedBy_compl,
    ← closure_space_sdiff_space_eq_subcomplexGeneratedBy (SimplicialComplex.geometricLink K {v})
      (SimplicialComplex.geometricLink K {v}) (SimplicialComplex.geometricLink A {v}) Subset.rfl
          hAL]

end DifferentialGeometry.Topology.PiecewiseLinear
