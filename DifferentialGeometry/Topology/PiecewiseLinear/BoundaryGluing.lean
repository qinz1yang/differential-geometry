/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.SphereGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isCombinatorialManifold_unionComplex {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (hboundaryK : K.space ∩ L.space = (boundaryComplex n K).space)
    (hboundaryL : K.space ∩ L.space = (boundaryComplex n L).space) :
    IsCombinatorialManifold n (unionComplex K L h) := by
  classical
  cases n with
  | zero =>
    intro v hv
    rw [eq_empty_iff_forall_notMem]
    intro t ht
    obtain ⟨hne, hdisj, hmem⟩ := (mem_geometricLink_faces_iff _).mp ht
    rcases hmem with hmem | hmem
    · have hvK := K.down_closed hmem Finset.subset_union_left (Finset.singleton_nonempty v)
      have htK : t ∈ (SimplicialComplex.geometricLink K {v}).faces := ⟨hne, hdisj, hmem⟩
      rw [hK v hvK] at htK
      exact htK
    · have hvL := L.down_closed hmem Finset.subset_union_left (Finset.singleton_nonempty v)
      have htL : t ∈ (SimplicialComplex.geometricLink L {v}).faces := ⟨hne, hdisj, hmem⟩
      rw [hL v hvL] at htL
      exact htL
  | succ n =>
    have hBK : intersectionComplex K L = boundaryComplex (n + 1) K :=
      eq_of_faces_subset_of_space_eq _ _ K (fun _ hs => hs.1)
        (boundaryComplex_faces_subset (n + 1) K)
        ((intersectionComplex_space K L h).trans hboundaryK)
    have hBL : intersectionComplex K L = boundaryComplex (n + 1) L :=
      eq_of_faces_subset_of_space_eq _ _ L (fun _ hs => hs.2)
        (boundaryComplex_faces_subset (n + 1) L)
        ((intersectionComplex_space K L h).trans hboundaryL)
    have hempty (M : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∉ M.faces) :
        (SimplicialComplex.geometricLink M {v}).space = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨s, hs, -⟩ := (SimplicialComplex.geometricLink M {v}).mem_space_iff.mp hx
      exact hv (mem_faces_of_mem_geometricLink M (Finset.singleton_nonempty v) hs)
    intro v hv
    change {v} ∈ K.faces ∪ L.faces at hv
    rw [geometricLink_space_unionComplex]
    by_cases hvK : {v} ∈ K.faces
    · by_cases hvL : {v} ∈ L.faces
      · have hvBK : {v} ∈ (boundaryComplex (n + 1) K).faces := hBK ▸ ⟨hvK, hvL⟩
        have hvBL : {v} ∈ (boundaryComplex (n + 1) L).faces := hBL ▸ ⟨hvK, hvL⟩
        have hballK : IsPLBall n (SimplicialComplex.geometricLink K {v}).space := by
          simpa using ((hK.mem_boundaryComplex_faces_iff K).mp hvBK).2.2
        have hballL : IsPLBall n (SimplicialComplex.geometricLink L {v}).space := by
          simpa using ((hL.mem_boundaryComplex_faces_iff L).mp hvBL).2.2
        have hlinkCompat : ∀ s ∈ (SimplicialComplex.geometricLink K {v}).faces,
            ∀ t ∈ (SimplicialComplex.geometricLink L {v}).faces,
            convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
              convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
          intro s hs t ht
          exact h s (geometricLink_faces_subset K {v} hs)
            t (geometricLink_faces_subset L {v} ht)
        have hinter : (SimplicialComplex.geometricLink K {v}).space ∩
            (SimplicialComplex.geometricLink L {v}).space =
              (SimplicialComplex.geometricLink (intersectionComplex K L) {v}).space := by
          rw [geometricLink_intersectionComplex]
          exact (intersectionComplex_space _ _ hlinkCompat).symm
        apply isPLSphere_union_of_isPLBall _ _ hballK hballL
        · rw [hinter, hBK]
          exact congrArg Geometry.SimplicialComplex.space
            (geometricLink_boundaryComplex n K v)
        · rw [hinter, hBL]
          exact congrArg Geometry.SimplicialComplex.space
            (geometricLink_boundaryComplex n L v)
      · rw [hempty L hvL, union_empty]
        apply hK.isPLSphere_geometricLink_of_not_mem_boundary K hvK
        intro hvB
        exact hvL ((hBK.symm ▸ hvB).2)
    · have hvL : {v} ∈ L.faces := hv.resolve_left hvK
      rw [hempty K hvK, empty_union]
      apply hL.isPLSphere_geometricLink_of_not_mem_boundary L hvL
      intro hvB
      exact hvK ((hBL.symm ▸ hvB).1)

open Classical in
theorem isCombinatorialManifold_of_space_eq_union {n : ℕ}
    (K L R : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (hboundaryK : K.space ∩ L.space = (boundaryComplex n K).space)
    (hboundaryL : K.space ∩ L.space = (boundaryComplex n L).space)
    (hR : R.space = K.space ∪ L.space) : IsCombinatorialManifold n R := by
  classical
  obtain ⟨T, hTfin, -, hTK, hTL⟩ := exists_simplicialComplex_space_union K L
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T K.space
  let B := restrict T L.space
  let _ : Finite A.faces := (restrict_faces_finite T K.space).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite T L.space).to_subtype
  have hA : IsCombinatorialManifoldWithBoundary n A := hK.of_isSubdivision hTK
  have hB : IsCombinatorialManifoldWithBoundary n B := hL.of_isSubdivision hTL
  have hboundary (M N : Geometry.SimplicialComplex ℝ E) [Finite M.faces] [Finite N.faces]
      (hM : IsCombinatorialManifoldWithBoundary n M) (hNM : IsSubdivision N M) :
      (boundaryComplex n N).space = (boundaryComplex n M).space := by
    cases n with
    | zero =>
      have hempty (C : Geometry.SimplicialComplex ℝ E) : (boundaryComplex 0 C).space = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨s, ⟨-, t, ht, -, hcard, -⟩, -⟩ := (boundaryComplex 0 C).mem_space_iff.mp hx
        have hpos := Finset.card_pos.mpr (C.nonempty_of_mem_faces ht)
        omega
      rw [hempty N, hempty M]
    | succ m => exact boundaryComplex_space_of_isSubdivision M N hM hNM
  have hcompat : ∀ s ∈ A.faces, ∀ t ∈ B.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact T.inter_subset_convexHull hs.1 ht.1
  have hAbd : A.space ∩ B.space = (boundaryComplex n A).space := by
    rw [hTK.space_eq, hTL.space_eq, hboundary K A hK hTK]
    exact hboundaryK
  have hBbd : A.space ∩ B.space = (boundaryComplex n B).space := by
    rw [hTK.space_eq, hTL.space_eq, hboundary L B hL hTL]
    exact hboundaryL
  have hU := isCombinatorialManifold_unionComplex A B hcompat hA hB hAbd hBbd
  have hid : IsPLHomeomorphOn (id : E → E) (unionComplex A B hcompat).space R.space := by
    rw [unionComplex_space, hTK.space_eq, hTL.space_eq, ← hR]
    exact (isPolyhedron_space R).isPLHomeomorphOn_id
  exact hU.of_isPLHomeomorphOn hid

open Classical in
theorem exists_isCombinatorialManifold_space_union {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (hboundaryK : K.space ∩ L.space = (boundaryComplex n K).space)
    (hboundaryL : K.space ∩ L.space = (boundaryComplex n L).space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifold n R ∧ R.space = K.space ∪ L.space := by
  obtain ⟨R, hfin, hR⟩ :=
    ((isPolyhedron_space K).union (isPolyhedron_space L)).exists_simplicialComplex
  let _ : Finite R.faces := hfin.to_subtype
  exact ⟨R, hfin,
    isCombinatorialManifold_of_space_eq_union K L R hK hL hboundaryK hboundaryL hR, hR⟩

end DifferentialGeometry.Topology.PiecewiseLinear
