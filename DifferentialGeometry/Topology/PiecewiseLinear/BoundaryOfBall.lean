/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.StarJoin
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Ball

variable [DecidableEq E]

theorem boundaryComplex_simplexComplex {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) :
    boundaryComplex (n + 1) (simplexComplex T hT) = simplexBoundary T hT := by
  ext s
  rw [mem_boundaryComplex_faces_iff, mem_simplexBoundary_faces_iff]
  constructor
  · rintro ⟨hs, t, ht, hst, htn, -⟩
    refine ⟨hs.2, hs.1, fun hsT => ?_⟩
    have hle := Finset.card_le_card hst
    rw [hsT, hcard] at hle
    omega
  · rintro ⟨hsT, hs, hsne⟩
    have hslt : s.card < T.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsT,
        hsne⟩)
    have hsn : s.card ≤ n + 1 := by omega
    have hrestcard : (T \ s).card = n + 1 - s.card + 1 := by
      rw [Finset.card_sdiff_of_subset hsT, hcard]
      omega
    have hrest : (T \ s).Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨⟨hs, hsT⟩, s, ⟨hs, hsT⟩, subset_rfl, hsn, ?_⟩
    rw [geometricLink_simplexComplex hT hsT,
      simplexComplex_space _ (affineIndependent_of_subset hT Finset.sdiff_subset) hrest]
    exact isPLBall_convexHull_of_affineIndependent _
      (affineIndependent_of_subset hT Finset.sdiff_subset) hrestcard

theorem simplexBoundary_stdVertices_space_subset (n : ℕ) :
    (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) := by
  intro y hy
  obtain ⟨s, hs, hys⟩ := (simplexBoundary _ _).mem_space_iff.mp hy
  rw [← convexHull_stdVertices]
  exact convexHull_mono (Finset.coe_subset.mpr hs.1) hys

theorem starAvoiding_eq_simplexBoundary_of_card (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {n : ℕ} (hK : IsPLBall (n + 1) K.space) {t : Finset E} (ht : t ∈ K.faces)
    (hcard : t.card = n + 2) : starAvoiding K t = simplexBoundary t (K.indep ht) := by
  ext s
  rw [mem_starAvoiding_faces_iff, mem_simplexBoundary_faces_iff]
  constructor
  · rintro ⟨hs, hst, hts⟩
    have hle := card_le_of_isPLBall K hK hst
    have hsub : t = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    refine ⟨fun w hw => ?_, K.nonempty_of_mem_faces hs, fun h => hts ?_⟩
    · rw [hsub]
      exact Finset.mem_union_left t hw
    · subst h
      exact Finset.Subset.refl _
  · rintro ⟨hst, hne, hst'⟩
    exact ⟨K.down_closed ht hst hne, by rwa [Finset.union_eq_right.mpr hst],
      fun h => hst' (Finset.Subset.antisymm hst h)⟩

theorem boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) L.space) :
    (boundaryComplex (n + 1) L).space =
      f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
  classical
  have hL : IsPLBall (n + 1) L.space := ⟨f, hf⟩
  have hfinB : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBsub := simplexBoundary_stdVertices_space_subset n
  have hclosed : IsClosed
      (f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space) :=
    ((SimplicialComplex.isCompact_geometricSpace _).image_of_continuousOn
      (hf.2.1.continuousOn.mono hBsub)).isClosed
  have hpoint : ∀ x ∈ L.space, ∀ (L' : Geometry.SimplicialComplex ℝ E) [Finite L'.faces],
      IsSubdivision L' L → {x} ∈ L'.faces →
      (IsPLBall n (SimplicialComplex.geometricLink L' {x}).space ↔
        x ∈ f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space) := by
    intro x _ L' _ hL' hx'
    have hf' : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) L'.space := by
      rwa [hL'.space_eq]
    exact isPLBall_geometricLink_iff_of_isPLHomeomorphOn_stdSimplex L' hf' hx'
  apply Subset.antisymm
  · intro y hy
    obtain ⟨s, ⟨-, t, ht, hst, htn, hball⟩, hys⟩ := (boundaryComplex (n + 1) L).mem_space_iff.mp hy
    have hsub : convexHull ℝ (t : Set E) ⊆
        f '' (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
      refine (convexHull_subset_closure_openSimplex (L.nonempty_of_mem_faces ht)).trans ?_
      rw [← hclosed.closure_eq]
      apply closure_mono
      intro x hx
      have hxL : x ∈ L.space :=
        L.convexHull_subset_space ht (openSimplex_subset_convexHull _ hx)
      obtain ⟨L', hL', hfin', hx'⟩ := exists_isSubdivision_singleton_mem L hxL
      have : Finite L'.faces := hfin'.to_subtype
      refine (hpoint x hxL L' hL' hx').mp ?_
      obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 :=
        ⟨t.card - 1, by have := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht); omega⟩
      have h := isPLBall_geometricLink_of_isPLBall_geometricLink L ht hx hL' hx' hk hball
      rwa [show k + (n + 1 - t.card) = n by omega] at h
    exact hsub (convexHull_mono (Finset.coe_subset.mpr hst) hys)
  · intro x hx
    have hxL : x ∈ L.space := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hf.1.mapsTo (hBsub hy)
    obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hxL
    obtain ⟨L', hL', hfin', hx'⟩ := exists_isSubdivision_singleton_mem L hxL
    have : Finite L'.faces := hfin'.to_subtype
    have hxball : IsPLBall n (SimplicialComplex.geometricLink L' {x}).space :=
      (hpoint x hxL L' hL' hx').mpr hx
    have hcardle : t.card ≤ n + 2 := card_le_of_isPLBall L hL ht
    obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 :=
      ⟨t.card - 1, by have := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht); omega⟩
    have hxconv : x ∈ convexHull ℝ (t : Set E) := openSimplex_subset_convexHull _ hxt
    by_cases hk' : k ≤ n
    · rcases isPLSphere_or_isPLBall_geometricLink_faces_of_isPLBall L hL ht hk hk' with hsph | hball
      · exfalso
        have h := isPLSphere_geometricLink_of_isPLSphere_geometricLink L ht hxt hL' hx' hk hsph
        rw [show k + (n - k) = n by omega] at h
        exact hxball.not_isPLSphere h
      · refine (boundaryComplex (n + 1) L).convexHull_subset_space
          (mem_boundaryComplex_faces_of_isPLBall (n + 1) L ht (by omega) ?_) hxconv
        rwa [show n + 1 - t.card = n - k by omega]
    · exfalso
      have hcard : t.card = n + 2 := by omega
      obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding L ht hxt hL' hx'
      rw [starAvoiding_eq_simplexBoundary_of_card L hL ht hcard,
        simplexBoundary_space t (L.indep ht) (by omega)] at hg
      exact hxball.not_isPLSphere
        ((isPLSphere_biUnion_erase t (L.indep ht) hcard).of_isPLHomeomorphOn hg.symm)

theorem isPLSphere_boundaryComplex_space_of_isPLBall {n : ℕ} (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsPLBall (n + 1) L.space) :
    IsPLSphere n (boundaryComplex (n + 1) L).space := by
  obtain ⟨f, hf⟩ := hL
  rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hf]
  have hfinB : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  exact (isPLSphere_simplexBoundary_std n).of_isPLHomeomorphOn
    (hf.restrict (isPolyhedron_space _) (simplexBoundary_stdVertices_space_subset n))

end Ball

open Classical in
theorem isCombinatorialManifold_boundaryComplex {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (h : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    IsCombinatorialManifold n (boundaryComplex (n + 1) K) := by
  cases n with
  | zero =>
    intro v _
    rw [geometricLink_boundaryComplex, Set.eq_empty_iff_forall_notMem]
    rintro s ⟨-, t, ht, -, htn, -⟩
    exact ((SimplicialComplex.geometricLink K {v}).nonempty_of_mem_faces ht).ne_empty
      (Finset.card_eq_zero.mp (Nat.le_zero.mp htn))
  | succ m =>
    intro v hv
    have hvK : {v} ∈ K.faces := boundaryComplex_faces_subset _ K hv
    rw [geometricLink_boundaryComplex]
    have hL : IsPLBall (m + 1) (SimplicialComplex.geometricLink K {v}).space := by
      rcases h v hvK with hsph | hball
      · exfalso
        obtain ⟨-, t, ht, hvt, htn, hball⟩ := hv
        have hvt' : v ∈ t := Finset.singleton_subset_iff.mp hvt
        rcases (t.erase v).eq_empty_or_nonempty with he | hne
        · have htv : t = {v} :=
            ((Finset.erase_eq_empty_iff t v).mp he).resolve_left
              (K.nonempty_of_mem_faces ht).ne_empty
          rw [htv, Finset.card_singleton, show m + 1 + 1 - 1 = m + 1 by omega] at hball
          exact hball.not_isPLSphere hsph
        · obtain ⟨k, hk⟩ : ∃ k, (t.erase v).card = k + 1 :=
            ⟨(t.erase v).card - 1, by have := Finset.card_pos.mpr hne; omega⟩
          have hsL : t.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces :=
            (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
              ⟨hne, Finset.notMem_erase v t, by rwa [Finset.insert_erase hvt']⟩
          have hk' : k ≤ m := by
            have := Finset.card_erase_of_mem hvt'
            omega
          have hs := isPLSphere_geometricLink_faces_of_isPLSphere _ hsph hsL hk hk'
          rw [← geometricLink_insert K (Finset.notMem_erase v t), Finset.insert_erase hvt'] at hs
          rw [show m + 1 + 1 - t.card = m - k by
            have := Finset.card_erase_of_mem hvt'
            omega] at hball
          exact hball.not_isPLSphere hs
      · exact hball
    exact isPLSphere_boundaryComplex_space_of_isPLBall _ hL

end DifferentialGeometry.Topology.PiecewiseLinear
