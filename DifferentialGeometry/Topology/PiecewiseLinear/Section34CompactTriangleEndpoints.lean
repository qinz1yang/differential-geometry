/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairTwoSimplices
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedIntervalLink
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem triangle_vertex_trace_inter_eq_mark (K L : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (hmax : ∀ r ∈ K.faces, r ⊆ s)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s)
    {v w : E} (hvs : v ∈ s) (hws : w ∈ s) (hvw : v ≠ w) :
    ((graphDualCell K L v).space ∩ (derivedNeighborhoodCell K s).space) ∩
        ((graphDualCell K L w).space ∩ (derivedNeighborhoodCell K s).space) =
      {({({v, w} : Finset E).centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id} := by
  have hpair : ({v, w} : Finset E) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hvs
    · rcases Finset.mem_singleton.mp hx with rfl
      exact hws
  have he := K.down_closed hs hpair (Finset.insert_nonempty _ _)
  have hec : ({v, w} : Finset E).card = 2 := Finset.card_pair hvw
  have heL : {v, w} ∈ L.faces := (hL _).mpr ⟨he, fun h => by
    have hc := congrArg Finset.card h
    rw [hec, hcard] at hc
    omega⟩
  have hLK : L.faces ⊆ K.faces := fun r hr => ((hL r).mp hr).1
  have hLc : ∀ r ∈ L.faces, r.card ≤ 2 := by
    intro r hr
    have hrK := hLK hr
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hmax r hrK, ((hL r).mp hr).2⟩)
    omega
  calc
    _ = ((graphDualCell K L v).space ∩ (graphDualCell K L w).space) ∩
        (derivedNeighborhoodCell K s).space := by
      ext x
      simp only [mem_inter_iff]
      tauto
    _ = (splittingDisk K {v, w} he).space ∩ (derivedNeighborhoodCell K s).space := by
      rw [graphDualCell_space_inter K L hLK hLc hvw heL]
    _ = _ := splittingDisk_inter_derivedNeighborhoodCell_eq_singleton K he hs hpair
      (by omega) hmax

open Classical in
theorem triangle_mark_ne_of_distinct_edges (K : Geometry.SimplicialComplex ℝ E)
    {e f s : Finset E} (he : e ∈ K.faces) (hf : f ∈ K.faces) (hs : s ∈ K.faces)
    (hes : e ⊆ s) (hfs : f ⊆ s) (hec : e.card < s.card) (hef : e ≠ f) :
    ({e.centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id ≠
      ({f.centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id := by
  have heS := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K he hs (Or.inl hes)
  have hfS := pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K hf hs (Or.inl hfs)
  intro h
  have hp := injOn_faces_of_mem_openSimplex (barycentricSubdivision K)
    (centroid_mem_openSimplex_of_mem_faces _) heS hfS h
  have hm : e.centroid ℝ id ∈ ({f.centroid ℝ id, s.centroid ℝ id} : Finset E) :=
    hp ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact hef (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) he hf h)
  · have heq := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) he hs (Finset.mem_singleton.mp h)
    have hc := congrArg Finset.card heq
    omega

open Classical in
theorem boundaryComplex_interval_eq_pair_of_subset [FiniteDimensional ℝ E]
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : IsPLBall 1 A.space)
    {p q : E} (hpq : p ≠ q) (hp : p ∈ (boundaryComplex 1 A).space)
    (hq : q ∈ (boundaryComplex 1 A).space) :
    (boundaryComplex 1 A).space = {p, q} := by
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hA
  have hbd := boundaryComplex_space_of_parametrized_Icc A zero_lt_one hγ
  rw [hbd] at hp hq ⊢
  simp only [mem_insert_iff, mem_singleton_iff] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (hpq (hp.trans hq.symm)).elim
  · rw [← hp, ← hq]
  · rw [← hq, ← hp, pair_comm]
  · exact (hpq (hp.trans hq.symm)).elim

open Classical in
theorem boundaryComplex_triangle_vertex_trace_eq_pair [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (hmax : ∀ r ∈ K.faces, r ⊆ s)
    (hL : ∀ r, r ∈ L.faces ↔ r ∈ K.faces ∧ r ≠ s)
    {v w z : E} (hv : {v} ∈ K.faces) (hvs : v ∈ s) (hws : w ∈ s) (hzs : z ∈ s)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    (boundaryComplex 1 (upperLink (dualCell K {v} hv) {s.centroid ℝ id})).space =
      {({({v, w} : Finset E).centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id,
        ({({v, z} : Finset E).centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id} := by
  let D := derivedNeighborhoodCell K s
  let R := boundaryComplex 2 D
  let A := upperLink (dualCell K {v} hv) {s.centroid ℝ id}
  let _ : Finite D.faces := (derivedNeighborhoodCell_faces_finite K s).to_subtype
  let _ : Finite R.faces := (boundaryComplex_faces_finite 2 D).to_subtype
  let _ : Finite (dualCell K {v} hv).faces := (dualCell_faces_finite K hv).to_subtype
  let _ : Finite A.faces := (upperLink_faces_finite _ _).to_subtype
  have hKsp : K.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := K.mem_space_iff.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr (hmax r hr)) hxr
    · exact K.convexHull_subset_space hs
  have hKball : IsPLBall 2 K.space := by
    rw [hKsp]
    exact isPLBall_convexHull_of_affineIndependent s (K.indep hs) hcard
  have hD : IsPLBall 2 D.space :=
    hKball.isCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell hs
  have hRman := (isPLSphere_boundaryComplex_space_of_isPLBall D hD).isCombinatorialManifold
  have hR : IsCombinatorialManifoldWithBoundary 1 R := hRman.isCombinatorialManifoldWithBoundary
  have hAeq : (graphDualCell K L v).space ∩ D.space = A.space :=
    graphDualCell_inter_derivedNeighborhoodCell_eq_upperLink K L hv hs hL
  have hA : IsPLBall 1 A.space := hAeq ▸
    isPLBall_graphDualCell_inter_triangleCell K L hs hvs hcard hmax hL
  have htraceR (a : E) (ha : a ∈ s) :
      (graphDualCell K L a).space ∩ D.space ⊆ R.space := by
    change _ ⊆ (boundaryComplex 2 (derivedNeighborhoodCell K s)).space
    rw [boundaryComplex_triangleCell_eq_iUnion_graphDualCell K L hs hcard hmax hL]
    change (graphDualCell K L a).space ∩ (derivedNeighborhoodCell K s).space ⊆ _
    exact subset_biUnion_of_mem (u := fun b =>
      (graphDualCell K L b).space ∩ (derivedNeighborhoodCell K s).space) ha
  have hAR : A.space ⊆ R.space := hAeq ▸ htraceR v hvs
  have hmark (a : E) (ha : a ∈ s) (hva : v ≠ a) :
      ({({v, a} : Finset E).centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id ∈
        (boundaryComplex 1 A).space := by
    let Q := (graphDualCell K L a).space ∩ D.space
    have hQ : IsPLBall 1 Q :=
      isPLBall_graphDualCell_inter_triangleCell K L hs ha hcard hmax hL
    have hI : A.space ∩ Q =
        {({({v, a} : Finset E).centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id} := by
      rw [← hAeq]
      exact triangle_vertex_trace_inter_eq_mark K L hs hcard hmax hL hvs ha hva
    have hIball : IsPLBall 0 (A.space ∩ Q) := by
      rw [hI]
      exact isPLBall_zero_singleton _
    have hbound := hR.inter_subset_boundaryComplex_of_isPLBall A hA hAR hQ
      (htraceR a ha) hIball
    apply hbound
    rw [hI]
    exact mem_singleton _
  have hedge (a : E) (ha : a ∈ s) : ({v, a} : Finset E) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hvs
    · rcases Finset.mem_singleton.mp hx with rfl
      exact ha
  have hevw := K.down_closed hs (hedge w hws) (Finset.insert_nonempty _ _)
  have hevz := K.down_closed hs (hedge z hzs) (Finset.insert_nonempty _ _)
  have hene : ({v, w} : Finset E) ≠ {v, z} := by
    intro h
    have hm : w ∈ ({v, z} : Finset E) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hm with h | h
    · exact hvw h.symm
    · exact hwz (Finset.mem_singleton.mp h)
  have hpq := triangle_mark_ne_of_distinct_edges K hevw hevz hs (hedge w hws)
    (hedge z hzs) (by rw [Finset.card_pair hvw, hcard]; omega) hene
  exact boundaryComplex_interval_eq_pair_of_subset A hA hpq
    (hmark w hws hvw) (hmark z hzs hvz)

end DifferentialGeometry.Topology.PiecewiseLinear
