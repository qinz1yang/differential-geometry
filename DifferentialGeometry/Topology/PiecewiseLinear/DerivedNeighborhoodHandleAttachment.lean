/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodTriangle
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodMaximalCell
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap

/-! Standard handle attachments produced from actual derived face cells. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLCellAttachment_derivedNeighborhoodCell
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces)
    {P B : Set F} (hBP : B ⊆ P) {g : F → E}
    (hg : IsPLHomeomorphOn g P (derivedNeighborhoodCell K s).space)
    (hgB : IsPLHomeomorphOn g B
      ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space)) :
    IsPLCellAttachment (n + 2) P B (derivedNeighborhood K L) (derivedNeighborhoodCell K s).space
      (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space := by
  classical
  let A : Set P := {z | z.val ∈ B}
  have hset : (fun z : P => g z.val) '' A = g '' B := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨z, hBP hz⟩, hz, rfl⟩
  refine ⟨(hK.isPLBall_derivedNeighborhoodCell hs).of_isPLHomeomorphOn hg.symm,
    hBP, g, hg, hgB, ?_⟩
  exact exists_derivedNeighborhoodCell_attachment K L hK hLK hs hsL hproper A hg
    (hset.trans hgB.image_eq)

open Classical in
theorem exists_isPLHomeomorphOn_derivedNeighborhoodCell_vertex
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 1) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 1) (hsL : s ∉ L.faces) :
    ∃ g : (Fin (n + 3) → ℝ) → E,
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 3))) (derivedNeighborhoodCell K s).space ∧
      IsPLHomeomorphOn g ∅
        ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space) := by
  classical
  have hmeet : (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxs, hxL⟩
    rw [← iUnion_derivedNeighborhoodCell_space K L hLK] at hxL
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxL
    have htc : t.card = 1 := by
      have hpos := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht)
      have hle := hL t ht
      omega
    have hne : s ≠ t := fun h => hsL (h.symm ▸ ht)
    exact disjoint_left.mp (disjoint_derivedNeighborhoodCell_of_card_eq K hs (hLK ht)
      (hcard.trans htc.symm) hne) hxs hxt
  obtain ⟨g, hg⟩ := hK.isPLBall_derivedNeighborhoodCell hs
  refine ⟨g, hg, ?_⟩
  rw [hmeet]
  simpa using hg.restrict IsPolyhedron.empty (empty_subset _)

open Classical in
theorem exists_isPLHomeomorphOn_derivedNeighborhoodCell_edge_pair
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 2) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 2) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3) ×ˢ Icc 0 1) (derivedNeighborhoodCell K s).space ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ))
        ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space) := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hea : ({a, b} : Finset E) ≠ {a} := by simpa [Finset.ext_iff] using hab.symm
  have heb : ({a, b} : Finset E) ≠ {b} := by simpa [Finset.ext_iff] using hab
  have ha := hproper {a} (Finset.singleton_nonempty a)
    (Finset.ssubset_iff_subset_ne.mpr ⟨by simp, hea.symm⟩)
  have hb := hproper {b} (Finset.singleton_nonempty b)
    (Finset.ssubset_iff_subset_ne.mpr ⟨by simp, heb.symm⟩)
  have hfin : L.faces.Finite := (Set.toFinite K.faces).subset hLK
  let d := hfin.toFinset
  have hmeet := derivedNeighborhoodCell_edge_inter_iUnion K hab hs d
    (fun t ht => ⟨hLK (hfin.mem_toFinset.mp ht), hL t (hfin.mem_toFinset.mp ht)⟩)
    (fun ht => hsL (hfin.mem_toFinset.mp ht)) (hfin.mem_toFinset.mpr ha) (hfin.mem_toFinset.mpr hb)
  have hU : (⋃ t ∈ d, (derivedNeighborhoodCell K t).space) = (derivedNeighborhood K L).space := by
    change (⋃ t ∈ (hfin.toFinset : Set (Finset E)), (derivedNeighborhoodCell K t).space) = _
    rw [hfin.coe_toFinset]
    exact iUnion_derivedNeighborhoodCell_space K L hLK
  rw [hU] at hmeet
  obtain ⟨g, hg, hg0, hg1⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_edge K hK hab hs
  let P := stdSimplex ℝ (Fin 3)
  have hends : P ×ˢ ({0, 1} : Set ℝ) = P ×ˢ {0} ∪ P ×ˢ {1} := by
    ext z
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_union]
    tauto
  have himage : g '' (P ×ˢ ({0, 1} : Set ℝ)) =
      (derivedNeighborhoodCell K {a, b}).space ∩ (derivedNeighborhood K L).space := by
    rw [hends, image_union, hg0, hg1, hmeet]
  have hpoly : IsPolyhedron (P ×ˢ ({0, 1} : Set ℝ)) := by
    rw [hends]
    exact (isPolyhedron_prod_singleton (isPLBall_stdSimplex 2).isPolyhedron 0).union
      (isPolyhedron_prod_singleton (isPLBall_stdSimplex 2).isPolyhedron 1)
  have hsub : P ×ˢ ({0, 1} : Set ℝ) ⊆ P ×ˢ Icc 0 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rcases ht with rfl | rfl <;> exact ⟨hx, by norm_num⟩
  refine ⟨g, hg, ?_⟩
  rw [← himage]
  exact hg.restrict hpoly hsub

open Classical in
theorem isPLThreeHandleAttachment_derivedNeighborhoodCell
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ s.card)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces)
    (k : Fin 4) (hcard : s.card = k.val + 1) :
    IsPLThreeHandleAttachment k (derivedNeighborhood K L) (derivedNeighborhoodCell K s).space
      (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space := by
  classical
  have hKw := hK.isCombinatorialManifoldWithBoundary
  fin_cases k
  · obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_vertex K L hKw hLK
      (fun t ht => by simpa [hcard] using hL t ht) hs hcard hsL
    exact isPLCellAttachment_derivedNeighborhoodCell K L hKw hLK hs hsL hproper
      (empty_subset _) hg hgB
  · obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_edge_pair K L hKw hLK
      (fun t ht => by simpa [hcard] using hL t ht) hs hcard hsL hproper
    apply isPLCellAttachment_derivedNeighborhoodCell K L hKw hLK hs hsL hproper ?_ hg hgB
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rcases ht with rfl | rfl <;> exact ⟨hx, by norm_num⟩
  · obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_triangle K L hK hLK
      (fun t ht => by simpa [hcard] using hL t ht) hs hcard hsL hproper
    exact isPLCellAttachment_derivedNeighborhoodCell K L hKw hLK hs hsL hproper
      (prod_mono (fun _ hx => hx.1) Subset.rfl) hg hgB
  · have hmax (t : Finset E) (ht : t ∈ K.faces) (hst : s ⊆ t) : s = t := by
      apply Finset.eq_of_subset_of_card_le hst
      have htcard := hK.card_le K ht
      simpa [hcard] using htcard
    obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_derivedNeighborhoodCell_maximal
      K L hK hLK hs hmax hsL hproper
    exact isPLCellAttachment_derivedNeighborhoodCell K L hKw hLK hs hsL hproper
      (fun _ hx => hx.1) hg hgB

end DifferentialGeometry.Topology.PiecewiseLinear
