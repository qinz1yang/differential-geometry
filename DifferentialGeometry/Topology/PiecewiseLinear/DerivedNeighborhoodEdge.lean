/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem disjoint_derivedNeighborhoodCell_of_card_eq
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hcard : s.card = t.card) (hne : s ≠ t) :
    Disjoint (derivedNeighborhoodCell K s).space (derivedNeighborhoodCell K t).space :=
  disjoint_derivedNeighborhoodCell_space K hs ht
    (fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge))
    (fun h => hne (Finset.eq_of_subset_of_card_le h hcard.le).symm)

open Classical in
theorem derivedNeighborhoodCell_edge_inter_iUnion
    (K : Geometry.SimplicialComplex ℝ E) {a b : E} (hab : a ≠ b)
    (he : {a, b} ∈ K.faces) (d : Finset (Finset E))
    (hd : ∀ s ∈ d, s ∈ K.faces ∧ s.card ≤ 2) (hed : {a, b} ∉ d)
    (ha : {a} ∈ d) (hb : {b} ∈ d) :
    (derivedNeighborhoodCell K {a, b}).space ∩
        (⋃ s ∈ d, (derivedNeighborhoodCell K s).space) =
      (derivedNeighborhoodCell K {a, b}).space ∩ (derivedNeighborhoodCell K {a}).space ∪
        (derivedNeighborhoodCell K {a, b}).space ∩ (derivedNeighborhoodCell K {b}).space := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hxe, hx⟩
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    have hne : s ≠ {a, b} := fun h => hed (h ▸ hs)
    have hsub : s ⊆ {a, b} := by
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
        (hd s hs).1 he ⟨x, hxs, hxe⟩ with h | h
      · exact h
      · exact (hne (Finset.eq_of_subset_of_card_le h
          (by simpa [hab] using (hd s hs).2)).symm).elim
    have hvertices : s = {a} ∨ s = {b} := by
      obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hd s hs).1
      have hv' : v = a ∨ v = b := by simpa using hsub hv
      rcases hv' with hva | hvb
      · have has : a ∈ s := hva ▸ hv
        left
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨has, fun w hw => ?_⟩
        have hw' : w = a ∨ w = b := by simpa using hsub hw
        rcases hw' with hwa | hwb
        · exact hwa
        · have hbs : b ∈ s := hwb ▸ hw
          exact (hne (Finset.Subset.antisymm hsub
            (Finset.insert_subset_iff.mpr ⟨has, Finset.singleton_subset_iff.mpr hbs⟩))).elim
      · have hbs : b ∈ s := hvb ▸ hv
        right
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hbs, fun w hw => ?_⟩
        have hw' : w = a ∨ w = b := by simpa using hsub hw
        rcases hw' with hwa | hwb
        · have has : a ∈ s := hwa ▸ hw
          exact (hne (Finset.Subset.antisymm hsub
            (Finset.insert_subset_iff.mpr ⟨has, Finset.singleton_subset_iff.mpr hbs⟩))).elim
        · exact hwb
    rcases hvertices with rfl | rfl
    · exact Or.inl ⟨hxe, hxs⟩
    · exact Or.inr ⟨hxe, hxs⟩
  · rintro x (⟨hxe, hxa⟩ | ⟨hxe, hxb⟩)
    · exact ⟨hxe, mem_iUnion₂.mpr ⟨{a}, ha, hxa⟩⟩
    · exact ⟨hxe, mem_iUnion₂.mpr ⟨{b}, hb, hxb⟩⟩

open Classical in
theorem exists_isPLHomeomorphOn_derivedNeighborhoodCell_edge
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {a b : E} (hab : a ≠ b)
    (he : {a, b} ∈ K.faces) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc 0 1)
        (derivedNeighborhoodCell K {a, b}).space ∧
      g '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {0}) =
        (derivedNeighborhoodCell K {a, b}).space ∩ (derivedNeighborhoodCell K {a}).space ∧
      g '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {1}) =
        (derivedNeighborhoodCell K {a, b}).space ∩ (derivedNeighborhoodCell K {b}).space := by
  classical
  have ha : {a} ∈ K.faces := K.down_closed he (by simp) (Finset.singleton_nonempty a)
  have hb : {b} ∈ K.faces := K.down_closed he (by simp) (Finset.singleton_nonempty b)
  have hea : ({a, b} : Finset E) ≠ {a} := by simpa [Finset.ext_iff] using hab.symm
  have heb : ({a, b} : Finset E) ≠ {b} := by simpa [Finset.ext_iff] using hab
  have hDa := hK.isPLBall_derivedNeighborhoodCell_inter he ha hea (Or.inr (by simp))
  have hDb := hK.isPLBall_derivedNeighborhoodCell_inter he hb heb (Or.inr (by simp))
  have hdis := disjoint_derivedNeighborhoodCell_of_card_eq K ha hb
    (by simp) (by simpa using hab)
  obtain ⟨f, hf⟩ := hDa
  let _ : Finite (derivedNeighborhoodCell K {a, b}).faces :=
    (derivedNeighborhoodCell_faces_finite K _).to_subtype
  obtain ⟨g, hg, hg0, hg1⟩ := exists_isPLHomeomorphOn_prism_map_ends
    (isPLBall_stdSimplex 2) (by norm_num : (0 : ℝ) < 1)
    (derivedNeighborhoodCell K {a, b}) (hK.isPLBall_derivedNeighborhoodCell he)
    (hK.derivedNeighborhoodCell_inter_subset_boundaryComplex he ha hea) hDb
    (hK.derivedNeighborhoodCell_inter_subset_boundaryComplex he hb heb)
    (hdis.mono inter_subset_right inter_subset_right) hf
  refine ⟨g, hg, ?_, hg1⟩
  have h0 : EqOn (g ∘ fun x => (x, (0 : ℝ))) f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hg0
  rw [← (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_prod_const (0 : ℝ) |>.image_eq,
    image_image]
  exact h0.image_eq.trans hf.image_eq

end DifferentialGeometry.Topology.PiecewiseLinear
