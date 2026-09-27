import DifferentialGeometry.Topology.PiecewiseLinear.ConeBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem frontier_coneComplex_inter_convexHull_insert [dE : DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 2) (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    {p : E} (hp : IsConeBase p L) (hL : IsPLBall (n + 1) L.space)
    {t s : Finset E} (ht : t ∈ L.faces) (hs : s.Nonempty)
    (htrace : (boundaryComplex (n + 1) L).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    frontier (coneComplex hp).space ∩ convexHull ℝ ((insert p t : Finset E) : Set E) =
      convexHull ℝ (t : Set E) ∪
        ⋃ v ∈ s, convexHull ℝ ((insert p (t.erase v) : Finset E) : Set E) := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let hpB := hp.of_faces_subset (boundaryComplex_faces_subset (n + 1) L)
  have hpt : p ∉ t := hp.notMem_face ht
  have hapex : p ∈ ⋃ v ∈ s, convexHull ℝ ((insert p (t.erase v) : Finset E) : Set E) := by
    obtain ⟨v, hv⟩ := hs
    exact mem_iUnion₂.mpr ⟨v, hv, subset_convexHull ℝ _ (Finset.mem_insert_self _ _)⟩
  rw [frontier_coneComplex hn hp hL]
  apply Subset.antisymm
  · rintro x ⟨hxL | hxB, hxT⟩
    · rcases exists_combo_of_mem_convexHull_insert hpt hxT with rfl | ⟨z, hz, r, hr, -, hxr⟩
      · exact (hp.notMem_space hxL).elim
      · have hxz := hp.radial z (L.convexHull_subset_space ht hz) x hxL r hr hxr
        exact Or.inl (hxz.symm ▸ hz)
    · rcases (mem_coneComplex_space_iff hpB).mp hxB with rfl | ⟨z, hz, r, hr, hr1, rfl⟩
      · exact Or.inr hapex
      · rcases exists_combo_of_mem_convexHull_insert hpt hxT with hxp | ⟨w, hw, q, hq, -, hxq⟩
        · rw [hxp]
          exact Or.inr hapex
        · have hzw := hp.radial.eq_of_add_smul_eq (boundaryComplex_space_subset (n + 1) L hz)
            (L.convexHull_subset_space ht hw) hr hq hxq
          have hzT : z ∈ convexHull ℝ (t : Set E) := hzw.symm ▸ hw
          obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp (htrace ▸ (show z ∈
            (boundaryComplex (n + 1) L).space ∩ convexHull ℝ (t : Set E) from ⟨hz, hzT⟩))
          exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, mem_convexHull_insert_of_combo hzv hr.le hr1⟩)
  · rintro x (hxT | hxR)
    · exact ⟨Or.inl (L.convexHull_subset_space ht hxT),
        convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p t)) hxT⟩
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxR
      have hxT := convexHull_mono (Finset.coe_subset.mpr
        (Finset.insert_subset_insert p (Finset.erase_subset v t))) hxv
      refine ⟨Or.inr ?_, hxT⟩
      rcases exists_combo_of_mem_convexHull_insert (show p ∉ t.erase v from
        fun h => hpt (Finset.mem_of_mem_erase h)) hxv with rfl | ⟨z, hz, r, hr, hr1, rfl⟩
      · exact apex_mem_coneComplex_space hpB
      · have hzB : z ∈ (boundaryComplex (n + 1) L).space :=
          (htrace.symm ▸ (show z ∈ ⋃ w ∈ s, convexHull ℝ ((t.erase w : Finset E) : Set E) from
            mem_iUnion₂.mpr ⟨v, hv, hz⟩)).1
        exact (mem_coneComplex_space_iff hpB).mpr (Or.inr ⟨z, hzB, r, hr, hr1, rfl⟩)

theorem isPLBall_frontier_coneComplex_inter_convexHull_insert [dE : DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 2) (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    {p : E} (hp : IsConeBase p L) (hL : IsPLBall (n + 1) L.space)
    {t s : Finset E} (ht : t ∈ L.faces) (htcard : t.card = n + 2)
    (hs : s.Nonempty) (hst : s ⊆ t) (hsne : s ≠ t)
    (htrace : (boundaryComplex (n + 1) L).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E)) :
    IsPLBall (n + 1) (frontier (coneComplex hp).space ∩
      convexHull ℝ ((insert p t : Finset E) : Set E)) := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hpt : p ∉ t := hp.notMem_face ht
  have hps : p ∉ s := fun h => hpt (hst h)
  have hT : AffineIndependent ℝ ((↑) : ↥(insert p t : Finset E) → E) := by
    have h := hp.indep t ht
    rwa [← Finset.coe_insert] at h
  have hTcard : (insert p t).card = (n + 1) + 2 := by
    rw [Finset.card_insert_of_notMem hpt, htcard]
  have hsT : insert p s ⊆ insert p t := Finset.insert_subset_insert p hst
  have hne : insert p s ≠ insert p t := by
    intro heq
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hsne⟩)
    have hc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hps, Finset.card_insert_of_notMem hpt] at hc
    omega
  have hball := isPLBall_simplexAvoiding_singleton hT hTcard hsT (Finset.insert_nonempty p s) hne
  rw [simplexAvoiding_singleton_space] at hball
  rw [frontier_coneComplex_inter_convexHull_insert hn L hp hL ht hs htrace]
  have heq : (⋃ v ∈ insert p s, convexHull ℝ (((insert p t).erase v : Finset E) : Set E)) =
      convexHull ℝ (t : Set E) ∪
        ⋃ v ∈ s, convexHull ℝ ((insert p (t.erase v) : Finset E) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl (by simpa only [Finset.erase_insert hpt] using hxv)
      · exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv hps).symm] using hxv⟩)
    · rintro (hx | hx)
      · exact mem_iUnion₂.mpr ⟨p, Finset.mem_insert_self p s, by
          simpa only [Finset.erase_insert hpt] using hx⟩
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨v, Finset.mem_insert_of_mem hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv hps).symm] using hxv⟩
  exact heq ▸ hball

end DifferentialGeometry.Topology.PiecewiseLinear
