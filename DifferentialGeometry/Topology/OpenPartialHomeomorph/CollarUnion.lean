import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import DifferentialGeometry.Topology.Compactness.ProductChartThickening
import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Topology.Order.DenselyOrdered

open Set

namespace OpenPartialHomeomorph

variable {N M : Type*} [TopologicalSpace N] [CompactSpace N] [PreconnectedSpace N]
  [TopologicalSpace M] [T2Space M]

theorem image_upper_boundary_subset_interior_union
    (e : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hs : univ ×ˢ Icc a b ⊆ e.source) {B T : Set M}
    (hB : closure (interior B) = B) (hT : IsClosed T)
    (hdis : Disjoint (interior (e '' (univ ×ˢ Icc a b))) (interior B))
    (hSB : e '' (univ ×ˢ ({b} : Set ℝ)) ⊆ B)
    (hfront : frontier B ⊆ e '' (univ ×ˢ ({b} : Set ℝ)) ∪ T)
    (hST : Disjoint (e '' (univ ×ˢ ({b} : Set ℝ))) T) :
    e '' (univ ×ˢ ({b} : Set ℝ)) ⊆ interior (e '' (univ ×ˢ Icc a b) ∪ B) := by
  have hA : closure (interior (e '' (univ ×ˢ Icc a b))) =
      e '' (univ ×ˢ Icc a b) := by
    apply e.closure_interior_image_of_subset_source hs _
      ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn (e.continuousOn.mono hs)).isClosed
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq, closure_univ,
      closure_Ioo hab.ne]
  have hdis' := hdis.closure_left isOpen_interior
  rw [hA] at hdis'
  have hbsource : univ ×ˢ Icc b b ⊆ e.source := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact hs ⟨hp, hab.le.trans ht.1, ht.2⟩
  have hbT : e '' (univ ×ˢ Icc b b) ⊆ Tᶜ := by
    rintro z ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩ hzT
    exact Set.disjoint_left.mp hST ⟨(p, t), ⟨hp, le_antisymm ht.2 ht.1⟩, rfl⟩ hzT
  obtain ⟨l, r, hl, hr, hsrc, himg⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band
      e (le_refl b) hbsource hT.isOpen_compl hbT
  let low := max a l
  have hlow : low < b := max_lt hab hl
  have hband : univ ×ˢ Ioo low r ⊆ e.source :=
    fun z hz => hsrc ⟨hz.1, (le_max_right a l).trans_lt hz.2.1, hz.2.2⟩
  have havoid : e '' (univ ×ˢ Ioo low r) ⊆ Tᶜ := by
    apply Subset.trans (image_mono _) himg
    intro z hz
    exact ⟨hz.1, (le_max_right a l).trans_lt hz.2.1, hz.2.2⟩
  have hopen : IsOpen (e '' (univ ×ˢ Ioo low r)) :=
    e.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hband
  have hside : univ ×ˢ Ioo b r ⊆ e.source :=
    fun z hz => hband ⟨hz.1, hlow.trans hz.2.1, hz.2.2⟩
  have hconn : IsPreconnected (e '' (univ ×ˢ Ioo b r)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _ (e.continuousOn.mono hside)
  have hsidefront : Disjoint (e '' (univ ×ˢ Ioo b r)) (frontier B) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨p, t⟩, ht, rfl⟩ hz
    rcases hfront hz with hz | hz
    · obtain ⟨⟨q, u⟩, hu, heq⟩ := hz
      have hub : u = b := hu.2
      have heq' := e.injOn (hs ⟨hu.1, by rw [hub]; exact ⟨hab.le, le_rfl⟩⟩)
        (hside ht) heq
      have hut : u = t := congrArg Prod.snd heq'
      exact (ne_of_lt ht.2.1) (hub.symm.trans hut)
    · exact havoid ⟨(p, t), ⟨ht.1, hlow.trans ht.2.1, ht.2.2⟩, rfl⟩ hz
  rintro z ⟨⟨p, t⟩, ht, rfl⟩
  have ht0 : t = b := ht.2
  subst t
  have hzB : e (p, b) ∈ closure (interior B) := by
    rw [hB]
    exact hSB ⟨(p, b), ⟨mem_univ _, rfl⟩, rfl⟩
  have hzU : e (p, b) ∈ e '' (univ ×ˢ Ioo low r) :=
    ⟨(p, b), ⟨mem_univ _, hlow, hr⟩, rfl⟩
  obtain ⟨y, hyU, hyB⟩ := mem_closure_iff.mp hzB _ hopen hzU
  obtain ⟨⟨q, u⟩, hu, rfl⟩ := hyU
  have hbu : b < u := by
    by_contra h
    exact Set.disjoint_left.mp hdis'
      ⟨(q, u), ⟨hu.1, (le_max_left a l).trans hu.2.1.le, le_of_not_gt h⟩, rfl⟩ hyB
  have hsideB : e '' (univ ×ˢ Ioo b r) ⊆ interior B :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hconn hsidefront ⟨e (q, u), ⟨(q, u), ⟨hu.1, hbu, hu.2.2⟩, rfl⟩, hyB⟩
  apply mem_interior.mpr
  refine ⟨e '' (univ ×ˢ Ioo low r), ?_, hopen, hzU⟩
  rintro y ⟨⟨q, v⟩, hv, rfl⟩
  rcases le_or_gt v b with hvb | hvb
  · exact Or.inl ⟨(q, v), ⟨hv.1, (le_max_left a l).trans hv.2.1.le, hvb⟩, rfl⟩
  · exact Or.inr (interior_subset (hsideB ⟨(q, v), ⟨hv.1, hvb, hv.2.2⟩, rfl⟩))

end OpenPartialHomeomorph
