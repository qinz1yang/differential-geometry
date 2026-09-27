import DifferentialGeometry.Topology.CylinderBoundarySide
import DifferentialGeometry.Topology.Compactness.ProductChartThickening

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology

private theorem collar_slice_subset_frontier_of_inter_nonempty
    {N M : Type*} [TopologicalSpace N] [PreconnectedSpace N]
    [TopologicalSpace M] (e : OpenPartialHomeomorph (N × ℝ) M)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    {K : Set M} (hregular : closure (interior K) = K)
    (hfront : frontier K ∩ e '' (univ ×ˢ Ioo (-r) r) ⊆
      range (fun q : N => e (q, 0)))
    (hmeet : (range (fun q : N => e (q, 0)) ∩ frontier K).Nonempty) :
    range (fun q : N => e (q, 0)) ⊆ frontier K := by
  let P := e '' (univ ×ˢ Ioo (0 : ℝ) r)
  let Q := e '' (univ ×ˢ Ioo (-r) (0 : ℝ))
  let O := e '' (univ ×ˢ Ioo (-r) r)
  have hK : IsClosed K := hregular ▸ isClosed_closure
  have hPsrc : univ ×ˢ Ioo (0 : ℝ) r ⊆ e.source :=
    fun q hq => hsource ⟨hq.1, (neg_lt_zero.mpr hr).trans hq.2.1, hq.2.2⟩
  have hQsrc : univ ×ˢ Ioo (-r) (0 : ℝ) ⊆ e.source :=
    fun q hq => hsource ⟨hq.1, hq.2.1, hq.2.2.trans hr⟩
  have hPc : IsPreconnected P :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hPsrc)
  have hQc : IsPreconnected Q :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hQsrc)
  have havoid (q : N) (t : ℝ) (ht : t ∈ Ioo (-r) r) (hne : t ≠ 0) :
      e (q, t) ∉ frontier K := by
    intro hf
    obtain ⟨w, hw⟩ := hfront ⟨hf, (q, t), ⟨mem_univ _, ht⟩, rfl⟩
    have he := e.injOn (hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩)
      (hsource ⟨mem_univ _, ht⟩) hw
    exact hne (congrArg Prod.snd he).symm
  have hPS : P ⊆ (frontier K)ᶜ := by
    rintro y ⟨⟨q, t⟩, ht, rfl⟩
    exact havoid q t ⟨(neg_lt_zero.mpr hr).trans ht.2.1, ht.2.2⟩ ht.2.1.ne'
  have hQS : Q ⊆ (frontier K)ᶜ := by
    rintro y ⟨⟨q, t⟩, ht, rfl⟩
    exact havoid q t ⟨ht.2.1, ht.2.2.trans hr⟩ ht.2.2.ne
  have hsplit : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isOpen_compl.interior_eq]
  have hPeither : P ⊆ interior K ∨ P ⊆ Kᶜ :=
    hPc.subset_or_subset isOpen_interior hK.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hPS.trans hsplit.subset)
  have hQeither : Q ⊆ interior K ∨ Q ⊆ Kᶜ :=
    hQc.subset_or_subset isOpen_interior hK.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hQS.trans hsplit.subset)
  have hOo : IsOpen O := e.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hsource
  have hzero (q : N) : e (q, 0) ∈ closure P ∩ closure Q := by
    have hp : (q, (0 : ℝ)) ∈ closure (univ ×ˢ Ioo (0 : ℝ) r : Set (N × ℝ)) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hr.ne]
      exact ⟨mem_univ _, le_rfl, hr.le⟩
    have hq : (q, (0 : ℝ)) ∈ closure (univ ×ˢ Ioo (-r) (0 : ℝ) : Set (N × ℝ)) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo (neg_lt_zero.mpr hr).ne]
      exact ⟨mem_univ _, neg_nonpos.mpr hr.le, le_rfl⟩
    have hc := e.continuousOn (q, 0) (hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩)
    exact ⟨(hc.mono hPsrc).mem_closure_image hp, (hc.mono hQsrc).mem_closure_image hq⟩
  have hparts : O ⊆ Q ∪ range (fun q : N => e (q, 0)) ∪ P := by
    rintro y ⟨⟨q, t⟩, ht, rfl⟩
    rcases lt_trichotomy t 0 with hn | he | hp
    · exact Or.inl (Or.inl ⟨(q, t), ⟨mem_univ _, ht.2.1, hn⟩, rfl⟩)
    · subst t
      exact Or.inl (Or.inr (mem_range_self q))
    · exact Or.inr ⟨(q, t), ⟨mem_univ _, hp, ht.2.2⟩, rfl⟩
  obtain ⟨x, ⟨q, rfl⟩, hx⟩ := hmeet
  have hxO : e (q, 0) ∈ O := ⟨(q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  have hnotIn : ¬ (P ⊆ interior K ∧ Q ⊆ interior K) := by
    rintro ⟨hP, hQ⟩
    have hzeroK : range (fun q : N => e (q, 0)) ⊆ K := by
      rintro y ⟨w, rfl⟩
      exact hK.closure_eq ▸ closure_mono (hP.trans interior_subset) (hzero w).1
    apply hx.2
    exact interior_maximal (fun y hy => by
      rcases hparts hy with (hyQ | hyZ) | hyP
      · exact interior_subset (hQ hyQ)
      · exact hzeroK hyZ
      · exact interior_subset (hP hyP)) hOo hxO
  have hnotOut : ¬ (P ⊆ Kᶜ ∧ Q ⊆ Kᶜ) := by
    rintro ⟨hP, hQ⟩
    have hzeroOut : range (fun q : N => e (q, 0)) ⊆ (interior K)ᶜ := by
      rintro y ⟨w, rfl⟩
      have hh : e (w, 0) ∈ closure Kᶜ := closure_mono hP (hzero w).1
      rwa [closure_compl] at hh
    have hxcl : e (q, 0) ∈ closure (interior K) := hregular.symm ▸ hK.frontier_subset hx
    obtain ⟨y, hyO, hyI⟩ := mem_closure_iff.mp hxcl O hOo hxO
    rcases hparts hyO with (hyQ | hyZ) | hyP
    · exact hQ hyQ (interior_subset hyI)
    · exact hzeroOut hyZ hyI
    · exact hP hyP (interior_subset hyI)
  rintro y ⟨w, rfl⟩
  rw [frontier_eq_closure_inter_closure]
  rcases hPeither with hP | hP <;> rcases hQeither with hQ | hQ
  · exact False.elim (hnotIn ⟨hP, hQ⟩)
  · exact ⟨closure_mono (hP.trans interior_subset) (hzero w).1,
      closure_mono hQ (hzero w).2⟩
  · exact ⟨closure_mono (hQ.trans interior_subset) (hzero w).2,
      closure_mono hP (hzero w).1⟩
  · exact False.elim (hnotOut ⟨hP, hQ⟩)

theorem frontier_eq_iUnion_of_finite_disjoint_collars
    {N M ι : Type*} [TopologicalSpace N] [CompactSpace N] [PreconnectedSpace N]
    [TopologicalSpace M] [T2Space M] [Finite ι]
    (e : ι → OpenPartialHomeomorph (N × ℝ) M)
    (hzero : ∀ i q, (q, (0 : ℝ)) ∈ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : N => e i (q, 0))) (range (fun q : N => e j (q, 0)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q : N => e i (q, 0))) :
    frontier K = ⋃ i ∈ {i | (range (fun q : N => e i (q, 0)) ∩ frontier K).Nonempty},
        range (fun q : N => e i (q, 0)) ∧
      ∀ i, (range (fun q : N => e i (q, 0)) ∩ frontier K).Nonempty →
        ∃ r σ : ℝ, 0 < r ∧ (σ = 1 ∨ σ = -1) ∧
          univ ×ˢ Ioo (-r) r ⊆ (e i).source ∧
          (∀ q : N, ∀ t ∈ Ioo (-r) r, e i (q, t) ∈ K ↔ σ * t ≤ 0) ∧
          ∀ q : N, ∀ t ∈ Ioo (-r) r, e i (q, t) ∈ interior K ↔ σ * t < 0 := by
  have hzeroset (i : ι) : e i '' (univ ×ˢ Icc (0 : ℝ) 0) =
      range (fun q : N => e i (q, 0)) := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      have ht0 : t = 0 := le_antisymm ht.2.2 ht.2.1
      subst t
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, le_rfl, le_rfl⟩, rfl⟩
  have hsource₀ (i : ι) : univ ×ˢ Icc (0 : ℝ) 0 ⊆ (e i).source := by
    rintro ⟨q, t⟩ ht
    have ht0 : t = 0 := le_antisymm ht.2.2 ht.2.1
    subst t
    exact hzero i q
  obtain ⟨l, r, hlr, hsource, hsep⟩ :=
    Compactness.exists_larger_product_chart_bands_preserving_disjointness
      e (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) hsource₀
      (fun i j => i ≠ j) (fun i j hij => by
        simpa only [hzeroset] using hdisjoint hij)
  let rad (i : ι) := min (-l i) (r i)
  have hrad (i : ι) : 0 < rad i := lt_min (neg_pos.mpr (hlr i).1) (hlr i).2
  have hsmall (i : ι) : (univ : Set N) ×ˢ Ioo (-rad i) (rad i) ⊆ univ ×ˢ Ioo (l i) (r i) := by
    intro x hx
    have hlo : rad i ≤ -l i := min_le_left _ _
    have hhi : rad i ≤ r i := min_le_right _ _
    exact ⟨hx.1, by linarith [hx.2.1], hx.2.2.trans_le hhi⟩
  have hsmallsource (i : ι) : univ ×ˢ Ioo (-rad i) (rad i) ⊆ (e i).source :=
    (hsmall i).trans (hsource i)
  have hslice (i : ι) : frontier K ∩ e i '' (univ ×ˢ Ioo (-rad i) (rad i)) ⊆
      range (fun q : N => e i (q, 0)) := by
    rintro x ⟨hxF, hxO⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hfrontier hxF)
    by_cases hji : j = i
    · exact hji ▸ hj
    · obtain ⟨q, rfl⟩ := hj
      have hzi : e j (q, 0) ∈ e j '' (univ ×ˢ Ioo (l j) (r j)) :=
        ⟨(q, 0), ⟨mem_univ _, (hlr j).1, (hlr j).2⟩, rfl⟩
      exact False.elim (disjoint_left.mp (hsep j i hji) hzi ((image_mono (hsmall i)) hxO))
  have hwhole (i : ι) (hi : (range (fun q : N => e i (q, 0)) ∩ frontier K).Nonempty) :
      range (fun q : N => e i (q, 0)) ⊆ frontier K :=
    collar_slice_subset_frontier_of_inter_nonempty (e i) (hrad i)
      (hsmallsource i) hregular (hslice i) hi
  constructor
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hfrontier hx)
      exact mem_iUnion₂.mpr ⟨i, ⟨x, hi, hx⟩, hi⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact hwhole i hi hxi
  intro i hi
  have hfront : frontier K ∩ e i '' (univ ×ˢ Ioo (-rad i) (rad i)) =
      range (fun q : N => e i (q, 0)) := by
    apply (hslice i).antisymm
    rintro x ⟨q, rfl⟩
    exact ⟨hwhole i hi (mem_range_self q), (q, 0),
      ⟨mem_univ _, neg_lt_zero.mpr (hrad i), hrad i⟩, rfl⟩
  have hN : Nonempty N := by
    obtain ⟨_, ⟨q, _⟩, _⟩ := hi
    exact ⟨q⟩
  let := hN
  have hclosed : IsClosed K := hregular ▸ isClosed_closure
  obtain hor | hor := exists_cylinder_orientation_of_frontier_inter_image_eq
    (e i) (hrad i) (hsmallsource i) hregular hfront
  · refine ⟨rad i, 1, hrad i, Or.inl rfl, hsmallsource i, ?_, ?_⟩
    · intro q t ht
      simp only [one_mul]
      rcases lt_trichotomy t 0 with hn | rfl | hp
      · have hh := (hor q (-t) ⟨by linarith, by linarith [ht.1]⟩).2
        rw [neg_neg] at hh
        exact iff_of_true (interior_subset hh) hn.le
      · exact iff_of_true (hclosed.frontier_subset (hwhole i hi (mem_range_self q))) le_rfl
      · exact iff_of_false (hor q t ⟨hp, ht.2⟩).1 (not_le.mpr hp)
    · intro q t ht
      simp only [one_mul]
      rcases lt_trichotomy t 0 with hn | rfl | hp
      · have hh := (hor q (-t) ⟨by linarith, by linarith [ht.1]⟩).2
        rw [neg_neg] at hh
        exact iff_of_true hh hn
      · exact iff_of_false (hwhole i hi (mem_range_self q)).2 (lt_irrefl _)
      · exact iff_of_false (fun hh => (hor q t ⟨hp, ht.2⟩).1 (interior_subset hh))
          (not_lt.mpr hp.le)
  · refine ⟨rad i, -1, hrad i, Or.inr rfl, hsmallsource i, ?_, ?_⟩
    · intro q t ht
      simp only [neg_one_mul]
      rcases lt_trichotomy t 0 with hn | rfl | hp
      · have hh := (hor q (-t) ⟨by linarith, by linarith [ht.1]⟩).1
        rw [neg_neg] at hh
        exact iff_of_false hh (by linarith)
      · exact iff_of_true (hclosed.frontier_subset (hwhole i hi (mem_range_self q))) (by simp)
      · exact iff_of_true (interior_subset (hor q t ⟨hp, ht.2⟩).2) (by linarith)
    · intro q t ht
      simp only [neg_one_mul]
      rcases lt_trichotomy t 0 with hn | rfl | hp
      · have hh := (hor q (-t) ⟨by linarith, by linarith [ht.1]⟩).1
        rw [neg_neg] at hh
        exact iff_of_false (fun hh' => hh (interior_subset hh')) (by linarith)
      · exact iff_of_false (hwhole i hi (mem_range_self q)).2 (by simp)
      · exact iff_of_true (hor q t ⟨hp, ht.2⟩).2 (by linarith)

end DifferentialGeometry.Topology
