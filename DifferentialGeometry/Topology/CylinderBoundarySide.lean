import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]

theorem positive_cylinder_subset_compl_of_frontier_eq
    (T : OpenPartialHomeomorph (X × ℝ) Y) {r : ℝ} (hr : 0 < r)
    (hsource : univ ×ˢ Ioo (-r) r ⊆ T.source) {K : Set Y} (hK : IsClosed K)
    (hfront : frontier K = range (fun q : X => T (q, 0)))
    (hout : (T '' (univ ×ˢ Ioo (0 : ℝ) r) \ K).Nonempty) :
    T '' (univ ×ˢ Ioo (0 : ℝ) r) ⊆ Kᶜ := by
  let A := T '' (univ ×ˢ Ioo (0 : ℝ) r)
  have hpos : univ ×ˢ Ioo (0 : ℝ) r ⊆ T.source :=
    fun q hq => hsource ⟨hq.1, (neg_lt_zero.mpr hr).trans hq.2.1, hq.2.2⟩
  have hconn : IsPreconnected A :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image T (T.continuousOn.mono hpos)
  have hdisjoint : Disjoint A (frontier Kᶜ) := by
    rw [frontier_compl, hfront, Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ ⟨q, hq⟩
    have hzero : (q, (0 : ℝ)) ∈ T.source :=
      hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩
    have heq := T.injOn hzero (hpos hz) hq
    have he := congrArg Prod.snd heq
    exact hz.2.1.ne' he.symm
  obtain ⟨y, hyA, hyout⟩ := hout
  exact (subset_interior_of_isPreconnected_of_disjoint_frontier hconn hdisjoint
    ⟨y, hyA, hK.isOpen_compl.interior_eq.symm ▸ hyout⟩).trans interior_subset

theorem exists_cylinder_orientation_of_frontier_inter_image_eq [Nonempty X]
    (T : OpenPartialHomeomorph (X × ℝ) Y) {r : ℝ} (hr : 0 < r)
    (hsource : univ ×ˢ Ioo (-r) r ⊆ T.source) {K : Set Y}
    (hregular : closure (interior K) = K)
    (hfront : frontier K ∩ T '' (univ ×ˢ Ioo (-r) r) =
      range (fun q : X => T (q, 0))) :
    (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, s) ∉ K ∧ T (q, -s) ∈ interior K) ∨
      (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, -s) ∉ K ∧ T (q, s) ∈ interior K) := by
  classical
  let P := T '' (univ ×ˢ Ioo (0 : ℝ) r)
  let N := T '' (univ ×ˢ Ioo (-r) (0 : ℝ))
  let O := T '' (univ ×ˢ Ioo (-r) r)
  have hK : IsClosed K := hregular ▸ isClosed_closure
  have hPsrc : univ ×ˢ Ioo (0 : ℝ) r ⊆ T.source :=
    fun q hq => hsource ⟨hq.1, (neg_lt_zero.mpr hr).trans hq.2.1, hq.2.2⟩
  have hNsrc : univ ×ˢ Ioo (-r) (0 : ℝ) ⊆ T.source :=
    fun q hq => hsource ⟨hq.1, hq.2.1, hq.2.2.trans hr⟩
  have hPc : IsPreconnected P :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image T (T.continuousOn.mono hPsrc)
  have hNc : IsPreconnected N :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image T (T.continuousOn.mono hNsrc)
  have havoid (q : X) (a : ℝ) (ha : a ∈ Ioo (-r) r) (hne : a ≠ 0) :
      T (q, a) ∉ frontier K := by
    intro hf
    obtain ⟨w, hw⟩ := hfront ▸
      (show T (q, a) ∈ frontier K ∩ T '' (univ ×ˢ Ioo (-r) r) from
        ⟨hf, (q, a), ⟨mem_univ _, ha⟩, rfl⟩)
    have he := T.injOn (hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩)
      (hsource ⟨mem_univ _, ha⟩) hw
    exact hne (congrArg Prod.snd he).symm
  have hPS : P ⊆ (frontier K)ᶜ := by
    rintro y ⟨⟨q, a⟩, ha, rfl⟩
    exact havoid q a ⟨(neg_lt_zero.mpr hr).trans ha.2.1, ha.2.2⟩ ha.2.1.ne'
  have hNS : N ⊆ (frontier K)ᶜ := by
    rintro y ⟨⟨q, a⟩, ha, rfl⟩
    exact havoid q a ⟨ha.2.1, ha.2.2.trans hr⟩ ha.2.2.ne
  have hsplit : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isOpen_compl.interior_eq]
  have hPeither : P ⊆ interior K ∨ P ⊆ Kᶜ :=
    hPc.subset_or_subset isOpen_interior hK.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hPS.trans hsplit.subset)
  have hNeither : N ⊆ interior K ∨ N ⊆ Kᶜ :=
    hNc.subset_or_subset isOpen_interior hK.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hNS.trans hsplit.subset)
  have hOo : IsOpen O := T.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsource
  let q : X := Classical.choice inferInstance
  have hzeroFront (w : X) : T (w, 0) ∈ frontier K :=
    (hfront.symm ▸ mem_range_self w : T (w, 0) ∈ frontier K ∩
      T '' (univ ×ˢ Ioo (-r) r)).1
  have hqfront : T (q, 0) ∈ frontier K := hzeroFront q
  have hqO : T (q, 0) ∈ O := ⟨(q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  have hOparts : O ⊆ (N ∪ frontier K) ∪ P := by
    rintro y ⟨⟨w, a⟩, ha, rfl⟩
    rcases lt_trichotomy a 0 with hn | he | hp
    · exact Or.inl (Or.inl ⟨(w, a), ⟨mem_univ _, ha.2.1, hn⟩, rfl⟩)
    · subst a
      exact Or.inl (Or.inr (hzeroFront w))
    · exact Or.inr ⟨(w, a), ⟨mem_univ _, hp, ha.2.2⟩, rfl⟩
  have hnotIn : ¬ (P ⊆ interior K ∧ N ⊆ interior K) := by
    rintro ⟨hP, hN⟩
    have hcl : T (q, 0) ∈ closure Kᶜ := by
      apply frontier_subset_closure
      rwa [frontier_compl]
    obtain ⟨y, hyO, hyout⟩ := mem_closure_iff.mp hcl O hOo hqO
    rcases hOparts hyO with (hyN | hyF) | hyP
    · exact hyout (interior_subset (hN hyN))
    · exact hyout (hK.frontier_subset hyF)
    · exact hyout (interior_subset (hP hyP))
  have hnotOut : ¬ (P ⊆ Kᶜ ∧ N ⊆ Kᶜ) := by
    rintro ⟨hP, hN⟩
    have hcl : T (q, 0) ∈ closure (interior K) := hregular.symm ▸ hK.frontier_subset hqfront
    obtain ⟨y, hyO, hyin⟩ := mem_closure_iff.mp hcl O hOo hqO
    rcases hOparts hyO with (hyN | hyF) | hyP
    · exact hN hyN (interior_subset hyin)
    · exact disjoint_interior_frontier.le_bot ⟨hyin, hyF⟩
    · exact hP hyP (interior_subset hyin)
  rcases hPeither with hP | hP
  · rcases hNeither with hN | hN
    · exact (hnotIn ⟨hP, hN⟩).elim
    · refine Or.inr (fun q s hs => ⟨?_, hP ⟨(q, s), ⟨mem_univ _, hs⟩, rfl⟩⟩)
      exact hN ⟨(q, -s), ⟨mem_univ _, neg_lt_neg hs.2, neg_lt_zero.mpr hs.1⟩, rfl⟩
  · rcases hNeither with hN | hN
    · refine Or.inl (fun q s hs => ⟨hP ⟨(q, s), ⟨mem_univ _, hs⟩, rfl⟩, ?_⟩)
      exact hN ⟨(q, -s), ⟨mem_univ _, neg_lt_neg hs.2, neg_lt_zero.mpr hs.1⟩, rfl⟩
    · exact (hnotOut ⟨hP, hN⟩).elim

theorem exists_cylinder_orientation_of_frontier_eq [Nonempty X]
    (T : OpenPartialHomeomorph (X × ℝ) Y) {r : ℝ} (hr : 0 < r)
    (hsource : univ ×ˢ Ioo (-r) r ⊆ T.source) {K : Set Y}
    (hregular : closure (interior K) = K)
    (hfront : frontier K = range (fun q : X => T (q, 0))) :
    (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, s) ∉ K ∧ T (q, -s) ∈ interior K) ∨
      (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, -s) ∉ K ∧ T (q, s) ∈ interior K) := by
  apply exists_cylinder_orientation_of_frontier_inter_image_eq T hr hsource hregular
  rw [hfront]
  apply inter_eq_left.mpr
  rintro y ⟨q, rfl⟩
  exact ⟨(q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩

end DifferentialGeometry.Topology
