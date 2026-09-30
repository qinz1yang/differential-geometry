import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact

open Set Topology

namespace OpenPartialHomeomorph

variable {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
  [CompactSpace N] [T2Space M]

theorem exists_half_collar_retraction
    (T : OpenPartialHomeomorph (N × ℝ) M) {r d : ℝ}
    (hd : 0 < d) (hdr : d < r)
    (hsource : (univ : Set N) ×ˢ Icc 0 r ⊆ T.source)
    {V : Set M} (hzero : Disjoint (range fun q : N => T (q, 0)) V)
    (hpos : T '' ((univ : Set N) ×ˢ Ioo 0 r) ⊆ V) :
    ∃ f : M → M, ContinuousOn f V ∧
      MapsTo f V (V \ T '' ((univ : Set N) ×ˢ Ioo 0 d)) ∧
      (∀ q t, t ∈ Ioo 0 r → f (T (q, t)) = T (q, max d t)) ∧
      EqOn f id (T '' ((univ : Set N) ×ˢ Ioo 0 d))ᶜ ∧
      f '' V = V \ T '' ((univ : Set N) ×ˢ Ioo 0 d) ∧
      MapsTo f (T '' ((univ : Set N) ×ˢ Icc 0 d))
        (T '' ((univ : Set N) ×ˢ Icc 0 d)) := by
  classical
  let H : Set M := T '' ((univ : Set N) ×ˢ Ioo 0 r)
  let K : Set M := T '' ((univ : Set N) ×ˢ Icc 0 d)
  have hsH : (univ : Set N) ×ˢ Ioo 0 r ⊆ T.source := by
    intro z hz
    exact hsource ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hsK : (univ : Set N) ×ˢ Icc 0 d ⊆ T.source := by
    intro z hz
    exact hsource ⟨hz.1, hz.2.1, hz.2.2.trans hdr.le⟩
  have hH : IsOpen H := T.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsH
  have hK : IsClosed K := ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (T.continuousOn.mono hsK)).isClosed
  have hHt : H ⊆ T.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact T.map_source (hsH hz)
  have hHinv : ∀ x ∈ H, (T.symm x).2 ∈ Ioo 0 r := by
    rintro _ ⟨z, hz, rfl⟩
    rw [T.left_inv (hsH hz)]
    exact hz.2
  let F : M → M := fun x => T ((T.symm x).1, max d (T.symm x).2)
  let f : M → M := fun x => if x ∈ H then F x else x
  have hF : ContinuousOn F H := by
    apply T.continuousOn.comp
      ((T.continuousOn_symm.mono hHt).fst.prodMk
        (continuousOn_const.sup (T.continuousOn_symm.mono hHt).snd))
    intro x hx
    exact hsource ⟨mem_univ _, hd.le.trans (le_max_left _ _),
      (max_lt hdr (hHinv x hx).2).le⟩
  have hfeq : ∀ x ∈ H, f x = F x := by
    intro x hx
    exact ite_eq_left hx
  have hfix : EqOn f id Kᶜ := by
    intro x hx
    change f x = x
    by_cases hxH : x ∈ H
    · have hxd : d ≤ (T.symm x).2 := by
        by_contra h
        apply hx
        refine ⟨T.symm x, ⟨mem_univ _, (hHinv x hxH).1.le, (lt_of_not_ge h).le⟩, ?_⟩
        exact T.right_inv (hHt hxH)
      rw [hfeq x hxH]
      dsimp [F]
      rw [max_eq_right hxd]
      exact T.right_inv (hHt hxH)
    · exact ite_eq_right hxH
  have hfc : ContinuousOn f V := by
    intro x hx
    by_cases hxK : x ∈ K
    · obtain ⟨z, hz, rfl⟩ := hxK
      have hzt : 0 < z.2 := by
        have hn : z.2 ≠ 0 := by
          intro he
          exact Set.disjoint_left.1 hzero ⟨z.1, by rw [← he]⟩ hx
        exact lt_of_le_of_ne hz.2.1 (Ne.symm hn)
      have hxH : T z ∈ H := ⟨z, ⟨hz.1, hzt, hz.2.2.trans_lt hdr⟩, rfl⟩
      have hcont : ContinuousAt F (T z) := (hF (T z) hxH).continuousAt (hH.mem_nhds hxH)
      apply (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hH.mem_nhds hxH] with y hy
      exact hfeq y hy
    · have hcont : ContinuousAt (id : M → M) x := continuousAt_id
      apply (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      exact hfix hy
  have hformula : ∀ q t, t ∈ Ioo 0 r → f (T (q, t)) = T (q, max d t) := by
    intro q t ht
    rw [hfeq _ ⟨(q, t), ⟨mem_univ _, ht⟩, rfl⟩]
    dsimp [F]
    rw [T.left_inv (hsH ⟨mem_univ _, ht⟩)]
  have hfixSmall : EqOn f id (T '' ((univ : Set N) ×ˢ Ioo 0 d))ᶜ := by
    intro x hx
    by_cases hxH : x ∈ H
    · obtain ⟨z, hz, rfl⟩ := hxH
      have hdz : d ≤ z.2 := by
        by_contra hn
        exact hx ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge hn⟩, rfl⟩
      rw [hformula z.1 z.2 hz.2, max_eq_right hdz]
      rfl
    · exact ite_eq_right hxH
  have hmaps : MapsTo f V (V \ T '' ((univ : Set N) ×ˢ Ioo 0 d)) := by
    intro x hx
    by_cases hxH : x ∈ H
    · obtain ⟨z, hz, rfl⟩ := hxH
      rw [hformula z.1 z.2 hz.2]
      refine ⟨hpos ⟨(z.1, max d z.2), ⟨mem_univ _,
        hd.trans_le (le_max_left _ _), max_lt hdr hz.2.2⟩, rfl⟩, ?_⟩
      rintro ⟨w, hw, he⟩
      have hwsrc : w ∈ T.source := hsource ⟨hw.1, hw.2.1.le, hw.2.2.le.trans hdr.le⟩
      have hzsrc : (z.1, max d z.2) ∈ T.source := hsource ⟨mem_univ _,
        hd.le.trans (le_max_left _ _), (max_lt hdr hz.2.2).le⟩
      have hcoord := congrArg Prod.snd (T.injOn hwsrc hzsrc he)
      have hlt : max d z.2 < d := by
        simpa only [hcoord] using hw.2.2
      exact (not_lt_of_ge (le_max_left d z.2)) hlt
    · have hfx : f x = x := ite_eq_right hxH
      rw [hfx]
      refine ⟨hx, ?_⟩
      rintro ⟨z, hz, he⟩
      exact hxH ⟨z, ⟨hz.1, hz.2.1, hz.2.2.trans hdr⟩, he⟩
  refine ⟨f, hfc, hmaps, hformula, hfixSmall, ?_, ?_⟩
  · apply subset_antisymm hmaps.image_subset
    intro x hx
    exact ⟨x, hx.1, hfixSmall hx.2⟩
  · intro x hx
    by_cases hxH : x ∈ H
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzt : 0 < z.2 := by
        have he := hHinv _ hxH
        rw [T.left_inv (hsK hz)] at he
        exact he.1
      rw [hformula z.1 z.2 ⟨hzt, hz.2.2.trans_lt hdr⟩, max_eq_left hz.2.2]
      exact ⟨(z.1, d), ⟨mem_univ _, hd.le, le_rfl⟩, rfl⟩
    · change f x ∈ K
      simpa only [f, ite_eq_right hxH] using hx


private theorem exists_finite_retraction
    {ι M : Type*} [TopologicalSpace M] (s : Finset ι)
    (V : Set M) (U K : ι → Set M) (f : ι → M → M)
    (hUK : ∀ i ∈ s, U i ⊆ K i)
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (V ∩ K i) (V ∩ K j))
    (hc : ∀ i ∈ s, ContinuousOn (f i) V)
    (hm : ∀ i ∈ s, MapsTo (f i) V (V \ U i))
    (hfix : ∀ i ∈ s, EqOn (f i) id (U i)ᶜ)
    (hK : ∀ i ∈ s, MapsTo (f i) (K i) (K i)) :
    ∃ F : M → M, ContinuousOn F V ∧
      MapsTo F V (V \ ⋃ i ∈ s, U i) ∧
      EqOn F id (⋃ i ∈ s, U i)ᶜ ∧ F '' V = V \ ⋃ i ∈ s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨id, continuousOn_id, ?_, ?_, ?_⟩
      · simpa using (mapsTo_id V)
      · simp
      · simp
  | @insert i s his ih =>
      have hsub : (s : Set ι) ⊆ (↑(insert i s) : Set ι) := by
        intro j hj
        exact Finset.mem_insert_of_mem hj
      obtain ⟨F, hFc, hFm, hFfix, hFimage⟩ := ih
        (fun j hj => hUK j (hsub hj))
        (hdis.mono hsub)
        (fun j hj => hc j (hsub hj))
        (fun j hj => hm j (hsub hj))
        (fun j hj => hfix j (hsub hj))
        (fun j hj => hK j (hsub hj))
      have hi : i ∈ insert i s := Finset.mem_insert_self i s
      have hFmV : MapsTo F V V := fun x hx => (hFm hx).1
      have hcomp : ContinuousOn (f i ∘ F) V := (hc i hi).comp hFc hFmV
      have hmcomp : MapsTo (f i ∘ F) V (V \ ⋃ j ∈ insert i s, U j) := by
        intro x hx
        obtain ⟨hxV, hxU⟩ := hFm hx
        obtain ⟨hyV, hyUi⟩ := hm i hi hxV
        refine ⟨hyV, ?_⟩
        simp only [mem_iUnion, Finset.mem_insert, exists_prop, not_exists, not_and]
        intro j hj hyj
        rcases hj with rfl | hj
        · exact hyUi hyj
        · by_cases hxKi : F x ∈ K i
          · exact Set.disjoint_left.1 (hdis hi (hsub hj) (by
              intro he
              exact his (he ▸ hj))) ⟨hyV, hK i hi hxKi⟩ ⟨hyV, hUK j (hsub hj) hyj⟩
          · have hfeq : f i (F x) = F x := hfix i hi (fun h => hxKi (hUK i hi h))
            exact hxU (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, hfeq ▸ hyj⟩⟩)
      have hfixcomp : EqOn (f i ∘ F) id (⋃ j ∈ insert i s, U j)ᶜ := by
        intro x hx
        have hxs : x ∉ ⋃ j ∈ s, U j := by
          intro h
          obtain ⟨j, hxj⟩ := mem_iUnion.1 h
          obtain ⟨hj, hxj⟩ := mem_iUnion.1 hxj
          exact hx (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hsub hj, hxj⟩⟩)
        have hxi : x ∉ U i := by
          intro h
          exact hx (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, h⟩⟩)
        change f i (F x) = x
        rw [hFfix hxs]
        exact hfix i hi hxi
      refine ⟨f i ∘ F, hcomp, hmcomp, hfixcomp, ?_⟩
      apply subset_antisymm hmcomp.image_subset
      intro x hx
      exact ⟨x, hx.1, hfixcomp hx.2⟩

variable {ι N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
  [CompactSpace N] [T2Space M]

theorem exists_finite_half_collar_retraction
    (s : Finset ι) (T : ι → OpenPartialHomeomorph (N × ℝ) M) (r d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) (hdr : ∀ i ∈ s, d i < r i)
    (hsource : ∀ i ∈ s, (univ : Set N) ×ˢ Icc 0 (r i) ⊆ (T i).source)
    {V : Set M} (hzero : ∀ i ∈ s, Disjoint (range fun q : N => T i (q, 0)) V)
    (hpos : ∀ i ∈ s, T i '' ((univ : Set N) ×ˢ Ioo 0 (r i)) ⊆ V)
    (hdis : (s : Set ι).Pairwise fun i j =>
      Disjoint (V ∩ T i '' ((univ : Set N) ×ˢ Icc 0 (d i)))
        (V ∩ T j '' ((univ : Set N) ×ˢ Icc 0 (d j)))) :
    ∃ f : M → M, ContinuousOn f V ∧
      MapsTo f V (V \ ⋃ i ∈ s, T i '' ((univ : Set N) ×ˢ Ioo 0 (d i))) ∧
      EqOn f id (⋃ i ∈ s, T i '' ((univ : Set N) ×ˢ Ioo 0 (d i)))ᶜ ∧
      f '' V = V \ ⋃ i ∈ s, T i '' ((univ : Set N) ×ˢ Ioo 0 (d i)) := by
  classical
  have hpush := fun i hi => (T i).exists_half_collar_retraction
    (hd i hi) (hdr i hi) (hsource i hi) (hzero i hi) (hpos i hi)
  choose f hc hm hf hfix him hK using hpush
  let F : ι → M → M := fun i => if hi : i ∈ s then f i hi else id
  apply exists_finite_retraction s V
    (fun i => T i '' ((univ : Set N) ×ˢ Ioo 0 (d i)))
    (fun i => T i '' ((univ : Set N) ×ˢ Icc 0 (d i))) F
  · intro i hi
    exact image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  · exact hdis
  · intro i hi
    simpa only [F, dite_eq_left hi] using hc i hi
  · intro i hi
    simpa only [F, dite_eq_left hi] using hm i hi
  · intro i hi
    simpa only [F, dite_eq_left hi] using hfix i hi
  · intro i hi
    simpa only [F, dite_eq_left hi] using hK i hi

end OpenPartialHomeomorph
