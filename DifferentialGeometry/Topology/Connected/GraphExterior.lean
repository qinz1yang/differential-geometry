import DifferentialGeometry.Topology.Connected.FrontierCover
import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation

noncomputable section

open Set

namespace DifferentialGeometry.Topology

theorem eq_compl_iUnion_of_frontier_graphs
    {ι Y : Type*} [Finite ι] [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, PreconnectedSpace (X i)]
    (A : ∀ i, OpenPartialHomeomorph (X i × ℝ) Y) (f : ∀ i, X i → ℝ)
    (hf : ∀ i, Continuous (f i)) (U : ι → Set Y) (hU : ∀ i, IsOpen (U i))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hsource : ∀ i p, |p.2 - f i p.1| < a i → p ∈ (A i).source)
    (hside : ∀ i p, |p.2 - f i p.1| < a i → (A i p ∈ U i ↔ p.2 < f i p.1))
    (hfrontU : ∀ i, frontier (U i) = range (fun x => A i (x, f i x)))
    (hdis : Pairwise fun i j => Disjoint
      (range (fun x => A i (x, f i x))) (range (fun x => A j (x, f j x))))
    {W : Set Y} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfrontW : frontier W = ⋃ i, range (fun x => A i (x, f i x)))
    (x₀ : Y) (hx₀ : x₀ ∈ interior W) (hthick : ∀ i, x₀ ∉ closure (U i)) :
    W = (⋃ i, U i)ᶜ := by
  classical
  let G (i : ι) : Set Y := range (fun x => A i (x, f i x))
  have hW : IsClosed W := hregular ▸ isClosed_closure
  have hGclosed (i : ι) : IsClosed (G i) := by
    apply IsCompact.isClosed
    apply isCompact_range
    exact (A i).continuousOn.comp_continuous (continuous_id.prodMk (hf i))
      (fun x => hsource i (x, f i x) (by simpa using ha i))
  have hGinW (i : ι) : G i ⊆ W := fun y hy =>
    hW.frontier_subset (hfrontW.symm ▸ mem_iUnion.mpr ⟨i, hy⟩)
  have hout (i : ι) : W ⊆ (U i)ᶜ := by
    apply subset_of_frontier_subset_of_closure_interior_eq (hU i).isClosed_compl
      hregular hconn
    · rw [frontier_compl, hfrontU, hfrontW]
      exact subset_iUnion (fun i => range (fun x => A i (x, f i x))) i
    · refine ⟨x₀, hx₀, ?_⟩
      rw [interior_compl]
      exact hthick i
  let V := W ∪ ⋃ i, U i
  have hVclosed : IsClosed V := by
    have heq : V = W ∪ ⋃ i, closure (U i) := by
      apply Subset.antisymm
      · exact union_subset_union_right W (iUnion_mono fun i => subset_closure)
      · rintro y (hyW | hyU)
        · exact Or.inl hyW
        · obtain ⟨i, hy⟩ := mem_iUnion.mp hyU
          rw [closure_eq_self_union_frontier, hfrontU] at hy
          exact hy.elim (fun h => Or.inr (mem_iUnion.mpr ⟨i, h⟩))
            (fun h => Or.inl (hGinW i h))
    rw [heq]
    exact hW.union (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rcases hy with hyW | hyU
    · by_cases hyint : y ∈ interior W
      · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hyint)
          (interior_subset.trans subset_union_left)
      · have hyfront : y ∈ frontier W := ⟨subset_closure hyW, hyint⟩
        rw [hfrontW] at hyfront
        obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hyfront
        let S := ⋃ j : {j : ι // j ≠ i}, G j.val
        have hS : IsClosed S := isClosed_iUnion_of_finite fun j => hGclosed j.val
        have heq : frontier W = G i ∪ S := by
          rw [hfrontW]
          ext z
          constructor
          · intro hz
            obtain ⟨j, hz⟩ := mem_iUnion.mp hz
            by_cases hji : j = i
            · subst j
              exact Or.inl hz
            · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hz⟩)
          · rintro (hz | hz)
            · exact mem_iUnion.mpr ⟨i, hz⟩
            · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
              exact mem_iUnion.mpr ⟨j.val, hj⟩
        have hd : Disjoint (G i) S := by
          apply Set.disjoint_left.mpr
          intro z hz hzS
          obtain ⟨j, hj⟩ := mem_iUnion.mp hzS
          exact Set.disjoint_left.mp (hdis (Ne.symm j.property)) hz hj
        obtain ⟨b, hb, hor⟩ := exists_graph_collar_orientation_of_frontier_eq_union
          (A i) (hf i) (fun x => hsource i (x, f i x) (by simpa using ha i))
          hregular hS heq hd
        let c := min (a i) b
        have hc : 0 < c := lt_min (ha i) hb
        have hright : ∀ x : X i, ∀ t ∈ Ioo (0 : ℝ) c,
            A i (x, f i x + t) ∈ interior W := by
          rcases hor with hl | hr
          · have hsmall : c / 2 ∈ Ioo (0 : ℝ) b :=
              ⟨half_pos hc, (half_lt_self hc).trans_le (min_le_right _ _)⟩
            have hm : |(f i q - c / 2) - f i q| < a i := by
              rw [sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hc)]
              exact (half_lt_self hc).trans_le (min_le_left _ _)
            have hin := (hside i (q, f i q - c / 2) hm).mpr (sub_lt_self _ (half_pos hc))
            exact False.elim (hout i (interior_subset (hl q (c / 2) hsmall).2) hin)
          · intro x t ht
            exact (hr x t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩).2
        let B : Set (X i × ℝ) := {p | |p.2 - f i p.1| < c}
        have hB : IsOpen B :=
          isOpen_lt (continuous_snd.sub ((hf i).comp continuous_fst)).abs continuous_const
        have hBs : B ⊆ (A i).source := fun p hp =>
          hsource i p (hp.trans_le (min_le_left _ _))
        have himage : A i '' B ⊆ V := by
          rintro z ⟨⟨x, t⟩, ht, rfl⟩
          rcases lt_trichotomy t (f i x) with hlt | he | hgt
          · right
            exact mem_iUnion.mpr ⟨i,
              (hside i (x, t) (ht.trans_le (min_le_left _ _))).mpr hlt⟩
          · left
            exact hGinW i ⟨x, by rw [he]⟩
          · left
            have hh : t - f i x ∈ Ioo (0 : ℝ) c :=
              ⟨sub_pos.mpr hgt, (le_abs_self _).trans_lt ht⟩
            have hw := hright x (t - f i x) hh
            rw [add_sub_cancel] at hw
            exact interior_subset hw
        apply Filter.mem_of_superset
          (((A i).isOpen_image_of_subset_source hB hBs).mem_nhds
            (show A i (q, f i q) ∈ A i '' B from ⟨(q, f i q), by simpa [B] using hc, rfl⟩))
          himage
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hyU
      exact Filter.mem_of_superset ((hU i).mem_nhds hi)
        (fun z hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩))
  have huniv : V = univ := (IsClopen.eq_univ ⟨hVclosed, hVopen⟩
    ⟨x₀, Or.inl (interior_subset hx₀)⟩)
  apply Subset.antisymm
  · intro y hy hnot
    obtain ⟨i, hi⟩ := mem_iUnion.mp hnot
    exact hout i hy hi
  · intro y hy
    exact (huniv.symm.subset (mem_univ y) : y ∈ W ∪ ⋃ i, U i).resolve_right hy

theorem eq_of_frontier_graphs
    {X L Y : Type*} [TopologicalSpace X] [LinearOrder L] [TopologicalSpace L]
    [TopologicalSpace Y]
    (A : OpenPartialHomeomorph (X × L) Y) (f g : X → L)
    {U V W : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hfsource : ∀ x, (x, f x) ∈ A.source) (hgsource : ∀ x, (x, g x) ∈ A.source)
    (hsideU : ∀ p ∈ A.source, A p ∈ U ↔ p.2 < f p.1)
    (hsideV : ∀ p ∈ A.source, A p ∈ V ↔ p.2 < g p.1)
    (hfrontU : frontier U = range (fun x => A (x, f x)))
    (hfrontV : frontier V = range (fun x => A (x, g x)))
    (hregular : closure (interior W) = W) (hconn : IsPreconnected (interior W))
    (hUW : frontier U ⊆ frontier W) (hVW : frontier V ⊆ frontier W)
    (x₀ : Y) (hx₀ : x₀ ∈ interior W) (hxU : x₀ ∉ closure U) (hxV : x₀ ∉ closure V) :
    f = g := by
  have hW : IsClosed W := hregular ▸ isClosed_closure
  have houtU : W ⊆ Uᶜ := by
    apply subset_of_frontier_subset_of_closure_interior_eq hU.isClosed_compl hregular hconn
    · rwa [frontier_compl]
    · exact ⟨x₀, hx₀, by rwa [interior_compl]⟩
  have houtV : W ⊆ Vᶜ := by
    apply subset_of_frontier_subset_of_closure_interior_eq hV.isClosed_compl hregular hconn
    · rwa [frontier_compl]
    · exact ⟨x₀, hx₀, by rwa [interior_compl]⟩
  funext x
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    have hgW : A (x, g x) ∈ W :=
      hW.frontier_subset (hVW (hfrontV.symm ▸ mem_range_self x))
    exact houtU hgW ((hsideU (x, g x) (hgsource x)).mpr h)
  · apply le_of_not_gt
    intro h
    have hfW : A (x, f x) ∈ W :=
      hW.frontier_subset (hUW (hfrontU.symm ▸ mem_range_self x))
    exact houtV hfW ((hsideV (x, f x) (hfsource x)).mpr h)

theorem injective_of_frontier_graphs
    {ι κ L Y : Type*} [LinearOrder L] [TopologicalSpace L] [TopologicalSpace Y]
    {X : κ → Type*} [∀ k, TopologicalSpace (X k)]
    (A : ∀ k, OpenPartialHomeomorph (X k × L) Y)
    (label : ι → κ) (f : ∀ i, X (label i) → L) (U : ι → Set Y)
    (hU : ∀ i, IsOpen (U i))
    (hsource : ∀ i x, (x, f i x) ∈ (A (label i)).source)
    (hside : ∀ i p, p ∈ (A (label i)).source →
      (A (label i) p ∈ U i ↔ p.2 < f i p.1))
    (hfront : ∀ i, frontier (U i) = range (fun x => A (label i) (x, f i x)))
    (hdis : Pairwise fun i j => Disjoint (frontier (U i)) (frontier (U j)))
    {W : Set Y} (hregular : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hUW : ∀ i, frontier (U i) ⊆ frontier W)
    (x₀ : Y) (hx₀ : x₀ ∈ interior W) (hthick : ∀ i, x₀ ∉ closure (U i)) :
    Function.Injective label := by
  intro i j hij
  by_contra hneij
  have hj : ∃ g : X (label j) → L,
      (∀ x, (x, g x) ∈ (A (label j)).source) ∧
      (∀ p ∈ (A (label j)).source, A (label j) p ∈ U j ↔ p.2 < g p.1) ∧
      frontier (U j) = range (fun x => A (label j) (x, g x)) :=
    ⟨f j, hsource j, hside j, hfront j⟩
  rw [← hij] at hj
  obtain ⟨g, hsourcej, hsidej, hfrontj⟩ := hj
  have he := eq_of_frontier_graphs (A (label i)) (f i) g (hU i) (hU j)
    (hsource i) hsourcej (hside i) hsidej (hfront i) hfrontj hregular hconn
    (hUW i) (hUW j) x₀ hx₀ (hthick i) (hthick j)
  have hfij : frontier (U i) = frontier (U j) := by rw [hfront i, hfrontj, he]
  let x := ((A (label i)).symm x₀).1
  have hy : A (label i) (x, f i x) ∈ frontier (U i) :=
    (hfront i).symm ▸ mem_range_self x
  exact disjoint_left.mp (hdis hneij) hy (hfij ▸ hy)

end DifferentialGeometry.Topology
