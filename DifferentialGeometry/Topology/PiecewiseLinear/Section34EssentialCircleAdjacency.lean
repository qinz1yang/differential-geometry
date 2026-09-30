import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCirclePair
import Mathlib.Order.Preorder.Finite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem disk_caps_strictly_ordered_of_disjoint_boundaries {X : Type*} [TopologicalSpace X]
    {S D₀ D₁ R₀ R₁ J L : Set X}
    (hDU : D₀ ∪ D₁ = S) (hDI : D₀ ∩ D₁ = J)
    (hRU : R₀ ∪ R₁ = S) (hRI : R₀ ∩ R₁ = L)
    (hD₀ : IsPreconnected D₀) (hD₁ : IsPreconnected D₁)
    (hD₀c : IsClosed D₀) (hD₁c : IsClosed D₁)
    (hR₀c : IsClosed R₀) (hR₁c : IsClosed R₁)
    (hJne : J.Nonempty) (hL : IsConnected L) (hJL : Disjoint J L)
    (hanchor₀ : (D₀ ∩ R₀ ∩ Lᶜ).Nonempty)
    (hanchor₁ : (D₁ ∩ R₁ ∩ Lᶜ).Nonempty) :
    (L ⊆ D₀ ∧ R₀ ⊂ D₀ ∧ Disjoint D₁ R₀) ∨
      (L ⊆ D₁ ∧ D₀ ⊂ R₀ ∧ Disjoint D₀ R₁) := by
  have hdis {D D' R R' : Set X} (hDcover : D ∪ D' = S) (hDmeet : D ∩ D' = J)
      (hRcover : R ∪ R' = S) (hRmeet : R ∩ R' = L)
      (hDc : IsPreconnected D) (hRc : IsClosed R) (hR'c : IsClosed R')
      (hLD' : L ⊆ D') (ha : (D ∩ R ∩ Lᶜ).Nonempty) : Disjoint D R' := by
    have hDL : Disjoint D L := disjoint_left.mpr fun x hxD hxL =>
      disjoint_left.mp hJL (hDmeet ▸ ⟨hxD, hLD' hxL⟩) hxL
    have hDS : D ⊆ S := hDcover ▸ subset_union_left
    have hDR : D ⊆ R := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hDc R R' hRc hR'c
          (hRcover ▸ hDS) (hRmeet ▸ hDL.inter_eq) with h | h
      · exact h
      · obtain ⟨x, ⟨hxD, hxR⟩, hxL⟩ := ha
        exact (hxL (hRmeet ▸ ⟨hxR, h hxD⟩)).elim
    exact disjoint_left.mpr fun x hxD hxR' =>
      disjoint_left.mp hDL hxD (hRmeet ▸ ⟨hDR hxD, hxR'⟩)
  have hLS : L ⊆ S := (hRI ▸ inter_subset_left).trans (hRU ▸ subset_union_left)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hL.isPreconnected D₀ D₁
      hD₀c hD₁c (hDU ▸ hLS) (hDI ▸ hJL.symm.inter_eq) with hLD₀ | hLD₁
  · have hd : Disjoint D₁ R₀ := hdis (by rwa [union_comm]) (by rwa [inter_comm])
      (by rwa [union_comm]) (by rwa [inter_comm]) hD₁ hR₁c hR₀c hLD₀ hanchor₁
    have hR₀D₀ : R₀ ⊆ D₀ := by
      intro x hx
      have hxS : x ∈ S := hRU ▸ Or.inl hx
      exact (hDU.symm ▸ hxS).resolve_right (fun hy => disjoint_left.mp hd hy hx)
    refine Or.inl ⟨hLD₀, ⟨hR₀D₀, ?_⟩, hd⟩
    intro hD₀R₀
    obtain ⟨x, hx⟩ := hJne
    have hxD : x ∈ D₀ ∩ D₁ := hDI.symm ▸ hx
    exact disjoint_left.mp hd hxD.2 (hD₀R₀ hxD.1)
  · have hd : Disjoint D₀ R₁ := hdis hDU hDI hRU hRI hD₀ hR₀c hR₁c hLD₁ hanchor₀
    have hD₀R₀ : D₀ ⊆ R₀ := by
      intro x hx
      have hxS : x ∈ S := hDU ▸ Or.inl hx
      exact (hRU.symm ▸ hxS).resolve_right (fun hy => disjoint_left.mp hd hx hy)
    refine Or.inr ⟨hLD₁, ⟨hD₀R₀, ?_⟩, hd⟩
    intro hR₀D₀
    obtain ⟨x, hx⟩ := hL.nonempty
    have hxR : x ∈ R₀ ∩ R₁ := hRI.symm ▸ hx
    exact disjoint_left.mp hd (hR₀D₀ hxR.1) hxR.2

private theorem exists_adjacent_disk_caps {ι X : Type*} [Finite ι]
    (C D₀ D₁ : ι → Set X) (hne : ∃ i j : ι, i ≠ j)
    (horder : ∀ i j : ι, i ≠ j →
      (C j ⊆ D₀ i ∧ D₀ j ⊂ D₀ i ∧ Disjoint (D₁ i) (D₀ j)) ∨
        (C j ⊆ D₁ i ∧ D₀ i ⊂ D₀ j ∧ Disjoint (D₀ i) (D₁ j))) :
    ∃ i j : ι, i ≠ j ∧ Disjoint (D₀ i) (D₁ j) ∧
      ∀ k : ι, k ≠ i → k ≠ j → C k ⊆ D₀ i ∨ C k ⊆ D₁ j := by
  have hex : ∃ i j : ι, D₀ i ⊂ D₀ j := by
    obtain ⟨i, j, hij⟩ := hne
    rcases horder i j hij with h | h
    · exact ⟨j, i, h.2.1⟩
    · exact ⟨i, j, h.2.1⟩
  obtain ⟨i, j₀, hij₀⟩ := hex
  obtain ⟨j, hj, hmin⟩ := Set.Finite.exists_minimalFor D₀ {k | D₀ i ⊂ D₀ k}
    (Set.toFinite _) ⟨j₀, hij₀⟩
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl (D₀ i)) hj
  have hdis : Disjoint (D₀ i) (D₁ j) := by
    rcases horder i j hij with h | h
    · exact (h.2.1.2 hj.1).elim
    · exact h.2.2
  refine ⟨i, j, hij, hdis, ?_⟩
  intro k hki hkj
  rcases horder i k hki.symm with hlow | hhigh
  · exact Or.inl hlow.1
  rcases horder j k hkj.symm with hlow | hhigh'
  · exact (hlow.2.1.2 (hmin hhigh.2.1 hlow.2.1.1)).elim
  · exact Or.inr hhigh'.1

theorem IsPLSphere.exists_empty_annular_band_of_essential_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (C : Set (Set E)) (hC : C.Finite) (hcard : 1 < C.ncard)
    (hCsph : ∀ J ∈ C, IsPLSphere 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J) :
    ∃ J ∈ C, ∃ L ∈ C, J ≠ L ∧ ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      Disjoint (φ '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (⋃₀ C) := by
  classical
  let _ : Finite C := hC.to_subtype
  choose D₀ D₁ r₀ r₁ hDU hDI hr₀ hr₁ hb₀ hb₁ hA₀D hA₁D using
    fun i : C => (hS.exists_disk_in_annulus_or_separating_ends hA hAS
      (hCsph i.val i.property) (hCA i.val i.property)
      (hCend i.val i.property)).resolve_left (hCess i.val i.property)
  have hAne : A₀.Nonempty ∧ A₁.Nonempty := by
    obtain ⟨ψ, rfl, rfl⟩ := hA
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    constructor
    · exact ⟨ψ (⟨x, hx⟩, ⟨0, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩
    · exact ⟨ψ (⟨x, hx⟩, ⟨1, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩
  have horder : ∀ i j : C, i ≠ j →
      (j.val ⊆ D₀ i ∧ D₀ j ⊂ D₀ i ∧ Disjoint (D₁ i) (D₀ j)) ∨
        (j.val ⊆ D₁ i ∧ D₀ i ⊂ D₀ j ∧ Disjoint (D₀ i) (D₁ j)) := by
    intro i j hij
    apply disk_caps_strictly_ordered_of_disjoint_boundaries (hDU i) (hDI i) (hDU j) (hDI j)
      (IsPLBall.isConnected ⟨r₀ i, hr₀ i⟩).isPreconnected
      (IsPLBall.isConnected ⟨r₁ i, hr₁ i⟩).isPreconnected
      (IsPLBall.isPolyhedron ⟨r₀ i, hr₀ i⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁ i, hr₁ i⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₀ j, hr₀ j⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁ j, hr₁ j⟩).isClosed
      (hCsph i.val i.property).nonempty (hCsph j.val j.property).isConnected
      (hCdisj i.property j.property (fun h => hij (Subtype.ext h)))
    · obtain ⟨x, hx⟩ := hAne.1
      exact ⟨x, ⟨hA₀D i hx, hA₀D j hx⟩,
        fun hxJ => disjoint_left.mp (hCend j.val j.property) hxJ (Or.inl hx)⟩
    · obtain ⟨x, hx⟩ := hAne.2
      exact ⟨x, ⟨hA₁D i hx, hA₁D j hx⟩,
        fun hxJ => disjoint_left.mp (hCend j.val j.property) hxJ (Or.inr hx)⟩
  have hne : ∃ i j : C, i ≠ j := by
    obtain ⟨J, hJ, L, hL, hJL⟩ := (Set.one_lt_ncard hC).mp hcard
    exact ⟨⟨J, hJ⟩, ⟨L, hL⟩, fun h => hJL (congrArg Subtype.val h)⟩
  obtain ⟨i, j, hij, hdis, houter⟩ :=
    exists_adjacent_disk_caps (fun i : C => i.val) D₀ D₁ hne horder
  obtain ⟨φ, hφ, hφS, hφ₀, hφ₁, hB₀, hB₁⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_of_disjoint_disks hS (hr₀ i) (hr₁ j)
      (hb₀ i) (hb₁ j) (hDU i ▸ subset_union_left) (hDU j ▸ subset_union_right) hdis
  have hφA : φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A := by
    have hconn := ((isConnected_stdSimplexBoundary 0).prod
      (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))).image φ
        hφ.isPiecewiseAffineOn.continuousOn
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAS hφS
      hconn.isPreconnected
    · obtain ⟨x, hx⟩ := (hCsph i.val i.property).nonempty
      refine ⟨x, ?_, hCA i.val i.property hx⟩
      rw [← hφ₀] at hx
      exact image_mono (prod_mono_right (by simp)) hx
    · refine disjoint_left.mpr fun x hxB hxend => ?_
      rcases hxend with hx₀ | hx₁
      · exact disjoint_left.mp (hCend i.val i.property)
          (hB₀ ▸ ⟨hxB, hA₀D i hx₀⟩) (Or.inl hx₀)
      · exact disjoint_left.mp (hCend j.val j.property)
          (hB₁ ▸ ⟨hxB, hA₁D j hx₁⟩) (Or.inr hx₁)
  have hopen : Disjoint (φ '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1))
      (i.val ∪ j.val) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ (hz | hz)
    · rw [← hφ₀] at hz
      obtain ⟨y, hy, heq⟩ := hz
      have hyA : y ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
        ⟨hy.1, by rw [show y.2 = 0 from hy.2]; exact ⟨le_rfl, zero_le_one⟩⟩
      have hxy := hφ.bijOn.injOn hyA ⟨hx.1, Ioo_subset_Icc_self hx.2⟩ heq
      have hxt : x.2 = 0 := (congrArg Prod.snd hxy).symm.trans hy.2
      exact (lt_irrefl (0 : ℝ)) (hxt ▸ hx.2.1)
    · rw [← hφ₁] at hz
      obtain ⟨y, hy, heq⟩ := hz
      have hyA : y ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
        ⟨hy.1, by rw [show y.2 = 1 from hy.2]; exact ⟨zero_le_one, le_rfl⟩⟩
      have hxy := hφ.bijOn.injOn hyA ⟨hx.1, Ioo_subset_Icc_self hx.2⟩ heq
      have hxt : x.2 = 1 := (congrArg Prod.snd hxy).symm.trans hy.2
      exact (lt_irrefl (1 : ℝ)) (hxt ▸ hx.2.2)
  refine ⟨i.val, i.property, j.val, j.property, fun h => hij (Subtype.ext h),
    φ, hφ, hφA, hφ₀, hφ₁, disjoint_left.mpr ?_⟩
  rintro x hxopen ⟨K, hK, hxK⟩
  let k : C := ⟨K, hK⟩
  have hxk : x ∈ k.val := hxK
  by_cases hki : k = i
  · exact disjoint_left.mp hopen hxopen (Or.inl (hki ▸ hxk))
  by_cases hkj : k = j
  · exact disjoint_left.mp hopen hxopen (Or.inr (hkj ▸ hxk))
  have hxB : x ∈ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    image_mono (prod_mono_right Ioo_subset_Icc_self) hxopen
  rcases houter k hki hkj with hlow | hhigh
  · exact disjoint_left.mp hopen hxopen (Or.inl (hB₀ ▸ ⟨hxB, hlow hxk⟩))
  · exact disjoint_left.mp hopen hxopen (Or.inr (hB₁ ▸ ⟨hxB, hhigh hxk⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
