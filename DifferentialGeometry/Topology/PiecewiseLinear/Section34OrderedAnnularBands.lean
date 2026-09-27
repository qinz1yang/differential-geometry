import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_lateral_annulus_eq_inter_of_disk_caps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S D₀ D₁ F₀ F₁ J L : Set E} (hS : IsPLSphere 2 S)
    {r s : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D₀)
    (hs : IsPLHomeomorphOn s (stdSimplex ℝ (Fin 3)) F₁)
    (hrb : r '' stdSimplexBoundary 2 = J) (hsb : s '' stdSimplexBoundary 2 = L)
    (hDU : D₀ ∪ D₁ = S) (hDI : D₀ ∩ D₁ = J)
    (hFU : F₀ ∪ F₁ = S) (hFI : F₀ ∩ F₁ = L) (hdis : Disjoint D₀ F₁) :
    ∃ f : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (D₁ ∩ F₀) ∧
      f '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      f '' (stdSimplexBoundary 2 ×ˢ {1}) = L := by
  obtain ⟨f, hf, hfS, hf₀, hf₁, hBD, hBF, hcover⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks hS hr hs hrb hsb
      (hDU ▸ subset_union_left) (hFU ▸ subset_union_right) hdis
  have hJ : J ⊆ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hf₀]
    exact image_mono (prod_mono_right (by simp))
  have hL : L ⊆ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hf₁]
    exact image_mono (prod_mono_right (by simp))
  have himage : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ ∩ F₀ := by
    apply Subset.antisymm
    · intro x hx
      constructor
      · rcases hDU.symm ▸ hfS hx with hxD | hxD
        · exact (hDI.superset (hBD.subset ⟨hx, hxD⟩)).2
        · exact hxD
      · rcases hFU.symm ▸ hfS hx with hxF | hxF
        · exact hxF
        · exact (hFI.superset (hBF.subset ⟨hx, hxF⟩)).1
    · rintro x ⟨hxD, hxF⟩
      rcases hcover (hDU.subset (Or.inr hxD)) with (hx₀ | hx₁) | hx
      · exact hJ (hDI.subset ⟨hx₀, hxD⟩)
      · exact hL (hFI.subset ⟨hxF, hx₁⟩)
      · exact hx
  exact ⟨f, himage ▸ hf, hf₀, hf₁⟩

theorem subset_inter_of_ordered_caps_iff
    {X ι : Type*} [Preorder ι] {J D₀ D₁ : ι → Set X}
    (hleft : ∀ i j, J i ⊆ D₀ j ↔ i ≤ j)
    (hright : ∀ i j, J i ⊆ D₁ j ↔ j ≤ i) (i j k : ι) :
    J k ⊆ D₁ i ∩ D₀ j ↔ i ≤ k ∧ k ≤ j := by
  rw [subset_inter_iff, hright, hleft]

theorem disjoint_open_lateral_trace_of_adjacent_caps
    {X : Type*} {n : ℕ} {J D₀ D₁ : Fin n → Set X}
    (hDI : ∀ i, D₀ i ∩ D₁ i = J i)
    (hdis : ∀ i j, i < j → Disjoint (D₀ i) (D₁ j))
    {i j : Fin n} (hij : j.val = i.val + 1)
    {f : (Fin 3 → ℝ) × ℝ → X}
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hf : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J i)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = J j) :
    Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (⋃ k, J k) := by
  have hopen := image_lateral_open_eq_sdiff_ends hfi
  rw [hf₀, hf₁, hf] at hopen
  refine disjoint_left.mpr ?_
  rintro x hx ⟨K, ⟨k, rfl⟩, hxk⟩
  have hx' := hopen.subset hx
  by_cases hki : k = i
  · exact hx'.2 (Or.inl (hki ▸ hxk))
  by_cases hkj : k = j
  · exact hx'.2 (Or.inr (hkj ▸ hxk))
  have hki' : k < i ∨ j < k := by
    have hni : k.val ≠ i.val := fun h => hki (Fin.ext h)
    have hnj : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    change k.val < i.val ∨ j.val < k.val
    omega
  rcases hki' with hk | hk
  · exact disjoint_left.mp (hdis k i hk) ((hDI k).superset hxk).1 hx'.1.1
  · exact disjoint_left.mp (hdis j k hk) hx'.1.2 ((hDI k).superset hxk).2

theorem IsPLSphere.exists_ordered_lateral_bands_of_essential_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (C : Set (Set E)) (hC : C.Finite)
    (hCsph : ∀ J ∈ C, IsPLSphere 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J) :
    ∃ e : Fin C.ncard ≃ C, ∀ i j, i < j → ∃ f : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      f '' (stdSimplexBoundary 2 ×ˢ {0}) = (e i).val ∧
      f '' (stdSimplexBoundary 2 ×ˢ {1}) = (e j).val ∧
      (∀ k, (e k).val ⊆ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ↔
        i ≤ k ∧ k ≤ j) ∧
      (j.val = i.val + 1 →
        Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (⋃₀ C)) := by
  obtain ⟨e, D₀, D₁, r₀, r₁, hcap, -, -, hdis, hleft, hright⟩ :=
    hS.exists_ordered_disk_caps_of_essential_family hA hAS C hC hCsph hCA hCend hCdisj hCess
  refine ⟨e, ?_⟩
  intro i j hij
  obtain ⟨f, hf, hf₀, hf₁⟩ := hS.exists_lateral_annulus_eq_inter_of_disk_caps
    (hcap i).1 (hcap j).2.1 (hcap i).2.2.1 (hcap j).2.2.2.1
    (hcap i).2.2.2.2.1 (hcap i).2.2.2.2.2.1
    (hcap j).2.2.2.2.1 (hcap j).2.2.2.2.2.1 (hdis i j hij)
  have hsubS : D₁ i ∩ D₀ j ⊆ S :=
    inter_subset_left.trans ((hcap i).2.2.2.2.1 ▸ subset_union_right)
  have hsubA : D₁ i ∩ D₀ j ⊆ A := by
    have hconn := ((isConnected_stdSimplexBoundary 0).prod
      (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))).image f
        hf.isPiecewiseAffineOn.continuousOn
    rw [hf.image_eq] at hconn
    apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAS hsubS
      hconn.isPreconnected
    · obtain ⟨x, hx⟩ := (hCsph (e i).val (e i).property).nonempty
      refine ⟨x, ⟨((hcap i).2.2.2.2.2.1.superset hx).2,
        (hleft i j).mpr hij.le hx⟩, hCA (e i).val (e i).property hx⟩
    · refine disjoint_left.mpr fun x hx hxrim => ?_
      rcases hxrim with hx₀ | hx₁
      · exact disjoint_left.mp (hCend (e i).val (e i).property)
          ((hcap i).2.2.2.2.2.1.subset ⟨(hcap i).2.2.2.2.2.2.1 hx₀, hx.1⟩)
          (Or.inl hx₀)
      · exact disjoint_left.mp (hCend (e j).val (e j).property)
          ((hcap j).2.2.2.2.2.1.subset ⟨hx.2, (hcap j).2.2.2.2.2.2.2 hx₁⟩)
          (Or.inr hx₁)
  refine ⟨f, hf.image_eq.symm ▸ hf, hf.image_eq ▸ hsubA, hf₀, hf₁, ?_, ?_⟩
  · intro k
    rw [hf.image_eq]
    exact subset_inter_of_ordered_caps_iff hleft hright i j k
  · intro hadj
    have htrace : (⋃ k, (e k).val) = ⋃₀ C := by
      apply Subset.antisymm
      · exact iUnion_subset fun k => subset_sUnion_of_mem (e k).property
      · rintro x ⟨J, hJ, hxJ⟩
        obtain ⟨k, hk⟩ := e.surjective ⟨J, hJ⟩
        exact mem_iUnion.mpr ⟨k, (congrArg Subtype.val hk).symm ▸ hxJ⟩
    rw [← htrace]
    exact disjoint_open_lateral_trace_of_adjacent_caps
      (fun k => (hcap k).2.2.2.2.2.1) hdis hadj hf.bijOn.injOn hf.image_eq hf₀ hf₁

end DifferentialGeometry.Topology.PiecewiseLinear
