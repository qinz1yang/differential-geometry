import DifferentialGeometry.Topology.Compactness.ProductChartBand
import DifferentialGeometry.Topology.Compactness.FiniteSeparation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.Compactness

theorem exists_larger_interval_subset_of_isOpen
    {a b : ℝ} (hab : a ≤ b) {V : Set ℝ} (hV : IsOpen V) (hsub : Icc a b ⊆ V) :
    ∃ a' b', a' < a ∧ b < b' ∧ Ioo a' b' ⊆ V := by
  obtain ⟨a', c, ha, hac⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hV.mem_nhds (hsub ⟨le_rfl, hab⟩))
  obtain ⟨d, b', hb, hdb⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hV.mem_nhds (hsub ⟨hab, le_rfl⟩))
  refine ⟨a', b', ha.1, hb.2, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hac ⟨ht.1, hta.trans ha.2⟩
  · by_cases hbt : b < t
    · exact hdb ⟨hb.1.trans hbt, ht.2⟩
    · exact hsub ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

theorem exists_larger_product_chart_band
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a ≤ b)
    (hsource : (univ : Set N) ×ˢ Icc a b ⊆ e.source)
    {U : Set M} (hU : IsOpen U) (hband : e '' ((univ : Set N) ×ˢ Icc a b) ⊆ U) :
    ∃ a' b', a' < a ∧ b < b' ∧
      (univ : Set N) ×ˢ Ioo a' b' ⊆ e.source ∧
      e '' ((univ : Set N) ×ˢ Ioo a' b') ⊆ U := by
  have hopen : IsOpen (e.source ∩ e ⁻¹' U) := e.isOpen_inter_preimage hU
  have hsmall : (univ : Set N) ×ˢ Icc a b ⊆ e.source ∩ e ⁻¹' U :=
    fun p hp ↦ ⟨hsource hp, hband ⟨p, hp, rfl⟩⟩
  obtain ⟨A, V, _, hV, hA, hI, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_Icc hopen hsmall
  obtain ⟨a', b', ha, hb, hsub⟩ := exists_larger_interval_subset_of_isOpen hab hV hI
  have hlarge : (univ : Set N) ×ˢ Ioo a' b' ⊆ e.source ∩ e ⁻¹' U :=
    fun p hp ↦ hprod ⟨hA hp.1, hsub hp.2⟩
  exact ⟨a', b', ha, hb, fun p hp ↦ (hlarge hp).1,
    by rintro z ⟨p, hp, rfl⟩; exact (hlarge hp).2⟩

theorem simplyConnectedSpace_product_chart_band
    {N M : Type*} [TopologicalSpace N] [SimplyConnectedSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : (univ : Set N) ×ˢ Ioo a b ⊆ e.source) :
    SimplyConnectedSpace (e '' ((univ : Set N) ×ˢ Ioo a b)) := by
  let _ : ContractibleSpace (Ioo a b) :=
    (convex_Ioo a b).contractibleSpace (by obtain ⟨t, ht⟩ := exists_between hab; exact ⟨t, ht⟩)
  let E₁ : ↑(e '' ((univ : Set N) ×ˢ Ioo a b)) ≃ₜ N × Ioo a b :=
    (e.homeomorphOfImageSubsetSource hsource rfl).symm.trans
      ((Homeomorph.Set.prod univ (Ioo a b)).trans
        ((Homeomorph.Set.univ N).prodCongr (Homeomorph.refl _)))
  let E₂ : N × Ioo a b ≃ₕ N :=
    ((ContinuousMap.HomotopyEquiv.refl N).prodCongr
      (ContractibleSpace.hequiv_unit (Ioo a b)).some).trans
        (Homeomorph.prodUnique N Unit).toHomotopyEquiv
  exact (E₁.toHomotopyEquiv.trans E₂).simplyConnectedSpace

theorem exists_larger_product_chart_bands_preserving_disjointness
    {N M ι : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    [T2Space M] [Finite ι] (e : ι → OpenPartialHomeomorph (N × ℝ) M)
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, (univ : Set N) ×ˢ Icc (a i) (b i) ⊆ (e i).source)
    (R : ι → ι → Prop)
    (hd : ∀ i j, R i j → Disjoint
      (e i '' ((univ : Set N) ×ˢ Icc (a i) (b i)))
      (e j '' ((univ : Set N) ×ˢ Icc (a j) (b j)))) :
    ∃ a' b' : ι → ℝ, (∀ i, a' i < a i ∧ b i < b' i) ∧
      (∀ i, (univ : Set N) ×ˢ Ioo (a' i) (b' i) ⊆ (e i).source) ∧
      ∀ i j, R i j → Disjoint
        (e i '' ((univ : Set N) ×ˢ Ioo (a' i) (b' i)))
        (e j '' ((univ : Set N) ×ˢ Ioo (a' j) (b' j))) := by
  have hK (i : ι) : IsCompact (e i '' ((univ : Set N) ×ˢ Icc (a i) (b i))) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((e i).continuousOn.mono (hsource i))
  obtain ⟨U, hU, hKU, hUd⟩ := exists_open_supersets_preserving_disjointness _ hK R hd
  have hbig (i : ι) := exists_larger_product_chart_band (e i) (hab i) (hsource i) (hU i) (hKU i)
  choose a' b' ha hb hsrc himg using hbig
  exact ⟨a', b', fun i ↦ ⟨ha i, hb i⟩, hsrc,
    fun i j hij ↦ (hUd i j hij).mono (himg i) (himg j)⟩

end DifferentialGeometry.Topology.Compactness
