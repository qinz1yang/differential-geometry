import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter
open scoped Topology

private theorem IsCompact.exists_prod_Icc_inter_subset_of_local_cylinder
    {X : Type*} [TopologicalSpace X] {K B C : Set X} (hK : IsCompact K)
    {S N : Set (X × ℝ)} (hS : IsClosed S) (hN : IsOpen N) {a : ℝ}
    (hzero : S ∩ (K ×ˢ {a}) ⊆ B ×ˢ univ)
    (hBN : B ×ˢ {a} ⊆ N) (hcylinder : N ∩ S ⊆ C ×ˢ univ) :
    ∃ ε > 0, (K ×ˢ Icc (a - ε) (a + ε)) ∩ S ⊆ C ×ˢ univ := by
  have hcover : K ×ˢ {a} ⊆ N ∪ Sᶜ := by
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl (hBN ⟨(hzero ⟨hs, hp⟩).1, hp.2⟩)
    · exact Or.inr hs
  obtain ⟨U, V, _, hV, hKU, haV, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton (hN.union hS.isOpen_compl) hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a (haV (mem_singleton a))
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro ⟨x, t⟩ ⟨⟨hx, ht⟩, hs⟩
  have htV : t ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound : |t - a| ≤ r / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hbound.trans_lt (half_lt_self hr))
  rcases hUV ⟨hKU hx, htV⟩ with hn | hn
  · exact hcylinder ⟨hn, hs⟩
  · exact False.elim (hn hs)

theorem IsCompact.exists_disjoint_interior_prod_Icc_of_boundary_collar
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {S N : Set (X × ℝ)} (hS : IsClosed S) (hN : IsOpen N) {a : ℝ}
    (hzero : Disjoint S (interior K ×ˢ {a}))
    (hBN : frontier K ×ˢ {a} ⊆ N)
    (hcollar : N ∩ S ⊆ (interior K)ᶜ ×ˢ univ) :
    ∃ ε > 0, Disjoint S (interior K ×ˢ Icc (a - ε) (a + ε)) := by
  have hcontact : S ∩ (K ×ˢ {a}) ⊆ frontier K ×ˢ univ := by
    rintro ⟨x, t⟩ ⟨hs, hx, ht⟩
    refine ⟨⟨subset_closure hx, ?_⟩, mem_univ _⟩
    exact fun hi => Set.disjoint_left.mp hzero hs ⟨hi, ht⟩
  obtain ⟨ε, hε, hεS⟩ := hK.exists_prod_Icc_inter_subset_of_local_cylinder
    hS hN hcontact hBN hcollar
  refine ⟨ε, hε, Set.disjoint_left.mpr ?_⟩
  rintro ⟨x, t⟩ hs ⟨hx, ht⟩
  exact (hεS ⟨⟨interior_subset hx, ht⟩, hs⟩).1 hx

theorem Continuous.disjoint_range_prod_singleton_of_not_isLocalMax
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) {U : Set X} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b)
    (hupper : Disjoint (range e) (U ×ˢ Ioc a b))
    (hregular : ∀ x, (e x).1 ∈ U → (e x).2 = a →
      ¬ IsLocalMax (fun y => (e y).2) x) :
    Disjoint (range e) (U ×ˢ {a}) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, rfl⟩ ⟨hx, ht⟩
  have heq : (e x).2 = a := mem_singleton_iff.mp ht
  apply hregular x hx heq
  have hxn : ∀ᶠ y in 𝓝 x, (e y).1 ∈ U :=
    (he.fst.continuousAt).preimage_mem_nhds (hU.mem_nhds hx)
  have htn : ∀ᶠ y in 𝓝 x, (e y).2 < b :=
    (he.snd.continuousAt).preimage_mem_nhds (Iio_mem_nhds (heq ▸ hab))
  filter_upwards [hxn, htn] with y hy hyt
  rw [heq]
  by_contra hn
  exact Set.disjoint_left.mp hupper (mem_range_self y) ⟨hy, lt_of_not_ge hn, hyt.le⟩

theorem Continuous.exists_disjoint_interior_prod_Icc_of_boundary_collar
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) (hclosed : IsClosed (range e))
    {K : Set X} (hK : IsCompact K) {a b : ℝ} (hab : a < b)
    (hupper : Disjoint (range e) (interior K ×ˢ Ioc a b))
    (hregular : ∀ x, (e x).1 ∈ interior K → (e x).2 = a →
      ¬ IsLocalMax (fun y => (e y).2) x)
    {N : Set (X × ℝ)} (hN : IsOpen N)
    (hBN : frontier K ×ˢ {a} ⊆ N)
    (hcollar : N ∩ range e ⊆ (interior K)ᶜ ×ˢ univ) :
    ∃ ε > 0, Disjoint (range e) (interior K ×ˢ Icc (a - ε) (a + ε)) :=
  hK.exists_disjoint_interior_prod_Icc_of_boundary_collar hclosed hN
    (he.disjoint_range_prod_singleton_of_not_isLocalMax isOpen_interior hab hupper hregular)
    hBN hcollar

theorem Continuous.disjoint_range_interior_prod_Icc_of_boundary_collar
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {e : M → X × ℝ} (he : Continuous e) (hclosed : IsClosed (range e))
    {K : Set X} (hK : IsCompact K) {a b : ℝ}
    (hupper : Disjoint (range e) (interior K ×ˢ {b}))
    (hregular : ∀ x, (e x).1 ∈ interior K → (e x).2 ∈ Ico a b →
      ¬ IsLocalMax (fun y => (e y).2) x)
    {N : Set (X × ℝ)} (hN : IsOpen N)
    (hBN : frontier K ×ˢ Icc a b ⊆ N)
    (hcollar : N ∩ range e ⊆ (interior K)ᶜ ×ˢ univ) :
    Disjoint (range e) (interior K ×ˢ Icc a b) := by
  let C := (K ×ˢ Icc a b) ∩ range e ∩ Nᶜ
  have hC : IsCompact C :=
    ((hK.prod isCompact_Icc).inter_right hclosed).inter_right hN.isClosed_compl
  apply Set.disjoint_left.mpr
  intro p hp hpt
  have hpC : p ∈ C := ⟨⟨⟨interior_subset hpt.1, hpt.2⟩, hp⟩,
    fun hn => (hcollar ⟨hn, hp⟩).1 hpt.1⟩
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn ⟨p, hpC⟩ continuous_snd.continuousOn
  have hqint : q.1 ∈ interior K := by
    by_contra hn
    exact hq.2 (hBN ⟨⟨subset_closure hq.1.1.1, hn⟩, hq.1.1.2⟩)
  have hqb : q.2 < b := lt_of_le_of_ne hq.1.1.2.2 (by
    intro heq
    exact Set.disjoint_left.mp hupper hq.1.2 ⟨hqint, mem_singleton_iff.mpr heq⟩)
  obtain ⟨x, rfl⟩ := hq.1.2
  apply hregular x hqint ⟨hq.1.1.2.1, hqb⟩
  have hxn : ∀ᶠ y in 𝓝 x, (e y).1 ∈ interior K :=
    (he.fst.continuousAt).preimage_mem_nhds (isOpen_interior.mem_nhds hqint)
  have htn : ∀ᶠ y in 𝓝 x, (e y).2 < b :=
    (he.snd.continuousAt).preimage_mem_nhds (Iio_mem_nhds hqb)
  filter_upwards [hxn, htn] with y hy hyt
  by_cases hay : a ≤ (e y).2
  · apply hmax
    exact ⟨⟨⟨interior_subset hy, hay, hyt.le⟩, mem_range_self y⟩,
      fun hn => (hcollar ⟨hn, mem_range_self y⟩).1 hy⟩
  · exact (lt_of_not_ge hay).le.trans hq.1.1.2.1
