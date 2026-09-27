import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set

theorem IsCompact.exists_pos_sublevel_subset {M : Type*} [TopologicalSpace M]
    {K U : Set M} (hK : IsCompact K) {f : M → ℝ} (hf : ContinuousOn f K)
    (hU : IsOpen U) {a : ℝ} (hsub : K ∩ f ⁻¹' Iic a ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ K ∩ f ⁻¹' Iic (a + ε) ⊆ U := by
  by_cases hne : (K ∩ Uᶜ).Nonempty
  · obtain ⟨q, hq, hqmin⟩ :=
      (hK.inter_right hU.isClosed_compl).exists_isMinOn hne (hf.mono inter_subset_left)
    have haq : a < f q := lt_of_not_ge (fun h => hq.2 (hsub ⟨hq.1, h⟩))
    refine ⟨(f q - a) / 2, by linarith, ?_⟩
    rintro x ⟨hxK, hxf⟩
    by_contra hxU
    have hle : f q ≤ f x := hqmin ⟨hxK, hxU⟩
    change f x ≤ a + (f q - a) / 2 at hxf
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    rintro x ⟨hx, _⟩
    by_contra hxU
    exact hne ⟨x, hx, hxU⟩

theorem IsCompact.exists_pos_superlevel_subset {M : Type*} [TopologicalSpace M]
    {K U : Set M} (hK : IsCompact K) {f : M → ℝ} (hf : ContinuousOn f K)
    (hU : IsOpen U) {a : ℝ} (hsub : K ∩ f ⁻¹' Ici a ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ K ∩ f ⁻¹' Ici (a - ε) ⊆ U := by
  obtain ⟨ε, hε, hlow⟩ := hK.exists_pos_sublevel_subset hf.neg hU
    (a := -a) (by
      rintro x ⟨hxK, hxf⟩
      change -f x ≤ -a at hxf
      exact hsub ⟨hxK, neg_le_neg_iff.mp hxf⟩)
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hxK, hxf⟩
  apply hlow
  refine ⟨hxK, ?_⟩
  change -f x ≤ -a + ε
  change a - ε ≤ f x at hxf
  linarith

theorem Continuous.exists_sublevel_subset_of_unique_minimum {M : Type*} [TopologicalSpace M]
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) {p : M}
    (hmin : ∀ x, x ≠ p → f p < f x) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' Iic (f p + ε) ⊆ U := by
  obtain ⟨ε, hε, hlow⟩ := isCompact_univ.exists_pos_sublevel_subset hf.continuousOn hU
    (a := f p) (by
      rintro x ⟨_, hx⟩
      have heq : x = p := by
        by_contra hne
        exact (hmin x hne).not_ge hx
      exact heq ▸ hp)
  exact ⟨ε, hε, fun _ hx => hlow ⟨mem_univ _, hx⟩⟩

theorem Continuous.exists_superlevel_subset_of_unique_maximum {M : Type*} [TopologicalSpace M]
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) {p : M}
    (hmax : ∀ x, x ≠ p → f x < f p) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' Ici (f p - ε) ⊆ U := by
  obtain ⟨ε, hε, hhigh⟩ := isCompact_univ.exists_pos_superlevel_subset hf.continuousOn hU
    (a := f p) (by
      rintro x ⟨_, hx⟩
      have heq : x = p := by
        by_contra hne
        exact (hmax x hne).not_ge hx
      exact heq ▸ hp)
  exact ⟨ε, hε, fun _ hx => hhigh ⟨mem_univ _, hx⟩⟩

section

open Filter Set
open scoped Topology

theorem Continuous.exists_pos_sublevel_subset_of_unique_zero
    {B : Type*} [TopologicalSpace B] [CompactSpace B]
    {rho : B → ℝ} (hrho : Continuous rho) (hnonneg : ∀ x, 0 ≤ rho x)
    {o : B} (hzero : ∀ x, rho x = 0 → x = o) {D : Set B} (hD : D ∈ 𝓝 o) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, rho x < ε → x ∈ D := by
  obtain ⟨W, hWD, hW, hoW⟩ := mem_nhds_iff.mp hD
  obtain ⟨ε, hε, hsub⟩ := isCompact_univ.exists_pos_sublevel_subset hrho.continuousOn hW
    (a := 0) (by
      rintro x ⟨_, hx⟩
      have hx0 : rho x = 0 := le_antisymm hx (hnonneg x)
      exact hzero x hx0 ▸ hoW)
  refine ⟨ε, hε, fun x hx => hWD (hsub ⟨mem_univ x, ?_⟩)⟩
  simpa only [mem_preimage, mem_Iic, zero_add] using hx.le

end

open scoped ENNReal in
theorem IsCompact.exists_lt_lt_sublevel_subset
    {X L : Type*} [TopologicalSpace X] [LinearOrder L] [DenselyOrdered L]
    [TopologicalSpace L] [ClosedIicTopology L] {f : X → L} {r R : L} {U : Set X}
    (hK : IsCompact {x | f x ≤ R}) (hf : ContinuousOn f {x | f x ≤ R})
    (hU : IsOpen U) (hsub : {x | f x ≤ r} ⊆ U) (hrR : r < R) :
    ∃ s, r < s ∧ s < R ∧ {x | f x ≤ s} ⊆ U := by
  by_cases hne : ({x | f x ≤ R} \ U).Nonempty
  · obtain ⟨q, hq, hmin⟩ := (hK.diff hU).exists_isMinOn hne (hf.mono sdiff_subset)
    have hrq : r < f q := lt_of_not_ge (fun h => hq.2 (hsub h))
    obtain ⟨s, hrs, hs⟩ := exists_between (lt_min hrR hrq)
    refine ⟨s, hrs, hs.trans_le (min_le_left _ _), ?_⟩
    intro x hx
    by_contra hxU
    have hqx : f q ≤ f x := hmin ⟨hx.trans (hs.le.trans (min_le_left _ _)), hxU⟩
    exact (hs.trans_le (min_le_right _ _)).not_ge (hqx.trans hx)
  · obtain ⟨s, hrs, hsR⟩ := exists_between hrR
    refine ⟨s, hrs, hsR, ?_⟩
    intro x hx
    by_contra hxU
    exact hne ⟨x, hx.trans hsR.le, hxU⟩


open scoped ENNReal in
theorem IsCompact.exists_lt_lt_ofReal_sublevel_subset
    {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞} {r R : ℝ} {U : Set X}
    (hK : IsCompact {x | f x ≤ ENNReal.ofReal R})
    (hf : ContinuousOn f {x | f x ≤ ENNReal.ofReal R})
    (hU : IsOpen U) (hsub : {x | f x ≤ ENNReal.ofReal r} ⊆ U) (hrR : r < R) :
    ∃ s : ℝ, r < s ∧ s < R ∧ {x | f x ≤ ENNReal.ofReal s} ⊆ U := by
  by_cases hr : 0 ≤ r
  · obtain ⟨s, hrs, hsR, hssub⟩ := hK.exists_lt_lt_sublevel_subset hf hU hsub
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mpr hrR)
    have hsfin : s ≠ ∞ := ne_top_of_lt hsR
    refine ⟨s.toReal, (ENNReal.ofReal_lt_iff_lt_toReal hr hsfin).mp hrs,
      ENNReal.toReal_lt_of_lt_ofReal hsR, ?_⟩
    simpa only [ENNReal.ofReal_toReal hsfin] using hssub
  · have hrzero : r < 0 := lt_of_not_ge hr
    obtain ⟨s, hrs, hs⟩ := exists_between (lt_min hrR hrzero)
    refine ⟨s, hrs, hs.trans_le (min_le_left _ _), ?_⟩
    have hsnonpos : s ≤ 0 := (hs.trans_le (min_le_right _ _)).le
    simpa only [ENNReal.ofReal_of_nonpos hsnonpos, ENNReal.ofReal_of_nonpos hrzero.le]
      using hsub
