import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas


open Set Filter
open scoped Topology

theorem IsCompact.exists_Icc_mapsTo_of_continuousOn
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {t₀ T : ℝ} (ht : t₀ < T) {Y : Type*} [TopologicalSpace Y]
    {f : X × ℝ → Y} {U : Set Y} (hU : IsOpen U)
    (hf : ContinuousOn f (K ×ˢ Icc t₀ T))
    (hKU : ∀ x, x ∈ K → f (x, t₀) ∈ U) :
    ∃ τ, 0 < τ ∧ τ ≤ T - t₀ ∧
      ∀ x, x ∈ K → ∀ t, t ∈ Icc t₀ (t₀ + τ) → f (x, t) ∈ U := by
  have hpre : f ⁻¹' U ∈ 𝓝ˢ[K ×ˢ Icc t₀ T] (K ×ˢ ({t₀} : Set ℝ)) := by
    have hU' : U ∈ 𝓝ˢ (f '' (K ×ˢ ({t₀} : Set ℝ))) :=
      hU.mem_nhdsSet.mpr <| by
        rintro _ ⟨p, hp, rfl⟩
        rcases p with ⟨x, t⟩
        rcases hp with ⟨hx, htmem⟩
        have ht' : t = t₀ := by simpa using htmem
        subst t
        exact hKU x hx
    have hpre' := hf.preimage_mem_nhdsSetWithin_of_mem_nhdsSet hU'
    refine (nhdsSetWithin_mono_left ?_ hpre')
    intro p hp
    rcases p with ⟨x, t⟩
    rcases hp with ⟨hx, htmem⟩
    have ht' : t = t₀ := by simpa using htmem
    subst t
    exact ⟨⟨hx, ⟨le_rfl, ht.le⟩⟩, ⟨x, t₀⟩, ⟨hx, rfl⟩, rfl⟩
  obtain ⟨V, hVopen, hVtarget, hVsub⟩ := mem_nhdsSetWithin.mp hpre
  obtain ⟨Ux, Vt, hUxopen, hVtopen, hKUx, ht₀Vt, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hVopen hVtarget
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hVtopen.mem_nhds (ht₀Vt rfl))
  refine ⟨min (ε / 2) (T - t₀), lt_min (by positivity) (sub_pos.mpr ht), min_le_right _ _, ?_⟩
  intro x hx t htI
  have htt : t ∈ Vt := by
    refine hεsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htI.1)]
    have htminus : t - t₀ ≤ min (ε / 2) (T - t₀) := by linarith [htI.2]
    have hτ : min (ε / 2) (T - t₀) < ε :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact lt_of_le_of_lt htminus hτ
  have htT : t ∈ Icc t₀ T := by
    refine ⟨htI.1, ?_⟩
    linarith [htI.2, min_le_right (ε / 2) (T - t₀)]
  exact hVsub ⟨hUV ⟨hKUx hx, htt⟩, ⟨hx, htT⟩⟩

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

end DifferentialGeometry.Topology.Compactness

theorem IsCompact.exists_prod_Icc_superset_of_isOpen
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {a b : ℝ} (hab : a ≤ b) {U : Set (X × ℝ)} (hU : IsOpen U)
    (hsub : K ×ˢ Icc a b ⊆ U) :
    ∃ lo hi : ℝ, lo < a ∧ b < hi ∧ K ×ˢ Icc lo hi ⊆ U := by
  obtain ⟨A, V, _, hV, hKA, hseg, hAV⟩ :=
    generalized_tube_lemma hK isCompact_Icc hU hsub
  obtain ⟨l, u, hl, hu, hlu⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_interval_subset_of_isOpen
      hab hV hseg
  obtain ⟨lo, hllo, hloa⟩ := exists_between hl
  obtain ⟨hi, hbhi, hhiu⟩ := exists_between hu
  exact ⟨lo, hi, hloa, hbhi,
    fun p hp => hAV ⟨hKA hp.1, hlu (Icc_subset_Ioo hllo hhiu hp.2)⟩⟩
