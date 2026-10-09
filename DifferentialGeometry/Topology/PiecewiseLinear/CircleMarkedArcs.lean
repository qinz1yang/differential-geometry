/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_arc_between_marks_of_ne_colors
    {Q : Set E} (hQ : IsPLSphere 1 Q) {ι κ : Type*} [Finite ι]
    (q : ι → E) (hq : ∀ i, q i ∈ Q) (hinj : Function.Injective q) (c : ι → κ)
    {i₀ j₀ : ι} (hc : c i₀ ≠ c j₀) :
    ∃ (i j : ι) (β : ℝ → E), c i ≠ c j ∧
      IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1) ∧
      β 0 = q i ∧ β 1 = q j ∧ β '' Icc 0 1 ⊆ Q ∧
      (∀ k, q k ∉ β '' Ioo 0 1) ∧ IsClosed (Q \ β '' Ioo 0 1) := by
  have hij₀ : i₀ ≠ j₀ := fun h => hc (congrArg c h)
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ₀, hγ₁, -, -, hAB, hAiB⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hQ (hq i₀) (hq j₀) (hinj.ne hij₀)
  have hγinj := hγ.bijOn.injOn
  let T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∃ k, q k = γ t}
  have hTfin : T.Finite := by
    refine Set.Finite.of_finite_image ((Set.finite_range q).subset ?_)
      (hγinj.mono fun t ht => ht.1)
    rintro _ ⟨t, ⟨-, k, hk⟩, rfl⟩
    exact ⟨k, hk⟩
  have h0T : (0 : ℝ) ∈ T := ⟨⟨le_rfl, zero_le_one⟩, i₀, hγ₀.symm⟩
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, j₀, hγ₁.symm⟩
  obtain ⟨b, ⟨hbT, j, hj, hjc⟩, hbmin⟩ :=
    Set.exists_min_image {t | t ∈ T ∧ ∃ k, q k = γ t ∧ c k ≠ c i₀} id
      (hTfin.subset fun _ ht => ht.1) ⟨1, h1T, j₀, hγ₁.symm, hc.symm⟩
  have hb0 : 0 < b := by
    by_contra h
    have hb : b = 0 := le_antisymm (not_lt.mp h) hbT.1.1
    exact hjc (congrArg c (hinj (hj.trans (hb ▸ hγ₀))))
  obtain ⟨a, ⟨haT, hab⟩, hamax⟩ :=
    Set.exists_max_image {t | t ∈ T ∧ t < b} id
      (hTfin.subset fun _ ht => ht.1) ⟨0, h0T, hb0⟩
  obtain ⟨i, hi⟩ := haT.2
  have hic : c i = c i₀ := by
    by_contra h
    have hba : b ≤ a := hbmin a ⟨haT, i, hi, h⟩
    exact (not_le_of_gt hab) hba
  have hcolors : c i ≠ c j := fun hij => hjc (hij.symm.trans hic)
  have hsubI : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc haT.1.1 hbT.1.2
  obtain ⟨σ, hσ, hσ₀, hσ₁⟩ :=
    exists_isPLHomeomorphOn_Icc_map_endpoints (by norm_num : (0 : ℝ) < 1) hab
  have hγab := hγ.restrict (isHPolytope_Icc (a := a) (b := b)).isPolyhedron hsubI
  have hβ := hσ.trans hγab
  have hβIoo : (γ ∘ σ) '' Ioo 0 1 = γ '' Ioo a b := by
    rw [hβ.image_Ioo_eq_sdiff_endpoints (by norm_num : (0 : ℝ) < 1),
      hγab.image_Ioo_eq_sdiff_endpoints hab]
    simp only [Function.comp_apply, hσ₀, hσ₁]
  refine ⟨i, j, γ ∘ σ, hcolors, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hβ.image_eq]
    exact hβ
  · simpa only [Function.comp_apply, hσ₀] using hi.symm
  · simpa only [Function.comp_apply, hσ₁] using hj.symm
  · rw [hβ.image_eq, ← hAB]
    exact (image_mono hsubI).trans (hγ.image_eq.subset.trans subset_union_left)
  · intro k hk
    rw [hβIoo] at hk
    obtain ⟨t, ht, hkt⟩ := hk
    have htT : t ∈ T := ⟨hsubI (Ioo_subset_Icc_self ht), k, hkt.symm⟩
    have hta : t ≤ a := hamax t ⟨htT, ht.2⟩
    exact (not_le_of_gt ht.1) hta
  · have heq : Q \ (γ ∘ σ) '' Ioo 0 1 = B ∪ γ '' Icc 0 a ∪ γ '' Icc b 1 := by
      rw [hβIoo]
      ext z
      constructor
      · rintro ⟨hzQ, hzn⟩
        rw [← hAB] at hzQ
        rcases hzQ with hzA | hzB
        · obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hzA
          by_cases hta : t ≤ a
          · exact Or.inl (Or.inr ⟨t, ⟨ht.1, hta⟩, rfl⟩)
          · by_cases htb : b ≤ t
            · exact Or.inr ⟨t, ⟨htb, ht.2⟩, rfl⟩
            · exact (hzn ⟨t, ⟨lt_of_not_ge hta, lt_of_not_ge htb⟩, rfl⟩).elim
        · exact Or.inl (Or.inl hzB)
      · rintro ((hzB | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
        · refine ⟨by rw [← hAB]; exact Or.inr hzB, ?_⟩
          rintro ⟨t, ht, rfl⟩
          have htI : t ∈ Icc (0 : ℝ) 1 := hsubI (Ioo_subset_Icc_self ht)
          have hmem : γ t ∈ A ∩ B := ⟨hγ.bijOn.mapsTo htI, hzB⟩
          rw [hAiB, ← hγ₀, ← hγ₁] at hmem
          rcases hmem with h0 | h1
          · have ht0 : t = 0 := hγinj htI ⟨le_rfl, zero_le_one⟩ h0
            linarith [ht.1, haT.1.1]
          · have ht1 : t = 1 := hγinj htI ⟨zero_le_one, le_rfl⟩ h1
            linarith [ht.2, hbT.1.2]
        · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans haT.1.2⟩
          refine ⟨by rw [← hAB]; exact Or.inl (hγ.bijOn.mapsTo htI), ?_⟩
          rintro ⟨t', ht', hγt⟩
          have htt : t' = t := hγinj (hsubI (Ioo_subset_Icc_self ht')) htI hγt
          linarith [ht'.1, ht.2]
        · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hbT.1.1.trans ht.1, ht.2⟩
          refine ⟨by rw [← hAB]; exact Or.inl (hγ.bijOn.mapsTo htI), ?_⟩
          rintro ⟨t', ht', hγt⟩
          have htt : t' = t := hγinj (hsubI (Ioo_subset_Icc_self ht')) htI hγt
          linarith [ht'.2, ht.1]
    rw [heq]
    have hBc : IsClosed B :=
      ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ).isPolyhedron.isClosed
    refine (hBc.union ?_).union ?_
    · exact (isCompact_Icc.image_of_continuousOn
        (hγ.isPiecewiseAffineOn.continuousOn.mono (Icc_subset_Icc le_rfl haT.1.2))).isClosed
    · exact (isCompact_Icc.image_of_continuousOn
        (hγ.isPiecewiseAffineOn.continuousOn.mono (Icc_subset_Icc hbT.1.1 le_rfl))).isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
