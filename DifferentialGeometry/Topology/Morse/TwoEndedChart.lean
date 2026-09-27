/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.RadialChartExtension

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Morse

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}

theorem exists_chart_containing_two_radial_ends
    (χ : Bool → PartialDiffeomorph 𝓘(ℝ, F) I F M ∞)
    (C : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞) (z : Bool → F)
    {K : Set M} (hK : IsCompact K) (hKC : K ⊆ C.source) (hxK : ∀ i, χ i (z i) ∈ K)
    {f : M → ℝ} (hC : ∀ y ∈ C.source, (C y).im = f y)
    (a b : Bool → ℝ) (hlo : a true < b true) (hmid : b true < b false)
    (hhi : b false < a false)
    (hquad : ∀ i (t : ℝ), t • z i ∈ (χ i).source →
      f (χ i (t • z i)) = a i + t ^ 2 * (b i - a i))
    (hKf : ∀ y ∈ K, f y ∈ Icc (b true) (b false))
    {O : Set M} (hO : IsOpen O) (hKO : K ⊆ O)
    (hray : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      t • z i ∈ (χ i).source ∧ χ i (t • z i) ∈ O) :
    ∃ (D : Bool → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞)
      (c : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞),
      let R := fun i => (fun t : ℝ => χ i (t • z i)) '' Icc (0 : ℝ) 1
      K ∪ R false ∪ R true ⊆ c.source ∧ c.source ⊆ O ∧
      (∀ i, χ i 0 ∈ c.source ∧ χ i (z i) ∈ c.source ∧ D i (z i) = C (χ i (z i))) ∧
      (∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ V ⊆ c.source ∩ C.source ∧ EqOn c C V) ∧
      ∀ i, ∃ V : Set M, IsOpen V ∧ R i ⊆ V ∧ V ⊆ c.source ∩ (χ i).target ∧
        (∀ y ∈ V, c y = D i ((χ i).symm y)) ∧
        c '' R i = D i '' ((fun t : ℝ => t • z i) '' Icc (0 : ℝ) 1) := by
  let R := fun i => (fun t : ℝ => χ i (t • z i)) '' Icc (0 : ℝ) 1
  have hz (i : Bool) : z i ∈ (χ i).source := by
    simpa only [one_smul] using (hray i 1 ⟨zero_le_one, le_rfl⟩).1
  have hRc (i : Bool) : IsCompact (R i) := isCompact_Icc.image_of_continuousOn
    ((χ i).contMDiffOn.continuousOn.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => (hray i t ht).1))
  have hRO (i : Bool) : R i ⊆ O := by
    rintro y ⟨t, ht, rfl⟩
    exact (hray i t ht).2
  have hDexists (i : Bool) := exists_diffeomorph_extending_radial_height_chart
    (χ i) C (hz i) (hKC (hxK i)) hC
    (show a i ≠ b i by
      cases i
      · exact hhi.ne'
      · exact hlo.ne) (hquad i)
  choose D hD hDsep hsource hmatch happly using hDexists
  let e (i : Bool) := (χ i).symm.trans (D i).toPartialDiffeomorph
  have hsep₀ (t : ℝ) (ht : t < 1) : 0 < (D false (t • z false)).im - b false := by
    rcases mul_pos_iff.mp (hDsep false t ht) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sub_pos.mpr hhi).le h.2).elim
  have hsep₁ (t : ℝ) (ht : t < 1) : 0 < -1 * ((D true (t • z true)).im - b true) := by
    rcases mul_pos_iff.mp (hDsep true t ht) with h | h
    · exact (not_lt_of_ge (sub_neg.mpr hlo).le h.2).elim
    · simpa only [neg_one_mul] using neg_pos.mpr h.1
  obtain ⟨c₀, hc₀s, hc₀O, hc₀K, hc₀R⟩ :=
    exists_chart_pasting_radial_segment (χ false) C (D false) hK hKC (hxK false)
      (a := a false) (b := b false) (σ := 1) (by simpa using sub_pos.mpr hhi)
      (fun t ht => hquad false t (hray false t ht).1)
      (fun y hy => by simpa using sub_nonpos.mpr (hKf y hy).2)
      (fun y hy => by simpa only [one_mul, hC y (hKC hy)] using
        sub_nonpos.mpr (hKf y hy).2)
      (fun t ht => by simpa only [one_mul] using hsep₀ t ht)
      (hmatch false) hO hKO (hray false)
  have hR₀f (y : M) (hy : y ∈ R false) : b false ≤ f y := by
    obtain ⟨t, ht, rfl⟩ := hy
    rw [hquad false t (hray false t ht).1]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hp := mul_nonneg (sub_nonneg.mpr ht2) (sub_pos.mpr hhi).le
    nlinarith
  have hR₀c (y : M) (hy : y ∈ R false) : b false ≤ (c₀ y).im := by
    have heq := (hc₀R y hy).eq_of_nhds
    obtain ⟨t, ht, rfl⟩ := hy
    have hv := (happly false (t • z false) (hray false t ht).1)
    rw [heq.trans hv]
    by_cases ht1 : t = 1
    · rw [ht1, one_smul, hD false, hC _ (hKC (hxK false))]
      have hh := hquad false 1 (by simpa only [one_smul] using hz false)
      simpa only [one_smul, one_pow, one_mul, add_sub_cancel] using hh.ge
    · exact (sub_pos.mp (hsep₀ t (ht.2.lt_of_ne ht1))).le
  have hK₁f (y : M) (hy : y ∈ K ∪ R false) : -1 * (f y - b true) ≤ 0 := by
    have hb : b true ≤ f y := hy.elim (fun h => (hKf y h).1)
      (fun h => hmid.le.trans (hR₀f y h))
    linarith
  have hK₁c (y : M) (hy : y ∈ K ∪ R false) : -1 * ((c₀ y).im - b true) ≤ 0 := by
    have hb : b true ≤ (c₀ y).im := by
      rcases hy with hy | hy
      · rw [(hc₀K y hy).eq_of_nhds, hC y (hKC hy)]
        exact (hKf y hy).1
      · exact hmid.le.trans (hR₀c y hy)
    linarith
  obtain ⟨c, hcs, hcO, hcK₀, hcR₁⟩ :=
    exists_chart_pasting_radial_segment (χ true) c₀ (D true) (hK.union (hRc false))
      hc₀s (Or.inl (hxK true)) (a := a true) (b := b true) (σ := -1)
      (by linarith) (fun t ht => hquad true t (hray true t ht).1) hK₁f hK₁c
      hsep₁ ((hmatch true).trans (hc₀K _ (hxK true)).symm) hO
      (union_subset hKO (hRO false)) (hray true)
  have hcK (y : M) (hy : y ∈ K) : (c : M → ℂ) =ᶠ[𝓝 y] C :=
    (hcK₀ y (Or.inl hy)).trans (hc₀K y hy)
  have hcR (i : Bool) (y : M) (hy : y ∈ R i) : (c : M → ℂ) =ᶠ[𝓝 y] e i := by
    cases i
    · exact (hcK₀ y (Or.inr hy)).trans (hc₀R y hy)
    · exact hcR₁ y hy
  have hRsource (i : Bool) : R i ⊆ c.source := by
    cases i
    · exact fun _ hy => hcs (Or.inl (Or.inr hy))
    · exact fun _ hy => hcs (Or.inr hy)
  refine ⟨D, c, hcs, hcO, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hRsource i ⟨0, ⟨le_rfl, zero_le_one⟩, by simp only [zero_smul]⟩,
      hcs (Or.inl (Or.inl (hxK i))), hD i⟩
  · let V := c.source ∩ C.source ∩ interior {y | c y = C y}
    refine ⟨V, (c.open_source.inter C.open_source).inter isOpen_interior, ?_,
      inter_subset_left, fun y hy => interior_subset (s := {y | c y = C y}) hy.2⟩
    intro y hy
    exact ⟨⟨hcs (Or.inl (Or.inl hy)), hKC hy⟩, mem_interior_iff_mem_nhds.mpr (hcK y hy)⟩
  · intro i
    let V := c.source ∩ (χ i).target ∩ interior {y | c y = e i y}
    have hRχ : R i ⊆ (χ i).target := by
      rintro y ⟨t, ht, rfl⟩
      exact (χ i).map_source (hray i t ht).1
    refine ⟨V, (c.open_source.inter (χ i).open_target).inter isOpen_interior, ?_,
      inter_subset_left, fun y hy => interior_subset (s := {y | c y = e i y}) hy.2, ?_⟩
    · intro y hy
      exact ⟨⟨hRsource i hy, hRχ hy⟩, mem_interior_iff_mem_nhds.mpr (hcR i y hy)⟩
    · rw [image_image, image_image]
      apply image_congr
      intro t ht
      exact ((hcR i _ ⟨t, ht, rfl⟩).eq_of_nhds).trans
        (happly i _ (hray i t ht).1)

end DifferentialGeometry.Morse
