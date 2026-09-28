/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.WallProductBlockTypedTransport

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem IsStableCrossingBlock.of_le_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η' :=
  ⟨h.1, hη', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans (by linarith), h.2.2.2.2.2⟩

theorem IsStableCrossingBlock.congr_of_eq {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hfg : ∀ x ∈ S, g x ∈ chartBlock ec A r tlo ∨ f x ∈ chartBlock ec A r tlo → g x = f x) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hm, hcpt, hcl, hside, hpre, hdis, hgA, hgB, hplA, hplB, hnA, hnB,
    hLipa, hLipb, hpa, hpb⟩ := h
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = S ∩ f ⁻¹' chartBlock ec A r tlo := by
    ext x
    constructor
    · rintro ⟨hx, hgx⟩
      refine ⟨hx, ?_⟩
      change f x ∈ chartBlock ec A r tlo
      rw [← hfg x hx (Or.inl hgx)]
      exact hgx
    · rintro ⟨hx, hfx⟩
      refine ⟨hx, ?_⟩
      change g x ∈ chartBlock ec A r tlo
      rw [hfg x hx (Or.inr hfx)]
      exact hfx
  have heq : ∀ x ∈ SA ∪ SB, g x = f x := by
    intro x hx
    rw [← hpre] at hx
    exact hfg x hx.1 (Or.inr hx.2)
  have heqA : EqOn (blockSheetProjA ec A g) (blockSheetProjA ec A f) SA := fun x hx => by
    simp only [blockSheetProjA, heq x (Or.inl hx)]
  have heqB : EqOn (blockSheetProjB ec A g) (blockSheetProjB ec A f) SB := fun x hx => by
    simp only [blockSheetProjB, heq x (Or.inr hx)]
  refine ⟨hr, hη, hLa, hLb, hm, hcpt, hcl, ?_, hpre'.trans hpre, hdis, ?_, ?_, ?_, ?_, ?_, ?_,
    hLipa, hLipb, hpa, hpb⟩
  · rcases hside with h1 | ⟨h0, hz, hfr⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h0, hz, fun x hx => ?_⟩
      rw [heq x hx]
      exact hfr x hx
  · intro x hx
    rw [heq x (Or.inl hx)]
    exact hgA x hx
  · intro x hx
    rw [heq x (Or.inr hx)]
    exact hgB x hx
  · rw [heqA.image_eq]
    exact hplA.congr heqA
  · rw [heqB.image_eq]
    exact hplB.congr heqB
  · intro x hx hin
    rw [heq x (Or.inl hx)] at hin
    rw [heqA.image_eq, heqA hx]
    exact hnA x hx hin
  · intro x hx hin
    rw [heq x (Or.inr hx)] at hin
    rw [heqB.image_eq, heqB hx]
    exact hnB x hx hin

theorem mem_chartBlock_of_norm_lt {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {s t : ℝ} {z : M} (hz : z ∈ ec.source)
    (hzn : ‖A (ec z)‖ < s) (ht : t = -s ∨ t = 0) (ht0 : t = 0 → 0 ≤ (A (ec z)).2.2) :
    z ∈ chartBlock ec A s t := by
  have h1 : |(A (ec z)).1| < s := by
    have := norm_fst_le (A (ec z))
    rw [Real.norm_eq_abs] at this
    linarith
  have h2 : ‖(A (ec z)).2‖ ≤ ‖A (ec z)‖ := norm_snd_le _
  have h21 : |(A (ec z)).2.1| < s := by
    have := norm_fst_le (A (ec z)).2
    rw [Real.norm_eq_abs] at this
    linarith
  have h22 : |(A (ec z)).2.2| < s := by
    have := norm_snd_le (A (ec z)).2
    rw [Real.norm_eq_abs] at this
    linarith
  refine ⟨hz, ?_⟩
  change |(A (ec z)).1| ≤ s ∧ |(A (ec z)).2.1| ≤ s ∧ t ≤ (A (ec z)).2.2 ∧ (A (ec z)).2.2 ≤ s
  refine ⟨h1.le, h21.le, ?_, (le_abs_self _).trans h22.le⟩
  rcases ht with ht | ht
  · rw [ht]
    have := neg_abs_le ((A (ec z)).2.2)
    linarith
  · exact ht ▸ ht0 ht

theorem IsStableCrossingBlock.exists_isOpen_mem_chartBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y : M}
    (hy : y ∈ innerChartBlock ec A r tlo) :
    ∃ N₀ : Set M, IsOpen N₀ ∧ y ∈ N₀ ∧
      ∀ z ∈ N₀, (y ∈ BdM → 0 ≤ ℓ (ec z)) → z ∈ chartBlock ec A r tlo := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -⟩ := h
  have htle : tlo ≤ 0 := by
    rcases hside with ⟨ht, -⟩ | ⟨ht, -⟩
    · linarith
    · exact ht.le
  have hyB : y ∈ chartBlock ec A r tlo := chartBlock_mono_of_half ec A hr.le htle hy
  have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  obtain ⟨hys, hy1, hy2, hy3, hy4⟩ := hy
  have ho1 : IsOpen {p : ℝ × ℝ × ℝ | |p.1| < r} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have ho2 : IsOpen {p : ℝ × ℝ × ℝ | |p.2.1| < r} :=
    isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const
  have ho3 : IsOpen {p : ℝ × ℝ × ℝ | p.2.2 < r} :=
    isOpen_lt (continuous_snd.comp continuous_snd) continuous_const
  have ho4 : IsOpen {p : ℝ × ℝ × ℝ | tlo < p.2.2} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
  by_cases hyBd : y ∈ BdM
  · have hside0 : tlo = 0 ∧ ∀ z, (A z).2.2 = ℓ z := by
      rcases hside with ⟨-, hdis⟩ | ⟨ht, hz, -⟩
      · exact absurd hyBd (Set.disjoint_left.mp hdis hyB)
      · exact ⟨ht, hz⟩
    refine ⟨ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' ({p : ℝ × ℝ × ℝ | |p.1| < r} ∩
      ({p : ℝ × ℝ × ℝ | |p.2.1| < r} ∩ {p : ℝ × ℝ × ℝ | p.2.2 < r}))),
      ec.isOpen_inter_preimage ((ho1.inter (ho2.inter ho3)).preimage hAc), ⟨hys, ?_⟩, ?_⟩
    · change |(A (ec y)).1| < r ∧ |(A (ec y)).2.1| < r ∧ (A (ec y)).2.2 < r
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro z ⟨hz, hz1, hz2, hz3⟩ hz0
      refine ⟨hz, ?_⟩
      change |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧ tlo ≤ (A (ec z)).2.2 ∧
        (A (ec z)).2.2 ≤ r
      refine ⟨le_of_lt hz1, le_of_lt hz2, ?_, le_of_lt hz3⟩
      rw [hside0.1, hside0.2]
      exact hz0 hyBd
  · refine ⟨ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' ({p : ℝ × ℝ × ℝ | |p.1| < r} ∩
      ({p : ℝ × ℝ × ℝ | |p.2.1| < r} ∩ ({p : ℝ × ℝ × ℝ | tlo < p.2.2} ∩
        {p : ℝ × ℝ × ℝ | p.2.2 < r})))),
      ec.isOpen_inter_preimage ((ho1.inter (ho2.inter (ho4.inter ho3))).preimage hAc),
      ⟨hys, ?_⟩, ?_⟩
    · change |(A (ec y)).1| < r ∧ |(A (ec y)).2.1| < r ∧ tlo < (A (ec y)).2.2 ∧
        (A (ec y)).2.2 < r
      refine ⟨by linarith, by linarith, ?_, by linarith⟩
      rcases hside with ⟨ht, -⟩ | ⟨ht, hz, -⟩
      · rw [ht] at hy3 ⊢
        linarith
      · rw [ht, zero_div] at hy3
        rw [ht]
        have hne : (A (ec y)).2.2 ≠ 0 := by
          rw [hz]
          exact fun h0 => hyBd ((hBd y hys).mpr h0)
        exact lt_of_le_of_ne hy3 (Ne.symm hne)
    · rintro z ⟨hz, hz1, hz2, hz3, hz4⟩ -
      refine ⟨hz, ?_⟩
      change |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧ tlo ≤ (A (ec z)).2.2 ∧
        (A (ec z)).2.2 ≤ r
      exact ⟨le_of_lt hz1, le_of_lt hz2, le_of_lt hz3, le_of_lt hz4⟩

theorem IsStableCrossingBlock.chartBlock_subset_of_subset_ball
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {r' tlo' : ℝ} (hr' : 0 < r')
    (hside' : (tlo' = -r' ∧ Disjoint (chartBlock ec A r' tlo') BdM) ∨
      (tlo' = 0 ∧ ∀ z, (A z).2.2 = ℓ z))
    {y : M} (hys : y ∈ ec.source) (hA0 : A (ec y) = 0)
    (hball : chartBlock ec A r' tlo' ⊆ ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' ball 0 r)) :
    (tlo = -r → tlo' = -r') ∧ (tlo = 0 → tlo' = 0) ∧
      chartBlock ec A r' tlo' ⊆ chartBlock ec A r tlo := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -⟩ := h
  have htle' : tlo' ≤ 0 := by
    rcases hside' with ⟨ht, -⟩ | ⟨ht, -⟩
    · linarith
    · exact ht.le
  have htle : tlo ≤ 0 := by
    rcases hside with ⟨ht, -⟩ | ⟨ht, -⟩
    · linarith
    · exact ht.le
  have hcen : ∀ s t : ℝ, 0 < s → t ≤ 0 → y ∈ chartBlock ec A s t := by
    intro s t hs ht
    refine ⟨hys, ?_⟩
    change |(A (ec y)).1| ≤ s ∧ |(A (ec y)).2.1| ≤ s ∧ t ≤ (A (ec y)).2.2 ∧ (A (ec y)).2.2 ≤ s
    rw [hA0]
    change |(0 : ℝ)| ≤ s ∧ |(0 : ℝ)| ≤ s ∧ t ≤ 0 ∧ (0 : ℝ) ≤ s
    rw [abs_zero]
    exact ⟨hs.le, hs.le, ht, hs.le⟩
  have hyBd : y ∈ BdM ↔ ℓ (ec y) = 0 := hBd y hys
  have hcomp : ∀ z ∈ chartBlock ec A r' tlo', |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧
      -r ≤ (A (ec z)).2.2 ∧ (A (ec z)).2.2 ≤ r := by
    intro z hz
    have hn : ‖A (ec z)‖ < r := mem_ball_zero_iff.mp (hball hz).2
    have h1 := norm_fst_le (A (ec z))
    have h2 := norm_snd_le (A (ec z))
    have h21 := norm_fst_le (A (ec z)).2
    have h22 := norm_snd_le (A (ec z)).2
    rw [Real.norm_eq_abs] at h1 h21 h22
    have := neg_abs_le ((A (ec z)).2.2)
    have := le_abs_self ((A (ec z)).2.2)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rcases hside with ⟨ht, hdis⟩ | ⟨ht, hz⟩
  · have hynB : y ∉ BdM := fun hB => Set.disjoint_left.mp hdis (hcen r tlo hr htle) hB
    have ht' : tlo' = -r' := by
      rcases hside' with ⟨ht', -⟩ | ⟨-, hz'⟩
      · exact ht'
      · exfalso
        apply hynB
        rw [hyBd, ← hz', hA0]
        rfl
    refine ⟨fun _ => ht', fun h0 => absurd (ht.symm.trans h0) (by linarith), ?_⟩
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hcomp z hz
    refine ⟨(hball hz).1, ?_⟩
    change |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧ tlo ≤ (A (ec z)).2.2 ∧ (A (ec z)).2.2 ≤ r
    rw [ht]
    exact ⟨h1, h2, h3, h4⟩
  · have hyB : y ∈ BdM := by
      rw [hyBd, ← hz.1, hA0]
      rfl
    have ht' : tlo' = 0 := by
      rcases hside' with ⟨-, hdis'⟩ | ⟨ht', -⟩
      · exact absurd hyB (Set.disjoint_left.mp hdis' (hcen r' tlo' hr' htle'))
      · exact ht'
    refine ⟨fun h0 => absurd (ht.symm.trans h0) (by linarith), fun _ => ht', ?_⟩
    intro z hzB
    obtain ⟨h1, h2, -, h4⟩ := hcomp z hzB
    refine ⟨(hball hzB).1, ?_⟩
    change |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧ tlo ≤ (A (ec z)).2.2 ∧ (A (ec z)).2.2 ≤ r
    have h3 : tlo' ≤ (A (ec z)).2.2 := hzB.2.2.2.1
    rw [ht, ← ht']
    exact ⟨h1, h2, h3, h4⟩

theorem IsStableCrossingBlock.exists_recentre_localized_subset [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀in : y₀ ∈ innerChartBlock ec A r tlo)
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω) (hKc : IsClosed Kc)
    (hKcΩ : Kc ⊆ Ω) {O₀ : Set M} (hO₀ : IsOpen O₀) (hy₀O₀ : y₀ ∈ O₀) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r₁ tlo₁ : ℝ) (a₁ b₁ : ℝ × ℝ → ℝ),
      0 < r₁ ∧ (∀ z, A' z = A z - A (ec y₀)) ∧ chartBlock ec A' r₁ tlo₁ ⊆ O₀ ∧
      IsStableCrossingBlock f S ec ℓ BdM A' r₁ tlo₁ (SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁)
        (SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁) a₁ b₁ La Lb η ∧
      ((∀ x ∈ SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∈ Ω) ∨
        ∀ x ∈ SA ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∉ Kc) ∧
      ((∀ x ∈ SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∈ Ω) ∨
        ∀ x ∈ SB ∩ f ⁻¹' chartBlock ec A' r₁ tlo₁, x ∉ Kc) := by
  obtain ⟨hr, -, -, -, -, -, -, hside, -, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have hy₀B : y₀ ∈ chartBlock ec A r tlo := chartBlock_mono_of_half ec A hr.le htle hy₀in
  have hy₀s : y₀ ∈ ec.source := hy₀B.1
  obtain ⟨⟨xA, hxA, hfxA⟩, ⟨xB, hxB, hfxB⟩⟩ :=
    sheets_nonempty_of_isStableCrossingBlock h hy₀ hy₀B
  have hfxA' : f xA = y₀ := hfxA
  have hfxB' : f xB = y₀ := hfxB
  have hGsel : ∀ x₀ : EuclideanSpace ℝ (Fin 2), ∃ G : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen G ∧ x₀ ∈ G ∧ (G ⊆ Ω ∨ Disjoint G Kc) := by
    intro x₀
    by_cases hx₀ : x₀ ∈ Ω
    · exact ⟨Ω, hΩ, hx₀, Or.inl subset_rfl⟩
    · exact ⟨Kcᶜ, hKc.isOpen_compl, fun h => hx₀ (hKcΩ h), Or.inr disjoint_compl_left⟩
  obtain ⟨GA, hGAo, hxGA, hGA⟩ := hGsel xA
  obtain ⟨GB, hGBo, hxGB, hGB⟩ := hGsel xB
  obtain ⟨ρA, hρA, hρA'⟩ := hplA.exists_pos_mem_of_dist_lt hxA hGAo hxGA
  obtain ⟨ρB, hρB, hρB'⟩ := hplB.exists_pos_mem_of_dist_lt hxB hGBo hxGB
  have ht₀0 : tlo = 0 → 0 ≤ (A (ec y₀)).2.2 := by
    intro h0
    have h1 : tlo / 2 ≤ (A (ec y₀)).2.2 := hy₀in.2.2.2.1
    rw [h0, zero_div] at h1
    exact h1
  set ρ₃ : ℝ := if (A (ec y₀)).2.2 = 0 then 1 else |(A (ec y₀)).2.2| with hρ₃
  have hρ₃pos : 0 < ρ₃ := by
    rw [hρ₃]
    split_ifs with h0
    · exact one_pos
    · exact abs_pos.mpr h0
  set ρ : ℝ := min (min ρA ρB) ρ₃
  have hρpos : 0 < ρ := lt_min (lt_min hρA hρB) hρ₃pos
  have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  set O : Set M := ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' ball (A (ec y₀)) ρ) ∩ O₀
  have hOo : IsOpen O := (ec.isOpen_inter_preimage (isOpen_ball.preimage hAc)).inter hO₀
  have hy₀O : y₀ ∈ O := ⟨⟨hy₀s, mem_ball_self hρpos⟩, hy₀O₀⟩
  set A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ :=
    A.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ × ℝ) (-(A (ec y₀)))) with hA'def
  have hA'app : ∀ z, A' z = A z - A (ec y₀) := by
    intro z
    rw [hA'def, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add,
      neg_add_eq_sub]
  have hOpos : ∀ z ∈ O, tlo = 0 → (A (ec y₀)).2.2 ≠ 0 → 0 < (A (ec z)).2.2 := by
    intro z hz h0 hne
    have hd : dist (A (ec z)) (A (ec y₀)) < ρ := hz.1.2
    have h1 : |(A (ec z)).2.2 - (A (ec y₀)).2.2| < |(A (ec y₀)).2.2| := by
      have h2 : dist (A (ec z)).2.2 (A (ec y₀)).2.2 ≤ dist (A (ec z)) (A (ec y₀)) := by
        rw [Prod.dist_eq (x := A (ec z)), Prod.dist_eq (x := (A (ec z)).2)]
        exact (le_max_right _ _).trans (le_max_right _ _)
      rw [Real.dist_eq] at h2
      have h3 : ρ ≤ |(A (ec y₀)).2.2| := by
        have h5 : ρ₃ = |(A (ec y₀)).2.2| := by rw [hρ₃, ite_eq_right hne]
        rw [← h5]
        exact min_le_right _ _
      linarith
    have h4 : 0 < (A (ec y₀)).2.2 := lt_of_le_of_ne (ht₀0 h0) (Ne.symm hne)
    rw [abs_of_pos h4] at h1
    have := (abs_lt.mp h1).1
    linarith
  obtain ⟨r₁, tlo₁, a₁, b₁, hr₁, hB₁, hsubO⟩ :=
    IsStableCrossingBlock.exists_kink_recentre (ec' := ec) (ℓ' := ℓ) (A' := A') (α₁ := 0)
      (β₁ := 0) (κ := 0) h hBd hy₀ hy₀in (by norm_num) hOo hy₀O (fun z hz => ⟨hz.1.1, hz.1.1⟩)
      hOpos (by rw [hA'app, sub_self]) (fun z _ _ => by
        rw [hA'app]
        simp only [kinkOffset, kinkHeight, zero_mul, add_zero]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring)
      (fun h0 ht0 => by
        have hAℓ : ∀ z, (A z).2.2 = ℓ z := by
          rcases hside with ⟨ht', -⟩ | ⟨-, hz, -⟩
          · exfalso
            linarith
          · exact hz
        refine ⟨fun z => ?_, fun z _ => ?_⟩
        · rw [hA'app, Prod.snd_sub, Prod.snd_sub, ht0, sub_zero, hAℓ]
        · rw [hA'app, Prod.snd_sub, Prod.snd_sub, ht0, sub_zero])
  have hloc : ∀ x, f x ∈ chartBlock ec A' r₁ tlo₁ → dist (A (ec (f x))) (A (ec y₀)) < ρ :=
    fun x hx => (hsubO hx).1.2
  have hdistA : ∀ x, dist (A (ec (f x))) (A (ec y₀)) < ρ →
      dist (blockSheetProjA ec A f x) (blockSheetProjA ec A f xA) < ρA := by
    intro x hx
    have h1 : dist (blockSheetProjA ec A f x) (blockSheetProjA ec A f xA) ≤
        dist (A (ec (f x))) (A (ec y₀)) := by
      change dist ((A (ec (f x))).2.1, (A (ec (f x))).2.2)
        ((A (ec (f xA))).2.1, (A (ec (f xA))).2.2) ≤ _
      rw [hfxA', Prod.mk.eta, Prod.mk.eta, Prod.dist_eq (x := A (ec (f x)))]
      exact le_max_right _ _
    exact h1.trans_lt (hx.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hdistB : ∀ x, dist (A (ec (f x))) (A (ec y₀)) < ρ →
      dist (blockSheetProjB ec A f x) (blockSheetProjB ec A f xB) < ρB := by
    intro x hx
    have h1 : dist (blockSheetProjB ec A f x) (blockSheetProjB ec A f xB) ≤
        dist (A (ec (f x))) (A (ec y₀)) := by
      change dist ((A (ec (f x))).1, (A (ec (f x))).2.2)
        ((A (ec (f xB))).1, (A (ec (f xB))).2.2) ≤ _
      rw [hfxB', Prod.dist_eq, Prod.dist_eq (x := A (ec (f x))),
        Prod.dist_eq (x := (A (ec (f x))).2)]
      exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))
    exact h1.trans_lt (hx.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  refine ⟨A', r₁, tlo₁, a₁, b₁, hr₁, hA'app, fun z hz => (hsubO hz).2, hB₁, ?_, ?_⟩
  · rcases hGA with hGA | hGA
    · exact Or.inl fun x hx => hGA (hρA' x hx.1 (hdistA x (hloc x hx.2)))
    · exact Or.inr fun x hx hxK =>
        Set.disjoint_left.mp hGA (hρA' x hx.1 (hdistA x (hloc x hx.2))) hxK
  · rcases hGB with hGB | hGB
    · exact Or.inl fun x hx => hGB (hρB' x hx.1 (hdistB x (hloc x hx.2)))
    · exact Or.inr fun x hx hxK =>
        Set.disjoint_left.mp hGB (hρB' x hx.1 (hdistB x (hloc x hx.2))) hxK

theorem IsStableCrossingBlock.exists_regional_perturbation_subset [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0) {y₀ : M}
    (hy₀ : y₀ ∈ doublePointSet f S) (hy₀in : y₀ ∈ innerChartBlock ec A r tlo)
    {Ω Kc : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω) (hKc : IsClosed Kc)
    (hKcΩ : Kc ⊆ Ω) {O₀ : Set M} (hO₀ : IsOpen O₀) (hy₀O₀ : y₀ ∈ O₀) :
    ∃ (A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r' tlo' : ℝ) (O : Set M),
      (∀ z, A' z = A z - A (ec y₀)) ∧ 0 < r' ∧ chartBlock ec A' r' tlo' ⊆ O₀ ∧
      ((tlo' = -r' ∧ Disjoint (chartBlock ec A' r' tlo') BdM) ∨
        (tlo' = 0 ∧ ∀ z, (A' z).2.2 = ℓ z)) ∧ IsOpen O ∧
      y₀ ∈ O ∧ O ⊆ ec.source ∧ (∀ z ∈ O, 0 ≤ ℓ (ec z) → z ∈ innerChartBlock ec A' r' tlo') ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ (g : EuclideanSpace ℝ (Fin 2) → M)
          (δ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (lam : NNReal),
          (lam : ℝ) ≤ lam₀ → IsPiecewiseAffineOn δ univ → LipschitzWith lam δ →
          (∀ x ∈ S, g x ∈ ec.source → f x ∈ ec.source ∧ ‖ec (g x) - ec (f x)‖ ≤ ε₀) →
          (∀ x ∈ S, f x ∈ ec.source → 0 ≤ ℓ (ec (f x))) →
          (∀ x ∈ S, x ∈ Ω → g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ x) →
          (∀ x ∈ S, x ∉ Kc → g x = f x) →
          (∀ x ∈ S, g x ∈ ec.source →
            0 ≤ ℓ (ec (g x)) ∧ (x ∈ frontier S ↔ ℓ (ec (g x)) = 0)) →
          ∃ (SA' SB' : Set (EuclideanSpace ℝ (Fin 2))) (a' b' : ℝ × ℝ → ℝ) (La' Lb' : ℝ),
            IsStableCrossingBlock g S ec ℓ BdM A' r' tlo' SA' SB' a' b' La' Lb' (η / 2) := by
  obtain ⟨hr, -, -, -, -, -, -, hside, hpre, -, -, -, -, -, -, -, -, -, -, -⟩ := id h
  have htlo : tlo = -r ∨ tlo = 0 := hside.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by rcases htlo with ht | ht <;> linarith
  have hy₀s : y₀ ∈ ec.source := (chartBlock_mono_of_half ec A hr.le htle hy₀in).1
  obtain ⟨A', r₁, tlo₁, a₁, b₁, hr₁, hA'app, hsub₁, hB₁, hlocA, hlocB⟩ :=
    h.exists_recentre_localized_subset hBd hy₀ hy₀in hΩ hKc hKcΩ hO₀ hy₀O₀
  have hA'0 : A' (ec y₀) = 0 := by rw [hA'app, sub_self]
  obtain ⟨r', hr', hr'le, hinner, ε₀, hε₀, lam₀, hlam₀, hmain⟩ :=
    hB₁.exists_perturbation hy₀ hy₀s hA'0
  have hAℓ : tlo₁ = 0 → ∀ z, (A' z).2.2 = ℓ z := by
    intro h0
    obtain ⟨hr₁', -, -, -, -, -, -, hside₁, -⟩ := hB₁
    rcases hside₁ with ⟨ht, -⟩ | ⟨-, hz, -⟩
    · exfalso
      linarith
    · exact hz
  have hside₁ : (tlo₁ = -r₁ ∧ Disjoint (chartBlock ec A' r₁ tlo₁) BdM) ∨ tlo₁ = 0 := by
    obtain ⟨-, -, -, -, -, -, -, hs, -⟩ := hB₁
    exact hs.imp id fun h => h.1
  have he : r₁ * (r' / r₁) = r' := by field_simp
  have hle : tlo₁ ≤ tlo₁ * (r' / r₁) := by
    rcases hside₁ with ⟨ht, -⟩ | ht
    · rw [ht, neg_mul, he]
      linarith
    · rw [ht, zero_mul]
  have hbox : chartBlock ec A' r' (tlo₁ * (r' / r₁)) ⊆ chartBlock ec A' r₁ tlo₁ :=
    fun z hz => ⟨hz.1, blockBox_mono hr'le hle hz.2⟩
  have hside' : (tlo₁ * (r' / r₁) = -r' ∧
      Disjoint (chartBlock ec A' r' (tlo₁ * (r' / r₁))) BdM) ∨
      (tlo₁ * (r' / r₁) = 0 ∧ ∀ z, (A' z).2.2 = ℓ z) := by
    rcases hside₁ with ⟨ht, hdis⟩ | ht
    · exact Or.inl ⟨by rw [ht, neg_mul, he], hdis.mono_left hbox⟩
    · exact Or.inr ⟨by rw [ht, zero_mul], hAℓ ht⟩
  have hA'c : Continuous A' := A'.toAffineMap.continuous_of_finiteDimensional
  have hSAS : ∀ x ∈ SA, x ∈ S := fun x hx => by
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inl hx
    exact h1.1
  have hSBS : ∀ x ∈ SB, x ∈ S := fun x hx => by
    have h1 : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by
      rw [hpre]
      exact Or.inr hx
    exact h1.1
  refine ⟨A', r', tlo₁ * (r' / r₁), ec.source ∩ ⇑ec ⁻¹' (⇑A' ⁻¹' ball 0 (r' / 2)), hA'app, hr',
    hbox.trans hsub₁, hside', ec.isOpen_inter_preimage (isOpen_ball.preimage hA'c), ⟨hy₀s, ?_⟩,
    inter_subset_left, ?_,
    ε₀, hε₀, lam₀, hlam₀, ?_⟩
  · change A' (ec y₀) ∈ ball 0 (r' / 2)
    rw [hA'0]
    exact mem_ball_self (half_pos hr')
  · intro z hz hz0
    refine hinner z hz.1 (mem_ball_zero_iff.mp hz.2) fun h0 => ?_
    rw [hAℓ h0]
    exact hz0
  intro g δ lam hlam hδ hδL hclose hfC hgΩ hgK hg4
  have hsel : ∀ T₁ : Set (EuclideanSpace ℝ (Fin 2)),
      ((∀ x ∈ T₁, x ∈ Ω) ∨ ∀ x ∈ T₁, x ∉ Kc) → (∀ x ∈ T₁, x ∈ S ∧ f x ∈ ec.source) →
      ∃ δ₁ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3),
        IsPiecewiseAffineOn δ₁ univ ∧ LipschitzWith lam δ₁ ∧
          ∀ x ∈ T₁, g x ∈ ec.source ∧ ec (g x) = ec (f x) + δ₁ x := by
    intro T₁ hT₁ hT₁S
    rcases hT₁ with hΩ₁ | hK₁
    · exact ⟨δ, hδ, hδL, fun x hx => hgΩ x (hT₁S x hx).1 (hΩ₁ x hx)⟩
    · refine ⟨fun _ => 0, isPiecewiseAffineOn_of_affine
        (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) (0 : EuclideanSpace ℝ (Fin 3)))
        isOpen_univ, (LipschitzWith.const (0 : EuclideanSpace ℝ (Fin 3))).weaken zero_le,
        fun x hx => ?_⟩
      rw [hgK x (hT₁S x hx).1 (hK₁ x hx), add_zero]
      exact ⟨(hT₁S x hx).2, rfl⟩
  obtain ⟨δA, hδA, hδAL, hGA⟩ := hsel _ hlocA fun x hx => ⟨hSAS x hx.1, hx.2.1⟩
  obtain ⟨δB, hδB, hδBL, hGB⟩ := hsel _ hlocB fun x hx => ⟨hSBS x hx.1, hx.2.1⟩
  obtain ⟨a', b', La', Lb', hblk⟩ := hmain g δA δB lam hlam hδA hδAL hδB hδBL
    (fun x hx hxN => hclose x hx hxN.1) (fun _ => hfC) hGA hGB
    (fun _ x hx => by
      rcases hx with hx | hx
      · exact hg4 x (hSAS x hx.1) (hGA x hx).1
      · exact hg4 x (hSBS x hx.1) (hGB x hx).1)
  exact ⟨_, _, a', b', La', Lb', hblk⟩

end Ambient

section ChartedAmbient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem WallProductBlock.of_subset_ball [CompactSpace M] {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') {i : ι}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo r' tlo' : ℝ}
    {SA SB SA' SB' : Set (EuclideanSpace ℝ (Fin 2))} {a b a' b' : ℝ × ℝ → ℝ}
    {La Lb η La' Lb' η' : ℝ} {y : M}
    (h : WallProductBlock f S (ec i) (ℓ i) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (h' : IsStableCrossingBlock g S (ec i) (ℓ i) BdM A r' tlo' SA' SB' a' b' La' Lb' η')
    (hys : y ∈ (ec i).source) (hA0 : A (ec i y) = 0) (hyC : y ∈ C)
    (hball : chartBlock (ec i) A r' tlo' ⊆ (ec i).source ∩ ⇑(ec i) ⁻¹' (⇑A ⁻¹' ball 0 r)) :
    WallProductBlock g S (ec i) (ℓ i) BdM C Q ρ A r' tlo' SA' SB' a' b' La' Lb' η' := by
  classical
  obtain ⟨hstab, hskel, htype⟩ := h
  obtain ⟨hr', -, -, -, -, -, -, hside', -⟩ := id h'
  have hside'' : (tlo' = -r' ∧ Disjoint (chartBlock (ec i) A r' tlo') BdM) ∨
      (tlo' = 0 ∧ ∀ z, (A z).2.2 = ℓ i z) := hside'.imp id fun h => ⟨h.1, h.2.1⟩
  obtain ⟨hfull, hhalf, hsub⟩ :=
    hstab.chartBlock_subset_of_subset_ball (hsys.chartBd i) hr' hside'' hys hA0 hball
  have htl2 : tlo' = -r' ∨ tlo' = 0 := hside''.imp (fun h => h.1) fun h => h.1
  have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  set U : Set M := (ec i).source ∩ ⇑(ec i) ⁻¹' (⇑A ⁻¹' ball 0 r') with hUdef
  have hyU : y ∈ U := by
    refine ⟨hys, ?_⟩
    change A (ec i y) ∈ ball 0 r'
    rw [hA0]
    exact mem_ball_self hr'
  have hU : U ∈ 𝓝 y := ((ec i).isOpen_inter_preimage (isOpen_ball.preimage hAc)).mem_nhds hyU
  have hUsub : ∀ z ∈ U, (tlo' = 0 → 0 ≤ (A (ec i z)).2.2) → z ∈ chartBlock (ec i) A r' tlo' :=
    fun z hz hz0 => mem_chartBlock_of_norm_lt hz.1 (mem_ball_zero_iff.mp hz.2) htl2 hz0
  have hyB' : y ∈ chartBlock (ec i) A r' tlo' := hUsub y hyU fun _ => by
    rw [hA0]
    exact le_rfl
  refine ⟨h', hskel.mono_left hsub, ?_⟩
  rcases htype with ⟨c, hc, htl, hcsub⟩ | ⟨w, hw, cm, hcm, cp, hcp, htl, hne, hwm, hwp, hcov,
      -, -, hwalls, hzero, hsm, hsp⟩ | ⟨c, hc, w, hw, htl, hwc, hAℓ, hCsub, hne, hBdsub, hwalls⟩
  · exact Or.inl ⟨c, hc, hfull htl, hsub.trans hcsub⟩
  · have htl' := hfull htl
    have hyw : y ∈ wallSystemCell ρ w := (hzero y (hsub hyB')).mpr (by rw [hA0]; rfl)
    have hUB : U ⊆ chartBlock (ec i) A r' tlo' := fun z hz => hUsub z hz fun h0 => by
      exfalso
      rw [htl'] at h0
      linarith
    have hmeet : ∀ c ∈ wallSystemCells Q, w ⊆ c →
        (chartBlock (ec i) A r' tlo' ∩ wallSystemCellInt ρ c).Nonempty := by
      intro c hc hwc
      obtain ⟨z, hzU, hz⟩ := exists_mem_wallSystemCellInt_of_mem_nhds hsys.continuous
        hsys.injective hsys.rangeEq hc (convexHull_mono (Finset.coe_subset.2 hwc) hyw) hU
      exact ⟨z, hUB hzU, hz⟩
    exact Or.inr (Or.inl ⟨w, hw, cm, hcm, cp, hcp, htl', hne, hwm, hwp, hsub.trans hcov,
      hmeet cm hcm hwm, hmeet cp hcp hwp,
      fun w' hw' => (inter_subset_inter_left _ hsub).trans (hwalls w' hw'),
      fun x hx => hzero x (hsub hx), fun x hx => hsm x ⟨hsub hx.1, hx.2⟩,
      fun x hx => hsp x ⟨hsub hx.1, hx.2⟩⟩)
  · have htl' := hhalf htl
    have hcCf : c ∈ Cf := by
      obtain ⟨z₀, hz₀B, hz₀c⟩ := hne
      have hz₀C : z₀ ∈ C := by
        rw [hsys.chartC i z₀ hz₀B.1, ← hAℓ]
        have h3 : tlo ≤ (A (ec i z₀)).2.2 := hz₀B.2.2.2.1
        rw [htl] at h3
        exact h3
      rw [hsys.eqC] at hz₀C
      obtain ⟨c', hc', hz₀c'⟩ := mem_iUnion₂.mp hz₀C
      by_cases hcc : c = c'
      · rw [hcc]
        exact hc'
      · exact absurd hz₀c' (Set.disjoint_left.mp
          (disjoint_wallSystemCellInt_wallSystemCell hc (hsys.facesC hc') hcc) hz₀c)
    have hcC : wallSystemCell ρ c ⊆ C := by
      rw [hsys.eqC]
      exact subset_biUnion_of_mem (u := fun c => wallSystemCell ρ c) hcCf
    have hyc : y ∈ wallSystemCell ρ c := hCsub ⟨hsub hyB', hyC⟩
    have hne' : (chartBlock (ec i) A r' tlo' ∩ wallSystemCellInt ρ c).Nonempty := by
      obtain ⟨z, hzU, hz⟩ := exists_mem_wallSystemCellInt_of_mem_nhds hsys.continuous
        hsys.injective hsys.rangeEq hc hyc hU
      refine ⟨z, hUsub z hzU fun _ => ?_, hz⟩
      rw [hAℓ]
      exact (hsys.chartC i z hzU.1).mp (hcC (wallSystemCellInt_subset_wallSystemCell ρ c hz))
    exact Or.inr (Or.inr ⟨c, hc, w, hw, htl', hwc, hAℓ,
      (inter_subset_inter_left _ hsub).trans hCsub, hne',
      (inter_subset_inter_left _ hsub).trans hBdsub,
      fun w' hw' => (inter_subset_inter_left _ hsub).trans (hwalls w' hw')⟩)

end ChartedAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
