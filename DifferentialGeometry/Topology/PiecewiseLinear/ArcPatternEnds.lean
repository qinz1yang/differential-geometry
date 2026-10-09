/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternEndFinal

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcPatternStraightening_with_ends {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    (H : Set (ℝ × ℝ)) (hH : ∀ v (t : ℝ), 0 < t → (t • v ∈ H ↔ v ∈ H))
    {S B D Bd : Set A} {Z : ι → Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγS : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ S) (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    (hγ1 : γ 1 ∈ Bd)
    {ψ₀ : (ℝ × ℝ) × ℝ → A} {V₀ : Set ((ℝ × ℝ) × ℝ)} {Ω₀ : Set A} (hV₀ : IsOpen V₀)
    (hΩ₀ : IsOpen Ω₀) (hψ₀ : IsPLHomeomorphOn ψ₀ V₀ (S ∩ Ω₀))
    (h0V₀ : (0 : (ℝ × ℝ) × ℝ) ∈ V₀) (hψ₀0 : ψ₀ 0 = γ 0)
    (hψ₀B : ∀ p ∈ V₀, ψ₀ p ∈ B ↔ p.1 ∈ H ∧ 0 ≤ p.2)
    (hψ₀D : ∀ p ∈ V₀, ψ₀ p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2)
    (hψ₀Z : ∀ i p, p ∈ V₀ → (ψ₀ p ∈ Z i ↔ p.1 ∈ P i))
    (hψ₀Bd : ∀ p ∈ V₀, ψ₀ p ∈ Bd ↔ p.1 ∈ H ∧ p.2 = 0)
    {ψ₁ : (ℝ × ℝ) × ℝ → A} {V₁ : Set ((ℝ × ℝ) × ℝ)} {Ω₁ : Set A} (hV₁ : IsOpen V₁)
    (hΩ₁ : IsOpen Ω₁) (hψ₁ : IsPLHomeomorphOn ψ₁ V₁ (S ∩ Ω₁)) (hγ1Ω₁ : γ 1 ∈ Ω₁)
    (hψ₁B : ∀ p ∈ V₁, ψ₁ p ∈ B ↔ p.1 ∈ H ∧ p.2 ≤ 0)
    (hψ₁D : ∀ p ∈ V₁, ψ₁ p ∈ D ↔ p.1 = 0 ∧ p.2 ≤ 0)
    (hψ₁Z : ∀ i p, p ∈ V₁ → (ψ₁ p ∈ Z i ↔ p.1 ∈ P i))
    (hψ₁Bd : ∀ p ∈ V₁, ψ₁ p ∈ Bd ↔ p.1 ∈ H ∧ p.2 = 0)
    (hint : ∀ r ∈ Ioo (0 : ℝ) 1, ∃ (ψ : (ℝ × ℝ) × ℝ → A) (V : Set ((ℝ × ℝ) × ℝ))
      (Ω : Set A), IsOpen V ∧ IsOpen Ω ∧ IsPLHomeomorphOn ψ V (S ∩ Ω) ∧ γ r ∈ Ω ∧
        (∀ p ∈ V, ψ p ∈ B ↔ p.1 ∈ H) ∧ (∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0) ∧
        (∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) ∧ ∀ p ∈ V, ψ p ∉ Bd) :
    ∃ (Φ : (ℝ × ℝ) × ℝ → A) (N : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A) (τ : ℝ),
      IsOpen N ∧ IsOpen Ω ∧ IsPLHomeomorphOn Φ N (S ∩ Ω) ∧ 0 < τ ∧ coreSegment τ ⊆ N ∧
      Φ '' coreSegment τ = γ '' Icc 0 1 ∧
      (∀ p ∈ N, Φ p ∈ B ↔ p.1 ∈ H ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) ∧
      (∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) ∧
      (∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i)) ∧
      (∀ p ∈ N, Φ p ∈ Bd ↔ p.1 ∈ H ∧ (p.2 = 0 ∨ p.2 = τ)) ∧
      Φ 0 = γ 0 ∧ Φ ((0, 0), τ) = γ 1 := by
  classical
  obtain ⟨s₀, τ₀, hs₀, hs₀1, hτ₀, hcore₀, hcoreimg₀, htip₀⟩ :=
    exists_arcStraightening_base hγc hγi hγS hγD hΩ₀ hψ₀ h0V₀ hψ₀0 hψ₀D
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨u₁, hu₁, hu₁eq⟩ := continuousOn_iff'.mp hγc Ω₁ hΩ₁
  have h1u₁ : (1 : ℝ) ∈ u₁ := by
    have h : (1 : ℝ) ∈ γ ⁻¹' Ω₁ ∩ Icc 0 1 := ⟨hγ1Ω₁, hmem1⟩
    rw [hu₁eq] at h
    exact h.1
  obtain ⟨δ₁, hδ₁, hδ₁u⟩ := Metric.isOpen_iff.mp hu₁ 1 h1u₁
  set sb := max s₀ (1 - δ₁ / 2) with hsbdef
  have hsb1 : sb < 1 := max_lt hs₀1 (by linarith)
  have hs₀sb : s₀ ≤ sb := le_max_left _ _
  have hcov₁ : γ '' Icc sb 1 ⊆ S ∩ Ω₁ := by
    rintro _ ⟨r, hr, rfl⟩
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hs₀.le.trans (hs₀sb.trans hr.1), hr.2⟩
    refine ⟨hγS r hr01, ?_⟩
    have hsbr : 1 - δ₁ / 2 ≤ r := (le_max_right _ _).trans hr.1
    have hru : r ∈ u₁ := hδ₁u (by
      rw [mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hr.2])]
      linarith)
    have h : r ∈ u₁ ∩ Icc 0 1 := ⟨hru, hr01⟩
    rw [← hu₁eq] at h
    exact h.1
  have hint' : ∀ r : Icc s₀ sb, ∃ (ψ : (ℝ × ℝ) × ℝ → A) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A),
      IsOpen V ∧ IsOpen Ω ∧ IsPLHomeomorphOn ψ V (S ∩ Ω) ∧ γ r ∈ Ω ∧
        (∀ p ∈ V, ψ p ∈ B ↔ p.1 ∈ H) ∧ (∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0) ∧
        (∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) ∧ ∀ p ∈ V, ψ p ∉ Bd := fun r =>
    hint r ⟨hs₀.trans_le r.2.1, r.2.2.trans_lt hsb1⟩
  choose ψf Vf Ωf hVf hΩf hψf hγf hBf hDf hZf hBdf using hint'
  have hU : ∀ r : Icc s₀ sb, ∃ U : Set ℝ, IsOpen U ∧ γ ⁻¹' Ωf r ∩ Icc 0 1 = U ∩ Icc 0 1 :=
    fun r => continuousOn_iff'.mp hγc (Ωf r) (hΩf r)
  choose U hUo hUeq using hU
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := s₀) (b := sb))
    hUo (fun x hx => by
      refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hs₀.le.trans hx.1, hx.2.trans hsb1.le⟩
      have h : x ∈ γ ⁻¹' Ωf ⟨x, hx⟩ ∩ Icc 0 1 := ⟨hγf ⟨x, hx⟩, hx01⟩
      rw [hUeq] at h
      exact h.1)
  have hchain : ∀ n : ℕ, ∃ (Φ : (ℝ × ℝ) × ℝ → A) (N : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A)
      (τ : ℝ), IsOpen N ∧ IsOpen Ω ∧ IsPLHomeomorphOn Φ N (S ∩ Ω) ∧ 0 < τ ∧
        coreSegment τ ⊆ N ∧ Φ '' coreSegment τ = γ '' Icc 0 (min (s₀ + n * (δ / 2)) sb) ∧
        Φ ((0, 0), τ) = γ (min (s₀ + n * (δ / 2)) sb) ∧
        (∀ p ∈ N, Φ p ∈ B ↔ p.1 ∈ H ∧ 0 ≤ p.2) ∧
        (∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2) ∧
        (∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i)) ∧
        (∀ p ∈ N, Φ p ∈ Bd ↔ p.1 ∈ H ∧ p.2 = 0) ∧ Φ 0 = γ 0 := by
    intro n
    induction n with
    | zero =>
      have h0 : min (s₀ + ((0 : ℕ) : ℝ) * (δ / 2)) sb = s₀ := by
        rw [Nat.cast_zero, zero_mul, add_zero, min_eq_left hs₀sb]
      rw [h0]
      exact ⟨ψ₀, V₀, Ω₀, τ₀, hV₀, hΩ₀, hψ₀, hτ₀, hcore₀, hcoreimg₀, htip₀, hψ₀B, hψ₀D,
        hψ₀Z, hψ₀Bd, hψ₀0⟩
    | succ n ih =>
      obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, htip, hB, hD, hZ, hBd, hstart⟩ := ih
      set a := s₀ + (n : ℝ) * (δ / 2) with hadef
      have ha' : s₀ + ((n + 1 : ℕ) : ℝ) * (δ / 2) = a + δ / 2 := by
        rw [hadef]
        push_cast
        ring
      rw [ha']
      set s := min a sb with hsdef
      set s' := min (a + δ / 2) sb with hs'def
      have hs₀a : s₀ ≤ a := by
        rw [hadef]
        have : (0 : ℝ) ≤ n * (δ / 2) := by positivity
        linarith
      have hss' : s ≤ s' := min_le_min_right _ (by linarith)
      rcases hss'.lt_or_eq with hlt | heq
      · have hsmem : s ∈ Icc s₀ sb := ⟨le_min hs₀a hs₀sb, min_le_right _ _⟩
        obtain ⟨r, hr⟩ := hleb s hsmem
        have hdiff : s' - s ≤ δ / 2 := by
          rcases le_total a sb with h | h
          · rw [hsdef, min_eq_left h]
            linarith [min_le_left (a + δ / 2) sb]
          · rw [hsdef, min_eq_right h]
            linarith [min_le_right (a + δ / 2) sb]
        have hs'1 : s' ≤ 1 := (min_le_right _ _).trans hsb1.le
        have hs0 : 0 ≤ s := hs₀.le.trans hsmem.1
        have hcov : γ '' Icc s s' ⊆ S ∩ Ωf r := by
          rintro _ ⟨r', hr', rfl⟩
          have hr'01 : r' ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hr'.1, hr'.2.trans hs'1⟩
          refine ⟨hγS r' hr'01, ?_⟩
          have hr'U : r' ∈ U r := hr (by
            rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hr'.1])]
            linarith [hr'.2])
          have h : r' ∈ U r ∩ Icc 0 1 := ⟨hr'U, hr'01⟩
          rw [← hUeq] at h
          exact h.1
        obtain ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hττ', hcore', hcoreimg', htip', hB', hD', hZ',
          hBd', hfix⟩ := exists_arcPatternStraightening_end_step P hP H hH hγc hγi hγD hN hΩ hΦ
            hτ hs0 hcore hcoreimg
            htip hB hD hZ hBd (hVf r) (hΩf r) (hψf r) (hBf r) (hDf r) (hZf r) (hBdf r) hlt hs'1
            hcov
        exact ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hτ.trans hττ', hcore', hcoreimg', htip', hB',
          hD', hZ', hBd',
          (hfix 0 (hcore' ⟨rfl, le_rfl, (hτ.trans hττ').le⟩) hτ).trans hstart⟩
      · rw [← heq]
        exact ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, htip, hB, hD, hZ, hBd, hstart⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((sb - s₀) / (δ / 2))
  obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, htip, hB, hD, hZ, hBd, hstart⟩ := hchain n
  have hmin : min (s₀ + n * (δ / 2)) sb = sb := by
    apply min_eq_right
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  rw [hmin] at hcoreimg htip
  obtain ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hτ', hcore', hcoreimg', hB', hD', hZ', hBd',
    hstart', htip'⟩ := exists_arcPatternStraightening_final P hP H hH hγc hγi hγD hγ1 hN hΩ hΦ hτ
    (hs₀.le.trans hs₀sb) hsb1
    hcore hcoreimg htip hB hD hZ hBd hV₁ hΩ₁ hψ₁ hψ₁B hψ₁D hψ₁Z hψ₁Bd hcov₁
  exact ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hτ', hcore', hcoreimg', hB', hD', hZ', hBd',
    hstart'.trans hstart, htip'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
