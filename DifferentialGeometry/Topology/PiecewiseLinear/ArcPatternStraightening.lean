/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternStraighteningBase
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternStraighteningStep

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcPatternStraightening {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    {S D : Set A} {Z : ι → Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγS : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ S) (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    (hlocal : ∀ r ∈ Icc (0 : ℝ) 1,
      ∃ (ψ : (ℝ × ℝ) × ℝ → A) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A),
        IsOpen V ∧ IsOpen Ω ∧ IsPLHomeomorphOn ψ V (S ∩ Ω) ∧ γ r ∈ Ω ∧
        (∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) ∧
        ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0) :
    ∃ (Φ : (ℝ × ℝ) × ℝ → A) (N : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A) (τ : ℝ),
      IsOpen N ∧ IsOpen Ω ∧ IsPLHomeomorphOn Φ N (S ∩ Ω) ∧ 0 < τ ∧
      coreSegment τ ⊆ N ∧ Φ '' coreSegment τ = γ '' Icc 0 1 ∧
      Φ 0 = γ 0 ∧ Φ ((0, 0), τ) = γ 1 ∧
      (∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i)) ∧
      ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 := by
  classical
  obtain ⟨ψ₀, V₀, Ω₀, hV₀, hΩ₀, hψ₀, hγ0Ω₀, hZ₀, hD₀⟩ :=
    hlocal 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨Φ₀, N₀, s₀, τ₀, hN₀, hΦ₀, hs₀, hs₀1, hτ₀, hcore₀, hcoreimg₀, hstart₀,
    htip₀, hZ₀, hD₀⟩ := exists_arcPatternStraightening_base P hγc hγi hγS hγD
      hV₀ hΩ₀ hψ₀ hγ0Ω₀ hZ₀ hD₀
  have hint : ∀ r : Icc s₀ (1 : ℝ),
      ∃ (ψ : (ℝ × ℝ) × ℝ → A) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A),
        IsOpen V ∧ IsOpen Ω ∧ IsPLHomeomorphOn ψ V (S ∩ Ω) ∧ γ r ∈ Ω ∧
        (∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) ∧
        ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0 :=
    fun r => hlocal r ⟨hs₀.le.trans r.2.1, r.2.2⟩
  choose ψf Vf Ωf hVf hΩf hψf hγf hZf hDf using hint
  have hU : ∀ r : Icc s₀ (1 : ℝ), ∃ U : Set ℝ, IsOpen U ∧ γ ⁻¹' Ωf r ∩ Icc 0 1 = U ∩ Icc 0 1 :=
    fun r => continuousOn_iff'.mp hγc (Ωf r) (hΩf r)
  choose U hUo hUeq using hU
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := s₀) (b := (1 : ℝ)))
    hUo (fun x hx => by
      refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hs₀.le.trans hx.1, hx.2.trans le_rfl⟩
      have h : x ∈ γ ⁻¹' Ωf ⟨x, hx⟩ ∩ Icc 0 1 := ⟨hγf ⟨x, hx⟩, hx01⟩
      rw [hUeq] at h
      exact h.1)
  have hchain : ∀ n : ℕ, ∃ (Φ : (ℝ × ℝ) × ℝ → A) (N : Set ((ℝ × ℝ) × ℝ)) (Ω : Set A)
      (τ : ℝ), IsOpen N ∧ IsOpen Ω ∧ IsPLHomeomorphOn Φ N (S ∩ Ω) ∧ 0 < τ ∧
        coreSegment τ ⊆ N ∧ Φ '' coreSegment τ = γ '' Icc 0 (min (s₀ + n * (δ / 2)) (1 : ℝ)) ∧
        Φ 0 = γ 0 ∧ Φ ((0, 0), τ) = γ (min (s₀ + n * (δ / 2)) (1 : ℝ)) ∧
        (∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i)) ∧
        ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 := by
    intro n
    induction n with
    | zero =>
      have h0 : min (s₀ + ((0 : ℕ) : ℝ) * (δ / 2)) (1 : ℝ) = s₀ := by
        rw [Nat.cast_zero, zero_mul, add_zero, min_eq_left hs₀1.le]
      rw [h0]
      exact ⟨Φ₀, N₀, Ω₀, τ₀, hN₀, hΩ₀, hΦ₀, hτ₀, hcore₀, hcoreimg₀, hstart₀, htip₀, hZ₀, hD₀⟩
    | succ n ih =>
      obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hstart, htip, hZ, hD⟩ := ih
      set a := s₀ + (n : ℝ) * (δ / 2) with hadef
      have ha' : s₀ + ((n + 1 : ℕ) : ℝ) * (δ / 2) = a + δ / 2 := by
        rw [hadef]
        push_cast
        ring
      rw [ha']
      set s := min a (1 : ℝ) with hsdef
      set s' := min (a + δ / 2) (1 : ℝ) with hs'def
      have hs₀a : s₀ ≤ a := by
        rw [hadef]
        have : (0 : ℝ) ≤ n * (δ / 2) := by positivity
        linarith
      have hss' : s ≤ s' := min_le_min_right _ (by linarith)
      rcases hss'.lt_or_eq with hlt | heq
      · have hsmem : s ∈ Icc s₀ (1 : ℝ) := ⟨le_min hs₀a hs₀1.le, min_le_right _ _⟩
        obtain ⟨r, hr⟩ := hleb s hsmem
        have hdiff : s' - s ≤ δ / 2 := by
          rcases le_total a (1 : ℝ) with h | h
          · rw [hsdef, min_eq_left h]
            linarith [min_le_left (a + δ / 2) (1 : ℝ)]
          · rw [hsdef, min_eq_right h]
            linarith [min_le_right (a + δ / 2) (1 : ℝ)]
        have hs'1 : s' ≤ 1 := (min_le_right _ _).trans le_rfl
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
        obtain ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hττ', hcore', hcoreimg', htip', hZ',
          hD', hfix⟩ := exists_arcPatternStraightening_step P hP hγc hγi hγD hN hΩ hΦ
            hτ hs0 hcore hcoreimg htip hZ hD (hVf r) (hΩf r) (hψf r) (hZf r) (hDf r)
            hlt hs'1 hcov
        have hstart' : Φ' 0 = γ 0 :=
          (hfix 0 (hcore' ⟨rfl, le_rfl, (hτ.trans hττ').le⟩) hτ).trans hstart
        exact ⟨Φ', N', Ω', τ', hN', hΩ', hΦ', hτ.trans hττ', hcore', hcoreimg', hstart',
          htip', hZ', hD'⟩
      · rw [← heq]
        exact ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hstart, htip, hZ, hD⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (((1 : ℝ) - s₀) / (δ / 2))
  obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hstart, htip, hZ, hD⟩ := hchain n
  have hmin : min (s₀ + n * (δ / 2)) (1 : ℝ) = (1 : ℝ) := by
    apply min_eq_right
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  rw [hmin] at hcoreimg htip
  exact ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hstart, htip, hZ, hD⟩

end DifferentialGeometry.Topology.PiecewiseLinear
