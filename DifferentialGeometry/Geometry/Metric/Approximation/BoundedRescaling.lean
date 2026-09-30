import DifferentialGeometry.Geometry.Metric.Approximation.FixedTargetTransfer

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace GC.MetricGeometry

universe u v w z

theorem exists_uniform_bounded_rescaling
    {P : ℕ → Type u} {X : ∀ i, P i → Type v}
    [mX : ∀ i a, MetricSpace (X i a)] (p : ∀ i a, X i a)
    {ι : Type w} {Y C : ι → Type z} [mY : ∀ b, MetricSpace (Y b)]
    [mC : ∀ b, MetricSpace (C b)] (q : ∀ b, Y b) (o : ∀ b, C b)
    (hextract : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, P (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        PointedGHConverges (fun j => p (a (k j)) (z (k j))) (q b))
    (hlimit : ∀ b : ι, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox (Y b) (C b)
          ((mY b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b) (q b) (o b) ε))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ N : ℕ, ∀ i ≥ N, ∀ a : P i,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧ ∃ b : ι,
        Nonempty (@KleinerLottApprox (X i a) (C b)
          ((mX i a).rescale s⁻¹ (inv_pos.mpr hs)) (mC b) (p i a) (o b) δ) := by
  classical
  by_contra! h
  have hbad (j : ℕ) : ∃ i ≥ j, ∃ a : P i,
      ∀ s : ℝ, ∀ hs : 0 < s, T ≤ s → s ≤ T + j → ∀ b : ι,
        ¬ Nonempty (@KleinerLottApprox (X i a) (C b)
          ((mX i a).rescale s⁻¹ (inv_pos.mpr hs)) (mC b) (p i a) (o b) δ) := by
    obtain ⟨i, hi, a, ha⟩ := h (T + j) (by linarith [Nat.cast_nonneg (α := ℝ) j]) j
    exact ⟨i, hi, a, fun s hs hTs hsj b =>
      not_nonempty_iff.mpr (ha s hs hTs hsj b)⟩
  choose a ha z hz using hbad
  have haTop : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  obtain ⟨b, k, hk, hconv⟩ := hextract a haTop z
  let ε := min (δ / 100) (1 / (2 * (2 * (δ⁻¹ + δ) + 4)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεone : ε < 1 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨R₀, hR₀⟩ := hlimit b ε hε hεone
  let R := max T R₀
  have hR : 0 < R := hT.trans_le (le_max_left _ _)
  obtain ⟨g⟩ := hR₀ R hR (le_max_right _ _)
  have hmaps := hconv.eventually_rescaled_approx_fixed_target R hR hδ hδone g
  have hbound : ∀ᶠ j : ℕ in atTop, R ≤ T + (k j : ℝ) := by
    have hkTop : Tendsto (fun j => (k j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop
    filter_upwards [hkTop.eventually (eventually_ge_atTop (R - T))] with j hj
    linarith
  obtain ⟨j, hj, hjbound⟩ := (hmaps.and hbound).exists
  exact hz (k j) R hR (le_max_left _ _) hjbound b hj

end GC.MetricGeometry
