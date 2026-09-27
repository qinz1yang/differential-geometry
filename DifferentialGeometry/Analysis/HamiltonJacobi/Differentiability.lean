import DifferentialGeometry.Analysis.Viscosity.Differentiability
import DifferentialGeometry.Analysis.Calculus.Rademacher

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis.HamiltonJacobi

theorem le_zero_of_upper_tests_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : UpperSemicontinuousOn u Ω)
    {H : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    (hsub : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) y → H y (u y) (fderiv ℝ φ y) ≤ 0)
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (hH : LowerSemicontinuousAt (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2)
      (x, u x, fderiv ℝ u x)) :
    H x (u x) (fderiv ℝ u x) ≤ 0 := by
  by_contra hn
  have hpos : 0 < H x (u x) (fderiv ℝ u x) := lt_of_not_ge hn
  have hJ : ContinuousAt
      (fun q : E × (E →L[ℝ] ℝ) => (q.1, u q.1, q.2)) (x, fderiv ℝ u x) :=
    continuousAt_fst.prodMk ((hd.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
  have hn : ∀ᶠ q : E × (E →L[ℝ] ℝ) in 𝓝 (x, fderiv ℝ u x),
      0 < H q.1 (u q.1) q.2 := hJ (hH 0 hpos)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨y, hy, φ, hφ, hm, hp⟩ :=
    Viscosity.exists_smooth_upper_test_near_differentiable_point hΩ hu hx hd hr
  have hj : (y, fderiv ℝ φ y) ∈ Metric.ball (x, fderiv ℝ u x) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hy.1, by simpa only [dist_eq_norm] using hp⟩
  exact (not_lt_of_ge (hsub y hy.2 φ hφ hm)) (hball hj)

theorem nonneg_of_lower_tests_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : LowerSemicontinuousOn u Ω)
    {H : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    (hsuper : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMin (fun z => u z - φ z) y → 0 ≤ H y (u y) (fderiv ℝ φ y))
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (hH : UpperSemicontinuousAt (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2)
      (x, u x, fderiv ℝ u x)) :
    0 ≤ H x (u x) (fderiv ℝ u x) := by
  by_contra hn
  have hneg : H x (u x) (fderiv ℝ u x) < 0 := lt_of_not_ge hn
  have hJ : ContinuousAt
      (fun q : E × (E →L[ℝ] ℝ) => (q.1, u q.1, q.2)) (x, fderiv ℝ u x) :=
    continuousAt_fst.prodMk ((hd.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
  have hn : ∀ᶠ q : E × (E →L[ℝ] ℝ) in 𝓝 (x, fderiv ℝ u x),
      H q.1 (u q.1) q.2 < 0 := hJ (hH 0 hneg)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨y, hy, φ, hφ, hm, hp⟩ :=
    Viscosity.exists_smooth_lower_test_near_differentiable_point hΩ hu hx hd hr
  have hj : (y, fderiv ℝ φ y) ∈ Metric.ball (x, fderiv ℝ u x) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hy.1, by simpa only [dist_eq_norm] using hp⟩
  exact (not_lt_of_ge (hsuper y hy.2 φ hφ hm)) (hball hj)

theorem eq_zero_of_tests_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    {H : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    (hsub : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) y → H y (u y) (fderiv ℝ φ y) ≤ 0)
    (hsuper : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMin (fun z => u z - φ z) y → 0 ≤ H y (u y) (fderiv ℝ φ y))
    {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (hH : ContinuousAt (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2)
      (x, u x, fderiv ℝ u x)) :
    H x (u x) (fderiv ℝ u x) = 0 :=
  le_antisymm
    (le_zero_of_upper_tests_of_differentiableAt hΩ hu.upperSemicontinuousOn hsub hx hd
      hH.lowerSemicontinuousAt)
    (nonneg_of_lower_tests_of_differentiableAt hΩ hu.lowerSemicontinuousOn hsuper hx hd
      hH.upperSemicontinuousAt)

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → ℝ} {Ω : Set E} {H : E → ℝ → (E →L[ℝ] ℝ) → ℝ}

theorem ae_le_zero_of_upper_tests_of_locallyLipschitzOn
    (hΩ : IsOpen Ω) (hu : LocallyLipschitzOn Ω u)
    (hsub : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) y → H y (u y) (fderiv ℝ φ y) ≤ 0)
    (hH : LowerSemicontinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2)
      (Ω ×ˢ univ)) :
    ∀ᵐ x ∂μ.restrict Ω, H x (u x) (fderiv ℝ u x) ≤ 0 := by
  filter_upwards [hu.ae_differentiableAt hΩ, ae_restrict_mem hΩ.measurableSet] with x hd hx
  apply le_zero_of_upper_tests_of_differentiableAt hΩ hu.continuousOn.upperSemicontinuousOn hsub hx hd
  intro a ha
  have h := hH (x, u x, fderiv ℝ u x) ⟨hx, mem_univ _⟩ a ha
  rwa [(hΩ.prod isOpen_univ).nhdsWithin_eq ⟨hx, mem_univ _⟩] at h

theorem ae_nonneg_of_lower_tests_of_locallyLipschitzOn
    (hΩ : IsOpen Ω) (hu : LocallyLipschitzOn Ω u)
    (hsuper : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMin (fun z => u z - φ z) y → 0 ≤ H y (u y) (fderiv ℝ φ y))
    (hH : UpperSemicontinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2)
      (Ω ×ˢ univ)) :
    ∀ᵐ x ∂μ.restrict Ω, 0 ≤ H x (u x) (fderiv ℝ u x) := by
  filter_upwards [hu.ae_differentiableAt hΩ, ae_restrict_mem hΩ.measurableSet] with x hd hx
  apply nonneg_of_lower_tests_of_differentiableAt hΩ hu.continuousOn.lowerSemicontinuousOn hsuper hx hd
  intro a ha
  have h := hH (x, u x, fderiv ℝ u x) ⟨hx, mem_univ _⟩ a ha
  rwa [(hΩ.prod isOpen_univ).nhdsWithin_eq ⟨hx, mem_univ _⟩] at h

theorem ae_eq_zero_of_tests_of_locallyLipschitzOn
    (hΩ : IsOpen Ω) (hu : LocallyLipschitzOn Ω u)
    (hsub : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMax (fun z => u z - φ z) y → H y (u y) (fderiv ℝ φ y) ≤ 0)
    (hsuper : ∀ y ∈ Ω, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsLocalMin (fun z => u z - φ z) y → 0 ≤ H y (u y) (fderiv ℝ φ y))
    (hH : ContinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) => H q.1 q.2.1 q.2.2) (Ω ×ˢ univ)) :
    ∀ᵐ x ∂μ.restrict Ω, H x (u x) (fderiv ℝ u x) = 0 := by
  filter_upwards [ae_le_zero_of_upper_tests_of_locallyLipschitzOn hΩ hu hsub hH.lowerSemicontinuousOn,
    ae_nonneg_of_lower_tests_of_locallyLipschitzOn hΩ hu hsuper hH.upperSemicontinuousOn] with x hle hge
  exact le_antisymm hle hge

end

end DifferentialGeometry.Analysis.HamiltonJacobi
