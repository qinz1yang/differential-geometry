import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import DifferentialGeometry.Geometry.Metric.Pullback.Retraction

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Retraction

variable [T3Space M]

theorem diskMapEnergyDensity_ae_eq_pullback_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) :
    diskMapEnergyDensity g u =ᵐ[volume] fun z =>
      (pullbackMetricCoefficients g r (Φ (u z))
          (fderiv ℝ (Φ ∘ u) z 1) (fderiv ℝ (Φ ∘ u) z 1) +
        pullbackMetricCoefficients g r (Φ (u z))
          (fderiv ℝ (Φ ∘ u) z Complex.I) (fderiv ℝ (Φ ∘ u) z Complex.I)) / 2 := by
  filter_upwards [ae_mdifferentiableAt_of_riemannian_lipschitz g hu] with z hz
  have hΦz : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (u z) :=
    hΦ.mdifferentiableAt one_ne_zero
  have hrz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (Φ (u z)) :=
    ((hr (Φ (u z)) (hΦN (mem_range_self (u z)))).contMDiffAt
      (hN.mem_nhds (hΦN (mem_range_self (u z))))).mdifferentiableAt one_ne_zero
  rw [pullbackMetricCoefficients_comp_fderiv_of_leftInverse g hΦz hrz hleft hz,
    pullbackMetricCoefficients_comp_fderiv_of_leftInverse g hΦz hrz hleft hz]
  rfl

end Retraction

variable [T2Space M] [CompactSpace M] [CompleteSpace F]

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
      ∀ (S : Set ℂ), S ⊆ closedBall (0 : ℂ) 1 →
        IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S ∧
        IntegrableOn (diskMapEnergyDensity g (diskExtension u)) S ∧
        (∫ z in S, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 * ∫ z in S, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨C, hC, hpoint⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le g hΦ
  refine ⟨C, hC, fun u K hu => ?_⟩
  obtain ⟨hLip, hpointu⟩ := hpoint (diskExtension u) K (diskExtension_riemannian_lipschitz g hu)
  refine ⟨hLip, fun S hSD => ?_⟩
  have he : IntegrableOn (diskMapEnergyDensity g (diskExtension u)) S :=
    (integrable_diskMapEnergyDensity g hu).mono_set hSD
  have hi : IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S := by
    apply (he.const_mul (4 * (C : ℝ) ^ 2)).mono'
      ((measurable_fderiv ℝ (Φ ∘ diskExtension u)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (s := S) hpointu] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hi, he, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono_ae hi (he.const_mul (4 * (C : ℝ) ^ 2)) (ae_restrict_of_ae hpointu)

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
      ∀ (S : Set ℂ), S ⊆ closedBall (0 : ℂ) 1 →
        let e : ℂ → ℝ := fun z =>
          (pullbackMetricCoefficients g r (Φ (diskExtension u z))
              (fderiv ℝ (Φ ∘ diskExtension u) z 1) (fderiv ℝ (Φ ∘ diskExtension u) z 1) +
            pullbackMetricCoefficients g r (Φ (diskExtension u z))
              (fderiv ℝ (Φ ∘ diskExtension u) z Complex.I)
              (fderiv ℝ (Φ ∘ diskExtension u) z Complex.I)) / 2
        IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S ∧
        IntegrableOn e S ∧
        (∫ z in S, diskMapEnergyDensity g (diskExtension u) z) = (∫ z in S, e z) ∧
        (∫ z in S, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 * ∫ z in S, e z := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets g hΦ
  refine ⟨C, hC, fun u K hu => ⟨(hbound u K hu).1, fun S hSD => ?_⟩⟩
  obtain ⟨hi, he, hle⟩ := (hbound u K hu).2 S hSD
  have heq := ae_restrict_of_ae (s := S)
    (diskMapEnergyDensity_ae_eq_pullback_of_lipschitz g hΦ hN hr hΦN hleft
      (diskExtension_riemannian_lipschitz g hu))
  have hint := integral_congr_ae heq
  exact ⟨hi, he.congr heq, hint, hle.trans_eq (congrArg (fun x => 4 * (C : ℝ) ^ 2 * x) hint)⟩

end DifferentialGeometry.Geometry

end
