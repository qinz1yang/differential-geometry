import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Beta
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Quasilinear.Flux

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure HarmonicMapFlowCoefficients (eps K : ℝ)
    (A : ℝ × V → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F) : Prop where
  eps0 : 0 ≤ eps
  K0 : 0 ≤ K
  principal : ∀ z, ‖A z‖ ≤ eps
  quadratic : ∀ z, ‖Q z‖ ≤ K

structure HarmonicMapFlowSourceSplitting (T Ap As : ℝ) (Cp Cs : ℝ≥0∞)
    (p s : ℝ × V → F) : Prop where
  principalWt : GradientWeightedBound T Ap p
  principalCarleson : GradientCarlesonBound T Cp p
  sourceWt : SourceWeightedBound T As s
  sourceCarleson : SourceCarlesonBound T Cs s

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem harmonicMapFlowPrincipalWeightedBound {eps K T C : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    {d : ℝ × V → G}
    (h : HarmonicMapFlowCoefficients eps K A Q) (hd : GradientWeightedBound T C d) :
    GradientWeightedBound T (eps * C) (fun z ↦ A z (d z)) :=
  linear_weighted_bound A h.principal h.eps0 hd

theorem harmonicMapFlowPrincipalCarlesonBound {eps K T : ℝ} {C : ℝ≥0∞}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    {d : ℝ × V → G}
    (h : HarmonicMapFlowCoefficients eps K A Q)
    (hae : AEStronglyMeasurable (fun z ↦ A z (d z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hd : GradientCarlesonBound T C d) :
    GradientCarlesonBound T (ENNReal.ofReal (eps ^ 2) * C) (fun z ↦ A z (d z)) :=
  linear_carleson_bound A h.principal h.eps0 hae hd

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem harmonicMapFlowCriticalTimeIntegralBound {eps K C t : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowCoefficients eps K A Q) (hC : 0 ≤ C) (ht : 0 < t) :
    (∫ s : ℝ in 0..t, (eps * C) * criticalTimeKernel t s) ≤ 4 * (eps * C) :=
  criticalTimeKernel_const_mul_integral_le ht (mul_nonneg h.eps0 hC)

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem quadratic_difference_weighted_bound {K T A₁ A₂ AΔ : ℝ}
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (hK : ∀ z, ‖Q z‖ ≤ K) (hK0 : 0 ≤ K)
    (hA₂0 : 0 ≤ A₂) (hAΔ0 : 0 ≤ AΔ)
    {d₁ d₂ : ℝ × V → G}
    (hd₁ : GradientWeightedBound T A₁ d₁) (hd₂ : GradientWeightedBound T A₂ d₂)
    (hdΔ : GradientWeightedBound T AΔ (fun z ↦ d₁ z - d₂ z)) :
    SourceWeightedBound T (K * AΔ * A₁ + K * A₂ * AΔ)
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  have h₁ := bilinear_weighted_bound_of_norm_bound Q hK hK0 hAΔ0 hdΔ hd₁
  have h₂ := bilinear_weighted_bound_of_norm_bound Q hK hK0 hA₂0 hd₂ hdΔ
  have hadd := SourceWeightedBound.add h₁ h₂
  have hsplit :
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) =
        (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z) +
          Q z (d₂ z) (d₁ z - d₂ z)) := by
    funext z
    simp only [map_sub, sub_apply]
    abel
  rw [hsplit]
  exact hadd

theorem quadratic_difference_carleson_bound {K T : ℝ} {C₁ C₂ CΔ : ℝ≥0∞}
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (hK : ∀ z, ‖Q z‖ ≤ K) (hK0 : 0 ≤ K)
    {d₁ d₂ : ℝ × V → G}
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (d₂ z) (d₁ z - d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hd₁ : GradientCarlesonBound T C₁ d₁) (hd₂ : GradientCarlesonBound T C₂ d₂)
    (hdΔ : GradientCarlesonBound T CΔ (fun z ↦ d₁ z - d₂ z)) :
    SourceCarlesonBound T
      (ENNReal.ofReal K * (CΔ + C₁) + ENNReal.ofReal K * (C₂ + CΔ))
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  have h₁ := bilinear_carleson_bound_of_norm_bound Q hK hK0 hae₁ hdΔ hd₁
  have h₂ := bilinear_carleson_bound_of_norm_bound Q hK hK0 hae₂ hd₂ hdΔ
  have hadd := SourceCarlesonBound.add h₁ h₂
  have hsplit :
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) =
        (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z) +
          Q z (d₂ z) (d₁ z - d₂ z)) := by
    funext z
    simp only [map_sub, sub_apply]
    abel
  rw [hsplit]
  exact hadd

theorem harmonicMapFlowDiffSplit {eps K T A₁ A₂ AΔ : ℝ}
    {C₁ C₂ CΔ : ℝ≥0∞}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowCoefficients eps K A Q)
    (hA₂0 : 0 ≤ A₂) (hAΔ0 : 0 ≤ AΔ)
    {d₁ d₂ : ℝ × V → G}
    (haep : AEStronglyMeasurable (fun z ↦ A z (d₁ z - d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (d₂ z) (d₁ z - d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hw₁ : GradientWeightedBound T A₁ d₁) (hw₂ : GradientWeightedBound T A₂ d₂)
    (hwΔ : GradientWeightedBound T AΔ (fun z ↦ d₁ z - d₂ z))
    (hc₁ : GradientCarlesonBound T C₁ d₁) (hc₂ : GradientCarlesonBound T C₂ d₂)
    (hcΔ : GradientCarlesonBound T CΔ (fun z ↦ d₁ z - d₂ z)) :
    HarmonicMapFlowSourceSplitting T (eps * AΔ)
      (K * AΔ * A₁ + K * A₂ * AΔ)
      (ENNReal.ofReal (eps ^ 2) * CΔ)
      (ENNReal.ofReal K * (CΔ + C₁) + ENNReal.ofReal K * (C₂ + CΔ))
      (fun z ↦ A z (d₁ z - d₂ z))
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  exact ⟨
    linear_weighted_bound A h.principal h.eps0 hwΔ,
    linear_carleson_bound A h.principal h.eps0 haep hcΔ,
    quadratic_difference_weighted_bound Q h.quadratic h.K0 hA₂0 hAΔ0 hw₁ hw₂ hwΔ,
    quadratic_difference_carleson_bound Q h.quadratic h.K0 hae₁ hae₂ hc₁ hc₂ hcΔ⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
