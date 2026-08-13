import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelBeta
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuasilinearFlux

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

structure HmfCoeff (eps K : ℝ)
    (A : ℝ × V → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F) : Prop where
  eps0 : 0 ≤ eps
  K0 : 0 ≤ K
  principal : ∀ z, ‖A z‖ ≤ eps
  quadratic : ∀ z, ‖Q z‖ ≤ K

structure HmfSplit (T Ap As : ℝ) (Cp Cs : ℝ≥0∞)
    (p s : ℝ × V → F) : Prop where
  principalWt : GradWt T Ap p
  principalCarl : GradCarl T Cp p
  sourceWt : SrcWt T As s
  sourceCarl : SrcCarl T Cs s

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem hmfPrinWt {eps K T C : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    {d : ℝ × V → G}
    (h : HmfCoeff eps K A Q) (hd : GradWt T C d) :
    GradWt T (eps * C) (fun z ↦ A z (d z)) :=
  linWt_of_bound A h.principal h.eps0 hd

theorem hmfPrinCarl {eps K T : ℝ} {C : ℝ≥0∞}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    {d : ℝ × V → G}
    (h : HmfCoeff eps K A Q)
    (hae : AEStronglyMeasurable (fun z ↦ A z (d z))
      (stVolume : Measure (ℝ × V)))
    (hd : GradCarl T C d) :
    GradCarl T (ENNReal.ofReal (eps ^ 2) * C) (fun z ↦ A z (d z)) :=
  linCarl_of_bound A h.principal h.eps0 hae hd

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem hmfCrit {eps K C t : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (h : HmfCoeff eps K A Q) (hC : 0 ≤ C) (ht : 0 < t) :
    (∫ s : ℝ in 0..t, (eps * C) * critTime t s) ≤ 4 * (eps * C) :=
  critCoeff_int_le ht (mul_nonneg h.eps0 hC)

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem quadDiffWt {K T A₁ A₂ AΔ : ℝ}
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (hK : ∀ z, ‖Q z‖ ≤ K) (hK0 : 0 ≤ K)
    (hA₂0 : 0 ≤ A₂) (hAΔ0 : 0 ≤ AΔ)
    {d₁ d₂ : ℝ × V → G}
    (hd₁ : GradWt T A₁ d₁) (hd₂ : GradWt T A₂ d₂)
    (hdΔ : GradWt T AΔ (fun z ↦ d₁ z - d₂ z)) :
    SrcWt T (K * AΔ * A₁ + K * A₂ * AΔ)
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  have h₁ := bilinWt_of_bound Q hK hK0 hAΔ0 hdΔ hd₁
  have h₂ := bilinWt_of_bound Q hK hK0 hA₂0 hd₂ hdΔ
  have hadd := srcWt_add h₁ h₂
  have hsplit :
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) =
        (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z) +
          Q z (d₂ z) (d₁ z - d₂ z)) := by
    funext z
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  exact hadd

theorem quadDiffCarl {K T : ℝ} {C₁ C₂ CΔ : ℝ≥0∞}
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (hK : ∀ z, ‖Q z‖ ≤ K) (hK0 : 0 ≤ K)
    {d₁ d₂ : ℝ × V → G}
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z))
      (stVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (d₂ z) (d₁ z - d₂ z))
      (stVolume : Measure (ℝ × V)))
    (hd₁ : GradCarl T C₁ d₁) (hd₂ : GradCarl T C₂ d₂)
    (hdΔ : GradCarl T CΔ (fun z ↦ d₁ z - d₂ z)) :
    SrcCarl T
      (ENNReal.ofReal K * (CΔ + C₁) + ENNReal.ofReal K * (C₂ + CΔ))
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  have h₁ := bilinCarl_bound Q hK hK0 hae₁ hdΔ hd₁
  have h₂ := bilinCarl_bound Q hK hK0 hae₂ hd₂ hdΔ
  have hadd := srcCarl_add h₁ h₂
  have hsplit :
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) =
        (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z) +
          Q z (d₂ z) (d₁ z - d₂ z)) := by
    funext z
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  exact hadd

theorem hmfDiffSplit {eps K T A₁ A₂ AΔ : ℝ}
    {C₁ C₂ CΔ : ℝ≥0∞}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (h : HmfCoeff eps K A Q)
    (hA₂0 : 0 ≤ A₂) (hAΔ0 : 0 ≤ AΔ)
    {d₁ d₂ : ℝ × V → G}
    (haep : AEStronglyMeasurable (fun z ↦ A z (d₁ z - d₂ z))
      (stVolume : Measure (ℝ × V)))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (d₁ z - d₂ z) (d₁ z))
      (stVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (d₂ z) (d₁ z - d₂ z))
      (stVolume : Measure (ℝ × V)))
    (hw₁ : GradWt T A₁ d₁) (hw₂ : GradWt T A₂ d₂)
    (hwΔ : GradWt T AΔ (fun z ↦ d₁ z - d₂ z))
    (hc₁ : GradCarl T C₁ d₁) (hc₂ : GradCarl T C₂ d₂)
    (hcΔ : GradCarl T CΔ (fun z ↦ d₁ z - d₂ z)) :
    HmfSplit T (eps * AΔ)
      (K * AΔ * A₁ + K * A₂ * AΔ)
      (ENNReal.ofReal (eps ^ 2) * CΔ)
      (ENNReal.ofReal K * (CΔ + C₁) + ENNReal.ofReal K * (C₂ + CΔ))
      (fun z ↦ A z (d₁ z - d₂ z))
      (fun z ↦ Q z (d₁ z) (d₁ z) - Q z (d₂ z) (d₂ z)) := by
  exact ⟨
    linWt_of_bound A h.principal h.eps0 hwΔ,
    linCarl_of_bound A h.principal h.eps0 haep hcΔ,
    quadDiffWt Q h.quadratic h.K0 hA₂0 hAΔ0 hw₁ hw₂ hwΔ,
    quadDiffCarl Q h.quadratic h.K0 hae₁ hae₂ hc₁ hc₂ hcΔ⟩

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
