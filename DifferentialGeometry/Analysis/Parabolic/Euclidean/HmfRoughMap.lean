import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelBeta
import DifferentialGeometry.Analysis.Parabolic.Euclidean.QuasilinearFlux

/-!
# Rough fixed-point interface for a local-addition harmonic-map heat flow

This is the specialization actually needed by smooth Ricci-flow forward
uniqueness.  The unknown is the local-addition section `V`, with zero initial
value.  Its nonlinear equation is split into

* a divergence flux `a(t,x) DV`, where the prescribed coefficient is the
  inverse-domain-metric difference `g(t)^{-1} - q^{-1}`;
* a target/local-addition term quadratic in `DV`.

The first coefficient is small because `g(t)` is uniformly `C^0` close to
`q = g(0)` on a short closed edge window.  The critical heat convolution has
no small horizon factor, so this coefficient smallness is retained explicitly
in every estimate below.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coefficient data for the local-addition HMF rough map.  `eps` bounds the
prescribed inverse-metric-difference flux and is the principal contraction
parameter.  `K` is only a uniform bound for the quadratic target coefficient. -/
structure HmfCoeff (eps K : ℝ)
    (A : ℝ × V → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F) : Prop where
  eps0 : 0 ≤ eps
  K0 : 0 ≤ K
  principal : ∀ z, ‖A z‖ ≤ eps
  quadratic : ∀ z, ‖Q z‖ ≤ K

/-- The two different analytic source classes in the HMF Duhamel map.  The
principal term is a divergence flux and therefore has the gradient-shaped
weighted/Carleson controls; the quadratic term is an undifferentiated source. -/
structure HmfSplit (T Ap As : ℝ) (Cp Cs : ℝ≥0∞)
    (p s : ℝ × V → F) : Prop where
  principalWt : GradWt T Ap p
  principalCarl : GradCarl T Cp p
  sourceWt : SrcWt T As s
  sourceCarl : SrcCarl T Cs s

/-- Weighted estimate for the prescribed inverse-metric-difference flux. -/
theorem hmfPrinWt {eps K T C : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    {d : ℝ × V → G}
    (h : HmfCoeff eps K A Q) (hd : GradWt T C d) :
    GradWt T (eps * C) (fun z ↦ A z (d z)) :=
  linWt_of_bound A h.principal h.eps0 hd

/-- Local `L²` Carleson estimate for the same prescribed principal flux. -/
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

/-- The critical first-heat-derivative time convolution leaves `eps` as the
small factor and supplies no power of the horizon. -/
theorem hmfCrit {eps K C t : ℝ}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (h : HmfCoeff eps K A Q) (hC : 0 ≤ C) (ht : 0 < t) :
    (∫ s : ℝ in 0..t, (eps * C) * critTime t s) ≤ 4 * (eps * C) :=
  critCoeff_int_le ht (mul_nonneg h.eps0 hC)

/-- Weighted two-arm difference estimate for the quadratic local-addition
source. -/
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

/-- Carleson two-arm difference estimate for the same quadratic source. -/
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

/-- Consumer-shaped stability package for the difference of two HMF
fixed-point iterates.  It keeps the principal divergence flux and quadratic
source in their distinct rough classes. -/
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
