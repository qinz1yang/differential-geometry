import DifferentialGeometry.Analysis.Parabolic.Euclidean.Carleson.Rough

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V Y G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure HarmonicMapFlowStateQuadraticCoefficients (K L : ℝ)
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F) : Prop where
  K0 : 0 ≤ K
  L0 : 0 ≤ L
  base : ∀ z, ‖Q z 0‖ ≤ K
  state_lip : ∀ z y₁ y₂, ‖Q z y₁ - Q z y₂‖ ≤ L * ‖y₁ - y₂‖

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ Y] in
theorem HarmonicMapFlowStateQuadraticCoefficients.norm_le {K L R : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowStateQuadraticCoefficients K L Q) {z : ℝ × V} {y : Y}
    (hy : ‖y‖ ≤ R) : ‖Q z y‖ ≤ K + L * R := by
  calc
    ‖Q z y‖ ≤ ‖Q z 0‖ + ‖Q z y - Q z 0‖ := by
      have hs : Q z y = Q z 0 + (Q z y - Q z 0) := by abel
      calc
        ‖Q z y‖ = ‖Q z 0 + (Q z y - Q z 0)‖ := congrArg norm hs
        _ ≤ ‖Q z 0‖ + ‖Q z y - Q z 0‖ :=
          norm_add_le (Q z 0) (Q z y - Q z 0)
    _ ≤ K + L * ‖y - 0‖ := add_le_add (h.base z) (h.state_lip z y 0)
    _ = K + L * ‖y‖ := by rw [sub_zero]
    _ ≤ K + L * R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hy h.L0)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ Y] in
theorem HarmonicMapFlowStateQuadraticCoefficients.dist_le {K L D : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowStateQuadraticCoefficients K L Q) {z : ℝ × V} {y₁ y₂ : Y}
    (hy : ‖y₁ - y₂‖ ≤ D) :
    ‖Q z y₁ - Q z y₂‖ ≤ L * D :=
  (h.state_lip z y₁ y₂).trans
    (mul_le_mul_of_nonneg_left hy h.L0)

def harmonicMapFlowStateQuadraticSource
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F)
    (p : ℝ × V → Y) (d : ℝ × V → G) (z : ℝ × V) : F :=
  Q z (p z) (d z) (d z)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateQuadraticSource_sub
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F)
    (p₁ p₂ : ℝ × V → Y) (d₁ d₂ : ℝ × V → G) (z : ℝ × V) :
    harmonicMapFlowStateQuadraticSource Q p₁ d₁ z - harmonicMapFlowStateQuadraticSource Q p₂ d₂ z =
      Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z) := by
  simp only [harmonicMapFlowStateQuadraticSource, map_sub, sub_apply]
  abel

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem bilinear_weighted_boundOn
    (B : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    {T K A₁ A₂ : ℝ} {d₁ d₂ : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K) (hA₁ : 0 ≤ A₁)
    (h₁ : GradientWeightedBound T A₁ d₁) (h₂ : GradientWeightedBound T A₂ d₂) :
    SourceWeightedBound T (K * A₁ * A₂) (fun z ↦ B z (d₁ z) (d₂ z)) := by
  intro t x ht hT
  have hd₁ := h₁ t x ht hT
  have hd₂ := h₂ t x ht hT
  have hb : ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖ ≤
      (K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ := by
    calc
      ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖
          ≤ ‖B (t, x) (d₁ (t, x))‖ * ‖d₂ (t, x)‖ :=
        (B (t, x) (d₁ (t, x))).le_opNorm _
      _ ≤ (‖B (t, x)‖ * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ :=
        mul_le_mul_of_nonneg_right
          ((B (t, x)).le_opNorm _) (norm_nonneg _)
      _ ≤ (K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ := by
        gcongr
        exact hK t x ht hT
  calc
    t * ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖
        ≤ t * ((K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left hb ht.le
    _ = K * (Real.sqrt t * ‖d₁ (t, x)‖) *
          (Real.sqrt t * ‖d₂ (t, x)‖) := by
      nth_rewrite 1 [← Real.sq_sqrt ht.le]
      ring
    _ ≤ K * A₁ * (Real.sqrt t * ‖d₂ (t, x)‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd₁ hK0)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ ≤ K * A₁ * A₂ :=
      mul_le_mul_of_nonneg_left hd₂ (mul_nonneg hK0 hA₁)

theorem bilinear_carleson_boundOn
    (B : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    {T K : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ d₂ : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ B z (d₁ z) (d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (h₁ : GradientCarlesonBound T C₁ d₁) (h₂ : GradientCarlesonBound T C₂ d₂) :
    SourceCarlesonBound T (ENNReal.ofReal K * (C₁ + C₂))
      (fun z ↦ B z (d₁ z) (d₂ z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (spaceTimeVolume : Measure (ℝ × V)).restrict (forwardParabolicCylinder x R)
  have hm₁ : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2)) μ :=
    ((h₁.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hm₂ : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ :=
    ((h₂.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hmadd : AEMeasurable
      (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2) +
        ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ := hm₁.add hm₂
  have hpoint : ∀ᵐ z ∂μ,
      ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ≤
        ENNReal.ofReal K *
          (ENNReal.ofReal (‖d₁ z‖ ^ 2) +
            ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_ball)] with z hz
    have hzT : z.1 ≤ T := hz.1.2.trans hRT
    have hreal : ‖B z (d₁ z) (d₂ z)‖ ≤
        K * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2) :=
      (norm_bilinear_apply_le_norm_mul_add_sq (B z) (d₁ z) (d₂ z)).trans
        (mul_le_mul_of_nonneg_right (hK z.1 z.2 hz.1.1 hzT)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    calc
      ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖
          ≤ ENNReal.ofReal (K * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal K *
          (ENNReal.ofReal (‖d₁ z‖ ^ 2) +
            ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
        rw [ENNReal.ofReal_mul hK0,
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  change (∫⁻ z, ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ∂μ) ≤
    (ENNReal.ofReal K * (C₁ + C₂)) *
      ENNReal.ofReal (R ^ Module.finrank ℝ V)
  calc
    (∫⁻ z, ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal K *
            (ENNReal.ofReal (‖d₁ z‖ ^ 2) +
              ENNReal.ofReal (‖d₂ z‖ ^ 2)) ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal K * (gradientCarlesonMass d₁ x R + gradientCarlesonMass d₂ x R) := by
      rw [lintegral_const_mul'' _ hmadd, lintegral_add_left' hm₁]
      rfl
    _ ≤ ENNReal.ofReal K *
        ((C₁ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) +
          C₂ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) := by
      gcongr
      · exact h₁.bound x R hR hRT
      · exact h₂.bound x R hR hRT
    _ = (ENNReal.ofReal K * (C₁ + C₂)) *
        ENNReal.ofReal (R ^ Module.finrank ℝ V) := by ring

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateQuadraticSourceWeightedBound
    {K L T R Dp Rg Dg : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowStateQuadraticCoefficients K L Q) (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    (hRg : 0 ≤ Rg) (hDg : 0 ≤ Dg)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathUniformBound T R p₁)
    (hpΔ : PathUniformBound T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₁ : GradientWeightedBound T Rg d₁) (hd₂ : GradientWeightedBound T Rg d₂)
    (hdΔ : GradientWeightedBound T Dg (fun z ↦ d₁ z - d₂ z)) :
    SourceWeightedBound T
      ((K + L * R) * Dg * Rg + (K + L * R) * Rg * Dg +
        (L * Dp) * Rg * Rg)
      (fun z ↦ harmonicMapFlowStateQuadraticSource Q p₁ d₁ z -
        harmonicMapFlowStateQuadraticSource Q p₂ d₂ z) := by
  have hcoef : 0 ≤ K + L * R :=
    add_nonneg h.K0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  have h₁ := bilinear_weighted_boundOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.norm_le h (hp₁ t x ht hT))
    hcoef hDg hdΔ hd₁
  have h₂ := bilinear_weighted_boundOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.norm_le h (hp₁ t x ht hT))
    hcoef hRg hd₂ hdΔ
  have h₃ := bilinear_weighted_boundOn (fun z ↦ Q z (p₁ z) - Q z (p₂ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.dist_le h (hpΔ t x ht hT))
    hcoefD hRg hd₂ hd₂
  rw [show (fun z ↦ harmonicMapFlowStateQuadraticSource Q p₁ d₁ z -
      harmonicMapFlowStateQuadraticSource Q p₂ d₂ z) =
      (fun z ↦ (Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) by
    funext z
    rw [harmonicMapFlowStateQuadraticSource_sub]]
  exact SourceWeightedBound.add (SourceWeightedBound.add h₁ h₂) h₃

omit [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateQuadraticSourceCarlesonBound
    {K L T R Dp : ℝ} {C₁ C₂ CΔ : ℝ≥0∞}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HarmonicMapFlowStateQuadraticCoefficients K L Q) (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathUniformBound T R p₁)
    (hpΔ : PathUniformBound T Dp (fun z ↦ p₁ z - p₂ z))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (p₁ z) (d₁ z - d₂ z) (d₁ z)) spaceTimeVolume)
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) spaceTimeVolume)
    (hae₃ : AEStronglyMeasurable
      (fun z ↦ (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) spaceTimeVolume)
    (hd₁ : GradientCarlesonBound T C₁ d₁) (hd₂ : GradientCarlesonBound T C₂ d₂)
    (hdΔ : GradientCarlesonBound T CΔ (fun z ↦ d₁ z - d₂ z)) :
    SourceCarlesonBound T
      (ENNReal.ofReal (K + L * R) * (CΔ + C₁) +
        ENNReal.ofReal (K + L * R) * (C₂ + CΔ) +
        ENNReal.ofReal (L * Dp) * (C₂ + C₂))
      (fun z ↦ harmonicMapFlowStateQuadraticSource Q p₁ d₁ z -
        harmonicMapFlowStateQuadraticSource Q p₂ d₂ z) := by
  have hcoef : 0 ≤ K + L * R :=
    add_nonneg h.K0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  have h₁ := bilinear_carleson_boundOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.norm_le h (hp₁ t x ht hT))
    hcoef hae₁ hdΔ hd₁
  have h₂ := bilinear_carleson_boundOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.norm_le h (hp₁ t x ht hT))
    hcoef hae₂ hd₂ hdΔ
  have h₃ := bilinear_carleson_boundOn (fun z ↦ Q z (p₁ z) - Q z (p₂ z))
    (fun t x ht hT ↦ HarmonicMapFlowStateQuadraticCoefficients.dist_le h (hpΔ t x ht hT))
    hcoefD hae₃ hd₂ hd₂
  rw [show (fun z ↦ harmonicMapFlowStateQuadraticSource Q p₁ d₁ z -
      harmonicMapFlowStateQuadraticSource Q p₂ d₂ z) =
      (fun z ↦ (Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) by
    funext z
    rw [harmonicMapFlowStateQuadraticSource_sub]]
  exact SourceCarlesonBound.add (SourceCarlesonBound.add h₁ h₂) h₃

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
