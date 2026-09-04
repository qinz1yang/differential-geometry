import DifferentialGeometry.Analysis.Parabolic.Euclidean.Carleson.Rough

noncomputable section
open MeasureTheory Set
open scoped ENNReal
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

structure HarmonicMapFlowStateCoefficients (eps L : ℝ)
    (A : ℝ × V → Y → G →L[ℝ] F) : Prop where
  eps0 : 0 ≤ eps
  L0 : 0 ≤ L
  base : ∀ z, ‖A z 0‖ ≤ eps
  state_lip : ∀ z y₁ y₂, ‖A z y₁ - A z y₂‖ ≤ L * ‖y₁ - y₂‖

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedSpace ℝ Y] in
theorem stateCoeff_bound {eps L R : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HarmonicMapFlowStateCoefficients eps L A) {z : ℝ × V} {y : Y}
    (hy : ‖y‖ ≤ R) :
    ‖A z y‖ ≤ eps + L * R := by
  calc
    ‖A z y‖ ≤ ‖A z 0‖ + ‖A z y - A z 0‖ := by
      have hs : A z y = A z 0 + (A z y - A z 0) := by abel
      calc
        ‖A z y‖ = ‖A z 0 + (A z y - A z 0)‖ := congrArg norm hs
        _ ≤ _ := norm_add_le _ _
    _ ≤ eps + L * ‖y - 0‖ := add_le_add (h.base z) (h.state_lip z y 0)
    _ = eps + L * ‖y‖ := by rw [sub_zero]
    _ ≤ eps + L * R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hy h.L0)
omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedSpace ℝ Y] in
theorem stateCoeff_sub {eps L D : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HarmonicMapFlowStateCoefficients eps L A) {z : ℝ × V} {y₁ y₂ : Y}
    (hy : ‖y₁ - y₂‖ ≤ D) :
    ‖A z y₁ - A z y₂‖ ≤ L * D :=
  (h.state_lip z y₁ y₂).trans
    (mul_le_mul_of_nonneg_left hy h.L0)

def harmonicMapFlowStateFlux
    (A : ℝ × V → Y → G →L[ℝ] F)
    (p : ℝ × V → Y) (d : ℝ × V → G) (z : ℝ × V) : F :=
  A z (p z) (d z)

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateFlux_sub
    (A : ℝ × V → Y → G →L[ℝ] F)
    (p₁ p₂ : ℝ × V → Y) (d₁ d₂ : ℝ × V → G) (z : ℝ × V) :
    harmonicMapFlowStateFlux A p₁ d₁ z - harmonicMapFlowStateFlux A p₂ d₂ z =
      A z (p₁ z) (d₁ z - d₂ z) +
        (A z (p₁ z) - A z (p₂ z)) (d₂ z) := by
  simp only [harmonicMapFlowStateFlux, map_sub, sub_apply]
  abel

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateFluxWeightedBound
    {eps L T R Dp Rg Dg : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HarmonicMapFlowStateCoefficients eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathUniformBound T R p₁)
    (hpΔ : PathUniformBound T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₂ : GradientWeightedBound T Rg d₂)
    (hdΔ : GradientWeightedBound T Dg (fun z ↦ d₁ z - d₂ z)) :
    GradientWeightedBound T ((eps + L * R) * Dg + (L * Dp) * Rg)
      (fun z ↦ harmonicMapFlowStateFlux A p₁ d₁ z - harmonicMapFlowStateFlux A p₂ d₂ z) := by
  intro t x ht hT
  let z : ℝ × V := (t, x)
  have hp₁R : ‖p₁ z‖ ≤ R := hp₁ t x ht hT
  have hpD : ‖p₁ z - p₂ z‖ ≤ Dp := hpΔ t x ht hT
  have hA : ‖A z (p₁ z)‖ ≤ eps + L * R :=
    stateCoeff_bound h hp₁R
  have hAD : ‖A z (p₁ z) - A z (p₂ z)‖ ≤ L * Dp :=
    stateCoeff_sub h hpD
  have hcoef : 0 ≤ eps + L * R :=
    add_nonneg h.eps0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  change Real.sqrt t *
      ‖harmonicMapFlowStateFlux A p₁ d₁ z - harmonicMapFlowStateFlux A p₂ d₂ z‖ ≤
        (eps + L * R) * Dg + L * Dp * Rg
  rw [harmonicMapFlowStateFlux_sub]
  calc
    Real.sqrt t *
        ‖A z (p₁ z) (d₁ z - d₂ z) +
          (A z (p₁ z) - A z (p₂ z)) (d₂ z)‖
        ≤ Real.sqrt t *
          (‖A z (p₁ z) (d₁ z - d₂ z)‖ +
            ‖(A z (p₁ z) - A z (p₂ z)) (d₂ z)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt t *
          ((eps + L * R) * ‖d₁ z - d₂ z‖ +
            (L * Dp) * ‖d₂ z‖) := by
      gcongr
      · exact (A z (p₁ z)).le_opNorm (d₁ z - d₂ z) |>.trans
          (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      · exact (A z (p₁ z) - A z (p₂ z)).le_opNorm (d₂ z) |>.trans
          (mul_le_mul_of_nonneg_right hAD (norm_nonneg _))
    _ = (eps + L * R) * (Real.sqrt t * ‖d₁ z - d₂ z‖) +
          (L * Dp) * (Real.sqrt t * ‖d₂ z‖) := by ring
    _ ≤ (eps + L * R) * Dg + (L * Dp) * Rg :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hdΔ t x ht hT) hcoef)
        (mul_le_mul_of_nonneg_left (hd₂ t x ht hT) hcoefD)

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V] in
theorem linear_weighted_boundOn
    (B : ℝ × V → G →L[ℝ] F)
    {T K C : ℝ} {d : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K) (hd : GradientWeightedBound T C d) :
    GradientWeightedBound T (K * C) (fun z ↦ B z (d z)) := by
  intro t x ht hT
  calc
    Real.sqrt t * ‖B (t, x) (d (t, x))‖
        ≤ Real.sqrt t * (‖B (t, x)‖ * ‖d (t, x)‖) :=
      mul_le_mul_of_nonneg_left ((B (t, x)).le_opNorm _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt t * (K * ‖d (t, x)‖) := by
      gcongr
      exact hK t x ht hT
    _ = K * (Real.sqrt t * ‖d (t, x)‖) := by ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hd t x ht hT) hK0

theorem linear_carleson_boundOn
    (B : ℝ × V → G →L[ℝ] F)
    {T K : ℝ} {C : ℝ≥0∞} {d : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ B z (d z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hd : GradientCarlesonBound T C d) :
    GradientCarlesonBound T (ENNReal.ofReal (K ^ 2) * C) (fun z ↦ B z (d z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (spaceTimeVolume : Measure (ℝ × V)).restrict (forwardParabolicCylinder x R)
  have hmd : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d z‖ ^ 2)) μ :=
    ((hd.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hpoint : ∀ᵐ z ∂μ,
      ENNReal.ofReal (‖B z (d z)‖ ^ 2) ≤
        ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_ball)] with z hz
    have hzT : z.1 ≤ T := hz.1.2.trans hRT
    have hlin : ‖B z (d z)‖ ≤ K * ‖d z‖ :=
      (B z).le_opNorm (d z) |>.trans
        (mul_le_mul_of_nonneg_right
          (hK z.1 z.2 hz.1.1 hzT) (norm_nonneg _))
    have hsq : ‖B z (d z)‖ ^ 2 ≤ (K * ‖d z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).2 hlin
    calc
      ENNReal.ofReal (‖B z (d z)‖ ^ 2)
          ≤ ENNReal.ofReal ((K * ‖d z‖) ^ 2) :=
        ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) := by
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg K)]
  change (∫⁻ z, ENNReal.ofReal (‖B z (d z)‖ ^ 2) ∂μ) ≤
    (ENNReal.ofReal (K ^ 2) * C) *
      ENNReal.ofReal (R ^ Module.finrank ℝ V)
  calc
    (∫⁻ z, ENNReal.ofReal (‖B z (d z)‖ ^ 2) ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal (K ^ 2) *
            ENNReal.ofReal (‖d z‖ ^ 2) ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (K ^ 2) * gradientCarlesonMass d x R := by
      rw [lintegral_const_mul'' _ hmd]
      rfl
    _ ≤ ENNReal.ofReal (K ^ 2) *
          (C * ENNReal.ofReal (R ^ Module.finrank ℝ V)) :=
      mul_le_mul_right (hd.bound x R hR hRT) _
    _ = (ENNReal.ofReal (K ^ 2) * C) *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by ring

omit [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateFluxTermsWeightedBounds
    {eps L T R Dp Rg Dg : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HarmonicMapFlowStateCoefficients eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathUniformBound T R p₁)
    (hpΔ : PathUniformBound T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₂ : GradientWeightedBound T Rg d₂)
    (hdΔ : GradientWeightedBound T Dg (fun z ↦ d₁ z - d₂ z)) :
    GradientWeightedBound T ((eps + L * R) * Dg)
        (fun z ↦ A z (p₁ z) (d₁ z - d₂ z)) ∧
      GradientWeightedBound T ((L * Dp) * Rg)
        (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z)) := by
  have hcoef : 0 ≤ eps + L * R :=
    add_nonneg h.eps0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  constructor
  · apply linear_weighted_boundOn (fun z ↦ A z (p₁ z))
      (fun t x ht hT ↦ stateCoeff_bound h (hp₁ t x ht hT))
      hcoef hdΔ
  · apply linear_weighted_boundOn (fun z ↦ A z (p₁ z) - A z (p₂ z))
      (fun t x ht hT ↦ stateCoeff_sub h (hpΔ t x ht hT))
      hcoefD hd₂

omit [NormedSpace ℝ Y] in
theorem harmonicMapFlowStateFluxTermsCarlesonBounds
    {eps L T R Dp : ℝ} {C₂ CΔ : ℝ≥0∞}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HarmonicMapFlowStateCoefficients eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathUniformBound T R p₁)
    (hpΔ : PathUniformBound T Dp (fun z ↦ p₁ z - p₂ z))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ A z (p₁ z) (d₁ z - d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hd₂ : GradientCarlesonBound T C₂ d₂)
    (hdΔ : GradientCarlesonBound T CΔ (fun z ↦ d₁ z - d₂ z)) :
    GradientCarlesonBound T (ENNReal.ofReal ((eps + L * R) ^ 2) * CΔ)
        (fun z ↦ A z (p₁ z) (d₁ z - d₂ z)) ∧
      GradientCarlesonBound T (ENNReal.ofReal ((L * Dp) ^ 2) * C₂)
        (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z)) := by
  have hcoef : 0 ≤ eps + L * R :=
    add_nonneg h.eps0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  constructor
  · apply linear_carleson_boundOn (fun z ↦ A z (p₁ z))
      (fun t x ht hT ↦ stateCoeff_bound h (hp₁ t x ht hT))
      hcoef hae₁ hdΔ
  · apply linear_carleson_boundOn (fun z ↦ A z (p₁ z) - A z (p₂ z))
      (fun t x ht hT ↦ stateCoeff_sub h (hpΔ t x ht hT))
      hcoefD hae₂ hd₂

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
