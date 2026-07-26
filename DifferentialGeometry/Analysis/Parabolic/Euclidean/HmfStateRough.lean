import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson

/-!
# A state-dependent principal arm in rough parabolic coordinates

This file records the exact difference split and rough estimates when a
principal flux genuinely depends on the state value.  It is a valid general
extension of `HmfCoeff`, but it is not forced by harmonic-map heat flow: in a
strong local-addition formula the vertical derivative multiplying `V_t`
should cancel the identical vertical derivative in the leading tension term.
After that cancellation the actual HMF principal coefficient is prescribed
by the domain metric, corresponding to the specialization `L = 0` here.
-/

noncomputable section

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

/-- Quantitative state dependence of a principal coefficient. -/
structure HmfStateCoeff (eps L : ℝ)
    (A : ℝ × V → Y → G →L[ℝ] F) : Prop where
  eps0 : 0 ≤ eps
  L0 : 0 ≤ L
  base : ∀ z, ‖A z 0‖ ≤ eps
  state_lip : ∀ z y₁ y₂, ‖A z y₁ - A z y₂‖ ≤ L * ‖y₁ - y₂‖

/-- On a radius-`R` state ball the full principal coefficient has size at
most `eps + L R`. -/
theorem stateCoeff_bound {eps L R : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HmfStateCoeff eps L A) {z : ℝ × V} {y : Y}
    (hy : ‖y‖ ≤ R) :
    ‖A z y‖ ≤ eps + L * R := by
  calc
    ‖A z y‖ ≤ ‖A z 0‖ + ‖A z y - A z 0‖ := by
      have hs : A z y = A z 0 + (A z y - A z 0) := by abel
      rw [hs]
      exact norm_add_le _ _
    _ ≤ eps + L * ‖y - 0‖ := add_le_add (h.base z) (h.state_lip z y 0)
    _ = eps + L * ‖y‖ := by rw [sub_zero]
    _ ≤ eps + L * R := add_le_add_left
      (mul_le_mul_of_nonneg_left hy h.L0) eps

/-- Difference form of the state-coefficient bound. -/
theorem stateCoeff_sub {eps L D : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HmfStateCoeff eps L A) {z : ℝ × V} {y₁ y₂ : Y}
    (hy : ‖y₁ - y₂‖ ≤ D) :
    ‖A z y₁ - A z y₂‖ ≤ L * D :=
  (h.state_lip z y₁ y₂).trans
    (mul_le_mul_of_nonneg_left hy h.L0)

/-- Realized state-dependent HMF principal flux. -/
def hmfStateFlux
    (A : ℝ × V → Y → G →L[ℝ] F)
    (p : ℝ × V → Y) (d : ℝ × V → G) (z : ℝ × V) : F :=
  A z (p z) (d z)

/-- Exact two-arm difference split for a state-dependent principal flux.
The first arm moves the gradient, while the second moves the coefficient and
retains the partner gradient. -/
theorem hmfStateFlux_sub
    (A : ℝ × V → Y → G →L[ℝ] F)
    (p₁ p₂ : ℝ × V → Y) (d₁ d₂ : ℝ × V → G) (z : ℝ × V) :
    hmfStateFlux A p₁ d₁ z - hmfStateFlux A p₂ d₂ z =
      A z (p₁ z) (d₁ z - d₂ z) +
        (A z (p₁ z) - A z (p₂ z)) (d₂ z) := by
  simp only [hmfStateFlux, map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- Weighted critical estimate for the repaired state-dependent HMF
principal flux.  Besides the prescribed smallness `eps`, the contraction
coefficient contains only state-ball quantities `L R` and `L Dp`; no false
horizon power is introduced. -/
theorem hmfStateFluxWt
    {eps L T R Dp Rg Dg : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HmfStateCoeff eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathSup T R p₁)
    (hpΔ : PathSup T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₂ : GradWt T Rg d₂)
    (hdΔ : GradWt T Dg (fun z ↦ d₁ z - d₂ z)) :
    GradWt T ((eps + L * R) * Dg + (L * Dp) * Rg)
      (fun z ↦ hmfStateFlux A p₁ d₁ z - hmfStateFlux A p₂ d₂ z) := by
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
  rw [hmfStateFlux_sub]
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

/-! ## Local Carleson control

The coefficient bounds needed for a Carleson cylinder are only required on
`0 < t ≤ T`.  This localized variant avoids extending a state-ball bound to
irrelevant negative or late times. -/

/-- A coefficient bounded on the positive time slab preserves the weighted
gradient class. -/
theorem linWtOn
    (B : ℝ × V → G →L[ℝ] F)
    {T K C : ℝ} {d : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K) (hd : GradWt T C d) :
    GradWt T (K * C) (fun z ↦ B z (d z)) := by
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

/-- A coefficient bounded on the positive time slab preserves the gradient
Carleson class.  This is the slab-local counterpart of `linCarl_of_bound`. -/
theorem linCarlOn
    (B : ℝ × V → G →L[ℝ] F)
    {T K : ℝ} {C : ℝ≥0∞} {d : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ B z (d z))
      (stVolume : Measure (ℝ × V)))
    (hd : GradCarl T C d) :
    GradCarl T (ENNReal.ofReal (K ^ 2) * C) (fun z ↦ B z (d z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (stVolume : Measure (ℝ × V)).restrict (paraCyl x R)
  have hmd : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d z‖ ^ 2)) μ :=
    ((hd.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hpoint : ∀ᵐ z ∂μ,
      ENNReal.ofReal (‖B z (d z)‖ ^ 2) ≤
        ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod Metric.measurableSet_ball)] with z hz
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
    _ = ENNReal.ofReal (K ^ 2) * gradMass d x R := by
      rw [lintegral_const_mul'' _ hmd]
      rfl
    _ ≤ ENNReal.ofReal (K ^ 2) *
          (C * ENNReal.ofReal (R ^ Module.finrank ℝ V)) :=
      mul_le_mul_right (hd.bound x R hR hRT) _
    _ = (ENNReal.ofReal (K ^ 2) * C) *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by ring

/-- Separate weighted estimates for the two state-principal difference
arms. -/
theorem hmfStateFluxWt2
    {eps L T R Dp Rg Dg : ℝ}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HmfStateCoeff eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathSup T R p₁)
    (hpΔ : PathSup T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₂ : GradWt T Rg d₂)
    (hdΔ : GradWt T Dg (fun z ↦ d₁ z - d₂ z)) :
    GradWt T ((eps + L * R) * Dg)
        (fun z ↦ A z (p₁ z) (d₁ z - d₂ z)) ∧
      GradWt T ((L * Dp) * Rg)
        (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z)) := by
  have hcoef : 0 ≤ eps + L * R :=
    add_nonneg h.eps0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  constructor
  · apply linWtOn (fun z ↦ A z (p₁ z))
      (fun t x ht hT ↦ stateCoeff_bound h (hp₁ t x ht hT))
      hcoef hdΔ
  · apply linWtOn (fun z ↦ A z (p₁ z) - A z (p₂ z))
      (fun t x ht hT ↦ stateCoeff_sub h (hpΔ t x ht hT))
      hcoefD hd₂

/-- The two state-dependent principal difference arms have separate
Carleson estimates.  This is the form consumed by two applications of the
linear heat-flux bound. -/
theorem hmfStateFluxCarl
    {eps L T R Dp : ℝ} {C₂ CΔ : ℝ≥0∞}
    {A : ℝ × V → Y → G →L[ℝ] F}
    (h : HmfStateCoeff eps L A)
    (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathSup T R p₁)
    (hpΔ : PathSup T Dp (fun z ↦ p₁ z - p₂ z))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ A z (p₁ z) (d₁ z - d₂ z))
      (stVolume : Measure (ℝ × V)))
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z))
      (stVolume : Measure (ℝ × V)))
    (hd₂ : GradCarl T C₂ d₂)
    (hdΔ : GradCarl T CΔ (fun z ↦ d₁ z - d₂ z)) :
    GradCarl T (ENNReal.ofReal ((eps + L * R) ^ 2) * CΔ)
        (fun z ↦ A z (p₁ z) (d₁ z - d₂ z)) ∧
      GradCarl T (ENNReal.ofReal ((L * Dp) ^ 2) * C₂)
        (fun z ↦ (A z (p₁ z) - A z (p₂ z)) (d₂ z)) := by
  have hcoef : 0 ≤ eps + L * R :=
    add_nonneg h.eps0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  constructor
  · apply linCarlOn (fun z ↦ A z (p₁ z))
      (fun t x ht hT ↦ stateCoeff_bound h (hp₁ t x ht hT))
      hcoef hae₁ hdΔ
  · apply linCarlOn (fun z ↦ A z (p₁ z) - A z (p₂ z))
      (fun t x ht hT ↦ stateCoeff_sub h (hpΔ t x ht hT))
      hcoefD hae₂ hd₂

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
