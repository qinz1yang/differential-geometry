import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson

/-!
# State-dependent quadratic HMF source

The local-addition quadratic-gradient coefficient depends on the path value.
Its difference therefore has a third arm in addition to the usual two
gradient arms:

`(Q(u) - Q(v)) (Dv) (Dv)`.

This file records the exact split and the weighted/Carleson estimates.  The
third arm is small through the square of the rough state radius.
-/

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

/-- Uniform base bound and value-Lipschitz control for a state-dependent
quadratic-gradient coefficient. -/
structure HmfStateQuad (K L : ℝ)
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F) : Prop where
  K0 : 0 ≤ K
  L0 : 0 ≤ L
  base : ∀ z, ‖Q z 0‖ ≤ K
  state_lip : ∀ z y₁ y₂, ‖Q z y₁ - Q z y₂‖ ≤ L * ‖y₁ - y₂‖

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ Y] in
theorem stateQuad_bound {K L R : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HmfStateQuad K L Q) {z : ℝ × V} {y : Y}
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
theorem stateQuad_sub {K L D : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HmfStateQuad K L Q) {z : ℝ × V} {y₁ y₂ : Y}
    (hy : ‖y₁ - y₂‖ ≤ D) :
    ‖Q z y₁ - Q z y₂‖ ≤ L * D :=
  (h.state_lip z y₁ y₂).trans
    (mul_le_mul_of_nonneg_left hy h.L0)

/-- Realized state-dependent quadratic-gradient source. -/
def hmfStateQuadSrc
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F)
    (p : ℝ × V → Y) (d : ℝ × V → G) (z : ℝ × V) : F :=
  Q z (p z) (d z) (d z)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] in
/-- Exact three-arm difference split for the state-dependent quadratic
source. -/
theorem stateQuadSrc_sub
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F)
    (p₁ p₂ : ℝ × V → Y) (d₁ d₂ : ℝ × V → G) (z : ℝ × V) :
    hmfStateQuadSrc Q p₁ d₁ z - hmfStateQuadSrc Q p₂ d₂ z =
      Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z) := by
  simp only [hmfStateQuadSrc, map_sub, ContinuousLinearMap.sub_apply]
  abel

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Positive-slab version of the variable-coefficient weighted bilinear
estimate. -/
theorem bilinWtOn
    (B : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    {T K A₁ A₂ : ℝ} {d₁ d₂ : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K) (hA₁ : 0 ≤ A₁)
    (h₁ : GradWt T A₁ d₁) (h₂ : GradWt T A₂ d₂) :
    SrcWt T (K * A₁ * A₂) (fun z ↦ B z (d₁ z) (d₂ z)) := by
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

/-- Positive-slab version of `bilinCarl_bound`. -/
theorem bilinCarlOn
    (B : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    {T K : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ d₂ : ℝ × V → G}
    (hK : ∀ t x, 0 < t → t ≤ T → ‖B (t, x)‖ ≤ K)
    (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ B z (d₁ z) (d₂ z))
      (stVolume : Measure (ℝ × V)))
    (h₁ : GradCarl T C₁ d₁) (h₂ : GradCarl T C₂ d₂) :
    SrcCarl T (ENNReal.ofReal K * (C₁ + C₂))
      (fun z ↦ B z (d₁ z) (d₂ z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (stVolume : Measure (ℝ × V)).restrict (paraCyl x R)
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
      (bilin_sq_bound (B z) (d₁ z) (d₂ z)).trans
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
    _ = ENNReal.ofReal K * (gradMass d₁ x R + gradMass d₂ x R) := by
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
/-- Weighted estimate for all three state-quadratic difference arms. -/
theorem stateQuadSrcWt
    {K L T R Dp Rg Dg : ℝ}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HmfStateQuad K L Q) (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    (hRg : 0 ≤ Rg) (hDg : 0 ≤ Dg)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathSup T R p₁)
    (hpΔ : PathSup T Dp (fun z ↦ p₁ z - p₂ z))
    (hd₁ : GradWt T Rg d₁) (hd₂ : GradWt T Rg d₂)
    (hdΔ : GradWt T Dg (fun z ↦ d₁ z - d₂ z)) :
    SrcWt T
      ((K + L * R) * Dg * Rg + (K + L * R) * Rg * Dg +
        (L * Dp) * Rg * Rg)
      (fun z ↦ hmfStateQuadSrc Q p₁ d₁ z -
        hmfStateQuadSrc Q p₂ d₂ z) := by
  have hcoef : 0 ≤ K + L * R :=
    add_nonneg h.K0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  have h₁ := bilinWtOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ stateQuad_bound h (hp₁ t x ht hT))
    hcoef hDg hdΔ hd₁
  have h₂ := bilinWtOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ stateQuad_bound h (hp₁ t x ht hT))
    hcoef hRg hd₂ hdΔ
  have h₃ := bilinWtOn (fun z ↦ Q z (p₁ z) - Q z (p₂ z))
    (fun t x ht hT ↦ stateQuad_sub h (hpΔ t x ht hT))
    hcoefD hRg hd₂ hd₂
  rw [show (fun z ↦ hmfStateQuadSrc Q p₁ d₁ z -
      hmfStateQuadSrc Q p₂ d₂ z) =
      (fun z ↦ (Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) by
    funext z
    rw [stateQuadSrc_sub]]
  exact srcWt_add (srcWt_add h₁ h₂) h₃

omit [NormedSpace ℝ Y] in
/-- Carleson estimate for all three state-quadratic difference arms. -/
theorem stateQuadSrcCarl
    {K L T R Dp : ℝ} {C₁ C₂ CΔ : ℝ≥0∞}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (h : HmfStateQuad K L Q) (hR : 0 ≤ R) (hDp : 0 ≤ Dp)
    {p₁ p₂ : ℝ × V → Y} {d₁ d₂ : ℝ × V → G}
    (hp₁ : PathSup T R p₁)
    (hpΔ : PathSup T Dp (fun z ↦ p₁ z - p₂ z))
    (hae₁ : AEStronglyMeasurable
      (fun z ↦ Q z (p₁ z) (d₁ z - d₂ z) (d₁ z)) stVolume)
    (hae₂ : AEStronglyMeasurable
      (fun z ↦ Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) stVolume)
    (hae₃ : AEStronglyMeasurable
      (fun z ↦ (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) stVolume)
    (hd₁ : GradCarl T C₁ d₁) (hd₂ : GradCarl T C₂ d₂)
    (hdΔ : GradCarl T CΔ (fun z ↦ d₁ z - d₂ z)) :
    SrcCarl T
      (ENNReal.ofReal (K + L * R) * (CΔ + C₁) +
        ENNReal.ofReal (K + L * R) * (C₂ + CΔ) +
        ENNReal.ofReal (L * Dp) * (C₂ + C₂))
      (fun z ↦ hmfStateQuadSrc Q p₁ d₁ z -
        hmfStateQuadSrc Q p₂ d₂ z) := by
  have hcoef : 0 ≤ K + L * R :=
    add_nonneg h.K0 (mul_nonneg h.L0 hR)
  have hcoefD : 0 ≤ L * Dp := mul_nonneg h.L0 hDp
  have h₁ := bilinCarlOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ stateQuad_bound h (hp₁ t x ht hT))
    hcoef hae₁ hdΔ hd₁
  have h₂ := bilinCarlOn (fun z ↦ Q z (p₁ z))
    (fun t x ht hT ↦ stateQuad_bound h (hp₁ t x ht hT))
    hcoef hae₂ hd₂ hdΔ
  have h₃ := bilinCarlOn (fun z ↦ Q z (p₁ z) - Q z (p₂ z))
    (fun t x ht hT ↦ stateQuad_sub h (hpΔ t x ht hT))
    hcoefD hae₃ hd₂ hd₂
  rw [show (fun z ↦ hmfStateQuadSrc Q p₁ d₁ z -
      hmfStateQuadSrc Q p₂ d₂ z) =
      (fun z ↦ (Q z (p₁ z) (d₁ z - d₂ z) (d₁ z) +
        Q z (p₁ z) (d₂ z) (d₁ z - d₂ z)) +
        (Q z (p₁ z) - Q z (p₂ z)) (d₂ z) (d₂ z)) by
    funext z
    rw [stateQuadSrc_sub]]
  exact srcCarl_add (srcCarl_add h₁ h₂) h₃

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
