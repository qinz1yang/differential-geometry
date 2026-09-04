import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Cylinders

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def forwardParabolicCylinder (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc 0 (R ^ 2) ×ˢ Metric.ball x R

def spaceTimeVolume : Measure (ℝ × V) :=
  (volume : Measure ℝ).prod (volume : Measure V)

end Cylinders

section Masses

variable {V G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G]
  [NormedAddCommGroup F]

def gradientCarlesonMass (d : ℝ × V → G) (x : V) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in forwardParabolicCylinder x R, ENNReal.ofReal (‖d z‖ ^ 2) ∂(spaceTimeVolume : Measure (ℝ × V))

def sourceCarlesonMass (f : ℝ × V → F) (x : V) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in forwardParabolicCylinder x R, ENNReal.ofReal ‖f z‖ ∂(spaceTimeVolume : Measure (ℝ × V))

structure GradientCarlesonBound (T : ℝ) (C : ℝ≥0∞) (d : ℝ × V → G) : Prop where
  ae : AEStronglyMeasurable d (spaceTimeVolume : Measure (ℝ × V))
  bound : ∀ x R, 0 < R → R ^ 2 ≤ T →
    gradientCarlesonMass d x R ≤ C * ENNReal.ofReal (R ^ Module.finrank ℝ V)

structure SourceCarlesonBound (T : ℝ) (C : ℝ≥0∞) (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (spaceTimeVolume : Measure (ℝ × V))
  bound : ∀ x R, 0 < R → R ^ 2 ≤ T →
    sourceCarlesonMass f x R ≤ C * ENNReal.ofReal (R ^ Module.finrank ℝ V)

def PathUniformBound (T A : ℝ) (u : ℝ × V → G) : Prop :=
  ∀ t x, 0 < t → t ≤ T → ‖u (t, x)‖ ≤ A

def GradientWeightedBound (T A : ℝ) (d : ℝ × V → G) : Prop :=
  ∀ t x, 0 < t → t ≤ T → Real.sqrt t * ‖d (t, x)‖ ≤ A

def SourceWeightedBound (T A : ℝ) (f : ℝ × V → F) : Prop :=
  ∀ t x, 0 < t → t ≤ T → t * ‖f (t, x)‖ ≤ A

def HasRoughPathBounds (T A₀ A₁ : ℝ) (C₁ : ℝ≥0∞)
    (u : ℝ × V → F) (d : ℝ × V → G) : Prop :=
  PathUniformBound T A₀ u ∧ GradientWeightedBound T A₁ d ∧ GradientCarlesonBound T C₁ d

def HasRoughSourceBounds (T A : ℝ) (C : ℝ≥0∞) (f : ℝ × V → F) : Prop :=
  SourceWeightedBound T A f ∧ SourceCarlesonBound T C f

end Masses

section Bilinear

variable {V G H F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem linear_weighted_bound (A : ℝ × V → G →L[ℝ] F)
    {T K C : ℝ} {d : ℝ × V → G}
    (hK : ∀ z, ‖A z‖ ≤ K) (hK0 : 0 ≤ K) (hd : GradientWeightedBound T C d) :
    GradientWeightedBound T (K * C) (fun z ↦ A z (d z)) := by
  intro t x ht hT
  calc
    Real.sqrt t * ‖A (t, x) (d (t, x))‖
        ≤ Real.sqrt t * (‖A (t, x)‖ * ‖d (t, x)‖) :=
      mul_le_mul_of_nonneg_left ((A (t, x)).le_opNorm _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt t * (K * ‖d (t, x)‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hK (t, x)) (norm_nonneg _))
        (Real.sqrt_nonneg _)
    _ = K * (Real.sqrt t * ‖d (t, x)‖) := by ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hd t x ht hT) hK0

theorem linear_carleson_bound (A : ℝ × V → G →L[ℝ] F)
    {T K : ℝ} {C : ℝ≥0∞} {d : ℝ × V → G}
    (hK : ∀ z, ‖A z‖ ≤ K) (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ A z (d z))
      (spaceTimeVolume : Measure (ℝ × V)))
    (hd : GradientCarlesonBound T C d) :
    GradientCarlesonBound T (ENNReal.ofReal (K ^ 2) * C) (fun z ↦ A z (d z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (spaceTimeVolume : Measure (ℝ × V)).restrict (forwardParabolicCylinder x R)
  have hmd : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d z‖ ^ 2)) μ :=
    ((hd.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hpoint : ∀ z : ℝ × V,
      ENNReal.ofReal (‖A z (d z)‖ ^ 2) ≤
        ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) := by
    intro z
    have hlin : ‖A z (d z)‖ ≤ K * ‖d z‖ :=
      (A z).le_opNorm (d z) |>.trans
        (mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _))
    have hsq : ‖A z (d z)‖ ^ 2 ≤ (K * ‖d z‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).2 hlin
    calc
      ENNReal.ofReal (‖A z (d z)‖ ^ 2)
          ≤ ENNReal.ofReal ((K * ‖d z‖) ^ 2) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) := by
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg K)]
  change (∫⁻ z, ENNReal.ofReal (‖A z (d z)‖ ^ 2) ∂μ) ≤
    (ENNReal.ofReal (K ^ 2) * C) *
      ENNReal.ofReal (R ^ Module.finrank ℝ V)
  calc
    (∫⁻ z, ENNReal.ofReal (‖A z (d z)‖ ^ 2) ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (‖d z‖ ^ 2) ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (K ^ 2) * gradientCarlesonMass d x R := by
      rw [lintegral_const_mul'' _ hmd]
      rfl
    _ ≤ ENNReal.ofReal (K ^ 2) *
          (C * ENNReal.ofReal (R ^ Module.finrank ℝ V)) :=
      mul_le_mul_right (hd.bound x R hR hRT) _
    _ = (ENNReal.ofReal (K ^ 2) * C) *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
      ring

theorem norm_bilinear_apply_le_norm_mul_add_sq (B : G →L[ℝ] H →L[ℝ] F) (a : G) (b : H) :
    ‖B a b‖ ≤ ‖B‖ * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hab : ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc
    ‖B a b‖ ≤ ‖B a‖ * ‖b‖ := (B a).le_opNorm b
    _ ≤ (‖B‖ * ‖a‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm a) (norm_nonneg _)
    _ = ‖B‖ * (‖a‖ * ‖b‖) := by ring
    _ ≤ ‖B‖ * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hab (norm_nonneg B)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem bilinear_weighted_bound_of_norm_bound (B : ℝ × V → G →L[ℝ] H →L[ℝ] F)
    {T K A₁ A₂ : ℝ} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hK : ∀ z, ‖B z‖ ≤ K) (hK0 : 0 ≤ K) (hA₁ : 0 ≤ A₁)
    (h₁ : GradientWeightedBound T A₁ d₁) (h₂ : GradientWeightedBound T A₂ d₂) :
    SourceWeightedBound T (K * A₁ * A₂) (fun z ↦ B z (d₁ z) (d₂ z)) := by
  intro t x ht hT
  have hd₁ := h₁ t x ht hT
  have hd₂ := h₂ t x ht hT
  have hnorm : ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖ ≤
      (K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ := by
    calc
      ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖
          ≤ ‖B (t, x) (d₁ (t, x))‖ * ‖d₂ (t, x)‖ :=
        (B (t, x) (d₁ (t, x))).le_opNorm _
      _ ≤ (‖B (t, x)‖ * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ :=
        mul_le_mul_of_nonneg_right
          ((B (t, x)).le_opNorm (d₁ (t, x))) (norm_nonneg _)
      _ ≤ (K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hK (t, x)) (norm_nonneg _)) (norm_nonneg _)
  calc
    t * ‖B (t, x) (d₁ (t, x)) (d₂ (t, x))‖
        ≤ t * ((K * ‖d₁ (t, x)‖) * ‖d₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left hnorm ht.le
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

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem bilinear_weighted_bound (B : G →L[ℝ] H →L[ℝ] F)
    {T A₁ A₂ : ℝ} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hA₁ : 0 ≤ A₁) (h₁ : GradientWeightedBound T A₁ d₁) (h₂ : GradientWeightedBound T A₂ d₂) :
    SourceWeightedBound T (‖B‖ * A₁ * A₂) (fun z ↦ B (d₁ z) (d₂ z)) := by
  exact bilinear_weighted_bound_of_norm_bound (fun _ ↦ B) (fun _ ↦ le_rfl) (norm_nonneg B) hA₁ h₁ h₂

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ F] in
theorem SourceWeightedBound.add {T A₁ A₂ : ℝ} {f₁ f₂ : ℝ × V → F}
    (h₁ : SourceWeightedBound T A₁ f₁) (h₂ : SourceWeightedBound T A₂ f₂) :
    SourceWeightedBound T (A₁ + A₂) (fun z ↦ f₁ z + f₂ z) := by
  intro t x ht hT
  calc
    t * ‖f₁ (t, x) + f₂ (t, x)‖
        ≤ t * (‖f₁ (t, x)‖ + ‖f₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) ht.le
    _ = t * ‖f₁ (t, x)‖ + t * ‖f₂ (t, x)‖ := by ring
    _ ≤ A₁ + A₂ := add_le_add (h₁ t x ht hT) (h₂ t x ht hT)

theorem bilinear_carleson_bound (B : G →L[ℝ] H →L[ℝ] F)
    {T : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (h₁ : GradientCarlesonBound T C₁ d₁) (h₂ : GradientCarlesonBound T C₂ d₂) :
    SourceCarlesonBound T (ENNReal.ofReal ‖B‖ * (C₁ + C₂)) (fun z ↦ B (d₁ z) (d₂ z)) := by
  refine ⟨?_, ?_⟩
  · have hB : Continuous (fun p : G × H ↦ B p.1 p.2) :=
      (B.continuous.comp continuous_fst).clm_apply continuous_snd
    exact hB.comp_aestronglyMeasurable (h₁.ae.prodMk h₂.ae)
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (spaceTimeVolume : Measure (ℝ × V)).restrict (forwardParabolicCylinder x R)
    have hm₁ : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2)) μ :=
      ((h₁.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
        Measure.restrict_le_self
    have hm₂ : AEMeasurable (fun z ↦ ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ :=
      ((h₂.ae.norm.pow 2).aemeasurable.ennreal_ofReal).mono_measure
        Measure.restrict_le_self
    have hmadd : AEMeasurable
        (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ :=
      hm₁.add hm₂
    have hpoint : ∀ z : ℝ × V,
        ENNReal.ofReal ‖B (d₁ z) (d₂ z)‖ ≤
          ENNReal.ofReal ‖B‖ *
            (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
      intro z
      calc
        ENNReal.ofReal ‖B (d₁ z) (d₂ z)‖
            ≤ ENNReal.ofReal (‖B‖ * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (norm_bilinear_apply_le_norm_mul_add_sq B (d₁ z) (d₂ z))
        _ = ENNReal.ofReal ‖B‖ *
              (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul (norm_nonneg B),
            ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    change (∫⁻ z, ENNReal.ofReal ‖B (d₁ z) (d₂ z)‖ ∂μ) ≤
      (ENNReal.ofReal ‖B‖ * (C₁ + C₂)) *
        ENNReal.ofReal (R ^ Module.finrank ℝ V)
    calc
      (∫⁻ z, ENNReal.ofReal ‖B (d₁ z) (d₂ z)‖ ∂μ)
          ≤ ∫⁻ z, ENNReal.ofReal ‖B‖ *
              (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) ∂μ :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal ‖B‖ *
            ((∫⁻ z, ENNReal.ofReal (‖d₁ z‖ ^ 2) ∂μ) +
              ∫⁻ z, ENNReal.ofReal (‖d₂ z‖ ^ 2) ∂μ) := by
        rw [lintegral_const_mul'' _ hmadd, lintegral_add_left' hm₁]
      _ = ENNReal.ofReal ‖B‖ * (gradientCarlesonMass d₁ x R + gradientCarlesonMass d₂ x R) := by
        rfl
      _ ≤ ENNReal.ofReal ‖B‖ *
            ((C₁ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) +
              C₂ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) := by
        gcongr
        · exact h₁.bound x R hR hRT
        · exact h₂.bound x R hR hRT
      _ = (ENNReal.ofReal ‖B‖ * (C₁ + C₂)) *
            ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
        ring

theorem bilinear_carleson_bound_of_norm_bound (B : ℝ × V → G →L[ℝ] H →L[ℝ] F)
    {T K : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hK : ∀ z, ‖B z‖ ≤ K) (hK0 : 0 ≤ K)
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
      (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ :=
    hm₁.add hm₂
  have hpoint : ∀ z : ℝ × V,
      ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ≤
        ENNReal.ofReal K *
          (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
    intro z
    have hreal : ‖B z (d₁ z) (d₂ z)‖ ≤
        K * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2) := by
      exact (norm_bilinear_apply_le_norm_mul_add_sq (B z) (d₁ z) (d₂ z)).trans
        (mul_le_mul_of_nonneg_right (hK z)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    calc
      ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖
          ≤ ENNReal.ofReal (K * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal K *
            (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
        rw [ENNReal.ofReal_mul hK0,
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  change (∫⁻ z, ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ∂μ) ≤
    (ENNReal.ofReal K * (C₁ + C₂)) *
      ENNReal.ofReal (R ^ Module.finrank ℝ V)
  calc
    (∫⁻ z, ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal K *
            (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) ∂μ :=
      lintegral_mono hpoint
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
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
      ring

omit [NormedSpace ℝ F] in
theorem SourceCarlesonBound.add {T : ℝ} {C₁ C₂ : ℝ≥0∞}
    {f₁ f₂ : ℝ × V → F}
    (h₁ : SourceCarlesonBound T C₁ f₁) (h₂ : SourceCarlesonBound T C₂ f₂) :
    SourceCarlesonBound T (C₁ + C₂) (fun z ↦ f₁ z + f₂ z) := by
  refine ⟨h₁.ae.add h₂.ae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (spaceTimeVolume : Measure (ℝ × V)).restrict (forwardParabolicCylinder x R)
  have hm₁ : AEMeasurable (fun z ↦ ENNReal.ofReal ‖f₁ z‖) μ :=
    (h₁.ae.norm.aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have hpoint : ∀ z : ℝ × V,
      ENNReal.ofReal ‖f₁ z + f₂ z‖ ≤
        ENNReal.ofReal ‖f₁ z‖ + ENNReal.ofReal ‖f₂ z‖ := by
    intro z
    exact (ENNReal.ofReal_le_ofReal (norm_add_le (f₁ z) (f₂ z))).trans_eq
      (ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _))
  change (∫⁻ z, ENNReal.ofReal ‖f₁ z + f₂ z‖ ∂μ) ≤
    (C₁ + C₂) * ENNReal.ofReal (R ^ Module.finrank ℝ V)
  calc
    (∫⁻ z, ENNReal.ofReal ‖f₁ z + f₂ z‖ ∂μ)
        ≤ ∫⁻ z, ENNReal.ofReal ‖f₁ z‖ + ENNReal.ofReal ‖f₂ z‖ ∂μ :=
      lintegral_mono hpoint
    _ = sourceCarlesonMass f₁ x R + sourceCarlesonMass f₂ x R := by
      rw [lintegral_add_left' hm₁]
      rfl
    _ ≤ C₁ * ENNReal.ofReal (R ^ Module.finrank ℝ V) +
          C₂ * ENNReal.ofReal (R ^ Module.finrank ℝ V) :=
      add_le_add (h₁.bound x R hR hRT) (h₂.bound x R hR hRT)
    _ = (C₁ + C₂) * ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
      ring

end Bilinear

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
