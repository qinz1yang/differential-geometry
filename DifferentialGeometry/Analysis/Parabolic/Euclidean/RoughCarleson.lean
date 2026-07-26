import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# A rough parabolic Carleson norm

The regularizing Ricci--DeTurck fixed-point space cannot ask for a uniformly
bounded spatial derivative at the initial time: its input metric is only
continuous.  The scale-invariant replacement is the space--time estimate

`integral_(0,R^2) integral_(B(x,R)) |Du|^2 <= C R^n`.

This file records that estimate as `GradCarl` and proves the basic product
fact needed by the divergence refold of the quasilinear principal term.  A
bounded bilinear expression in two Carleson-controlled gradients is a
Carleson-controlled `L^1` source.  Thus the compensating
`DA(u)[Du] Dw` term is retained rather than hidden behind a nonexistent
initial-slice derivative bound.
-/

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

/-- The forward parabolic cylinder `(0,R^2] x B(x,R)`. -/
def paraCyl (x : V) (R : ℝ) : Set (ℝ × V) :=
  Set.Ioc 0 (R ^ 2) ×ˢ Metric.ball x R

/-- Product Lebesgue measure on time and a Euclidean model space. -/
def stVolume : Measure (ℝ × V) :=
  (volume : Measure ℝ).prod (volume : Measure V)

end Cylinders

section Masses

variable {V G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G]
  [NormedAddCommGroup F]

/-- Space--time `L^2` mass of a gradient-like field on a parabolic cylinder. -/
def gradMass (d : ℝ × V → G) (x : V) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paraCyl x R, ENNReal.ofReal (‖d z‖ ^ 2) ∂(stVolume : Measure (ℝ × V))

/-- Space--time `L^1` mass of a source on a parabolic cylinder. -/
def srcMass (f : ℝ × V → F) (x : V) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paraCyl x R, ENNReal.ofReal ‖f z‖ ∂(stVolume : Measure (ℝ × V))

/-- Scale-invariant Carleson control of a gradient-like field up to time `T`.

The explicit a.e.-strong measurability field is part of the analytic data; no
measurability or derivative regularity at the initial slice is inferred. -/
structure GradCarl (T : ℝ) (C : ℝ≥0∞) (d : ℝ × V → G) : Prop where
  ae : AEStronglyMeasurable d (stVolume : Measure (ℝ × V))
  bound : ∀ x R, 0 < R → R ^ 2 ≤ T →
    gradMass d x R ≤ C * ENNReal.ofReal (R ^ Module.finrank ℝ V)

/-- Scale-invariant Carleson control of an `L^1` source up to time `T`. -/
structure SrcCarl (T : ℝ) (C : ℝ≥0∞) (f : ℝ × V → F) : Prop where
  ae : AEStronglyMeasurable f (stVolume : Measure (ℝ × V))
  bound : ∀ x R, 0 < R → R ^ 2 ≤ T →
    srcMass f x R ≤ C * ENNReal.ofReal (R ^ Module.finrank ℝ V)

/-- Uniform positive-time `C⁰` control of a space--time path. -/
def PathSup (T A : ℝ) (u : ℝ × V → G) : Prop :=
  ∀ t x, 0 < t → t ≤ T → ‖u (t, x)‖ ≤ A

/-- The scale-invariant pointwise part of the rough gradient norm. -/
def GradWt (T A : ℝ) (d : ℝ × V → G) : Prop :=
  ∀ t x, 0 < t → t ≤ T → Real.sqrt t * ‖d (t, x)‖ ≤ A

/-- The scale-invariant pointwise part of the rough quadratic-source norm. -/
def SrcWt (T A : ℝ) (f : ℝ × V → F) : Prop :=
  ∀ t x, 0 < t → t ≤ T → t * ‖f (t, x)‖ ≤ A

/-- The three components of the rough solution ball: `C⁰`, weighted
pointwise gradient, and gradient Carleson mass.  The derivative is supplied
as explicit data, so this definition does not manufacture a derivative at
`t = 0`. -/
def InRoughPath (T A₀ A₁ : ℝ) (C₁ : ℝ≥0∞)
    (u : ℝ × V → F) (d : ℝ × V → G) : Prop :=
  PathSup T A₀ u ∧ GradWt T A₁ d ∧ GradCarl T C₁ d

/-- The two components of the rough nondifferentiated source class. -/
def InRoughSrc (T A : ℝ) (C : ℝ≥0∞) (f : ℝ × V → F) : Prop :=
  SrcWt T A f ∧ SrcCarl T C f

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
/-- A uniformly small space--time dependent linear coefficient preserves the
weighted gradient class, with its operator bound appearing as the explicit
small factor. -/
theorem linWt_of_bound (A : ℝ × V → G →L[ℝ] F)
    {T K C : ℝ} {d : ℝ × V → G}
    (hK : ∀ z, ‖A z‖ ≤ K) (hK0 : 0 ≤ K) (hd : GradWt T C d) :
    GradWt T (K * C) (fun z ↦ A z (d z)) := by
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

/-- The local `L²` Carleson counterpart of `linWt_of_bound`.  Measurability
of the realized flux is explicit because a merely pointwise operator field
need not be measurable. -/
theorem linCarl_of_bound (A : ℝ × V → G →L[ℝ] F)
    {T K : ℝ} {C : ℝ≥0∞} {d : ℝ × V → G}
    (hK : ∀ z, ‖A z‖ ≤ K) (hK0 : 0 ≤ K)
    (hae : AEStronglyMeasurable (fun z ↦ A z (d z))
      (stVolume : Measure (ℝ × V)))
    (hd : GradCarl T C d) :
    GradCarl T (ENNReal.ofReal (K ^ 2) * C) (fun z ↦ A z (d z)) := by
  refine ⟨hae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (stVolume : Measure (ℝ × V)).restrict (paraCyl x R)
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
    _ = ENNReal.ofReal (K ^ 2) * gradMass d x R := by
      rw [lintegral_const_mul'' _ hmd]
      rfl
    _ ≤ ENNReal.ofReal (K ^ 2) *
          (C * ENNReal.ofReal (R ^ Module.finrank ℝ V)) :=
      mul_le_mul_right (hd.bound x R hR hRT) _
    _ = (ENNReal.ofReal (K ^ 2) * C) *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
      ring

/-- A bounded bilinear map is controlled by the sum of the two squared input
norms.  The harmless factor `2` saved by Young's sharper inequality is not
needed for the fixed-point norm. -/
theorem bilin_sq_bound (B : G →L[ℝ] H →L[ℝ] F) (a : G) (b : H) :
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
/-- The weighted pointwise product estimate, allowing a space--time dependent
bilinear coefficient with a uniform operator bound. -/
theorem bilinWt_of_bound (B : ℝ × V → G →L[ℝ] H →L[ℝ] F)
    {T K A₁ A₂ : ℝ} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hK : ∀ z, ‖B z‖ ≤ K) (hK0 : 0 ≤ K) (hA₁ : 0 ≤ A₁)
    (h₁ : GradWt T A₁ d₁) (h₂ : GradWt T A₂ d₂) :
    SrcWt T (K * A₁ * A₂) (fun z ↦ B z (d₁ z) (d₂ z)) := by
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
/-- Constant-coefficient specialization of `bilinWt_of_bound`. -/
theorem bilinWt (B : G →L[ℝ] H →L[ℝ] F)
    {T A₁ A₂ : ℝ} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hA₁ : 0 ≤ A₁) (h₁ : GradWt T A₁ d₁) (h₂ : GradWt T A₂ d₂) :
    SrcWt T (‖B‖ * A₁ * A₂) (fun z ↦ B (d₁ z) (d₂ z)) := by
  exact bilinWt_of_bound (fun _ ↦ B) (fun _ ↦ le_rfl) (norm_nonneg B) hA₁ h₁ h₂

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedSpace ℝ F] in
/-- Addition in the weighted pointwise source class. -/
theorem srcWt_add {T A₁ A₂ : ℝ} {f₁ f₂ : ℝ × V → F}
    (h₁ : SrcWt T A₁ f₁) (h₂ : SrcWt T A₂ f₂) :
    SrcWt T (A₁ + A₂) (fun z ↦ f₁ z + f₂ z) := by
  intro t x ht hT
  calc
    t * ‖f₁ (t, x) + f₂ (t, x)‖
        ≤ t * (‖f₁ (t, x)‖ + ‖f₂ (t, x)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) ht.le
    _ = t * ‖f₁ (t, x)‖ + t * ‖f₂ (t, x)‖ := by ring
    _ ≤ A₁ + A₂ := add_le_add (h₁ t x ht hT) (h₂ t x ht hT)

/-- The compensating quadratic-gradient term belongs to the rough source
Carleson class.  This is the product estimate used after the exact divergence
refold of the inverse-metric variation times `D²u`. -/
theorem bilinCarl (B : G →L[ℝ] H →L[ℝ] F)
    {T : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (h₁ : GradCarl T C₁ d₁) (h₂ : GradCarl T C₂ d₂) :
    SrcCarl T (ENNReal.ofReal ‖B‖ * (C₁ + C₂)) (fun z ↦ B (d₁ z) (d₂ z)) := by
  refine ⟨?_, ?_⟩
  · have hB : Continuous (fun p : G × H ↦ B p.1 p.2) :=
      (B.continuous.comp continuous_fst).clm_apply continuous_snd
    exact hB.comp_aestronglyMeasurable (h₁.ae.prodMk h₂.ae)
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (stVolume : Measure (ℝ × V)).restrict (paraCyl x R)
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
          ENNReal.ofReal_le_ofReal (bilin_sq_bound B (d₁ z) (d₂ z))
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
      _ = ENNReal.ofReal ‖B‖ * (gradMass d₁ x R + gradMass d₂ x R) := by
        rfl
      _ ≤ ENNReal.ofReal ‖B‖ *
            ((C₁ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) +
              C₂ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) := by
        gcongr
        exact h₁.bound x R hR hRT
        exact h₂.bound x R hR hRT
      _ = (ENNReal.ofReal ‖B‖ * (C₁ + C₂)) *
            ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
        ring

/-- Variable-coefficient version of `bilinCarl`.  The realized source is
required to be measurable explicitly; the coefficient field itself may be
supplied by a geometric chart construction. -/
theorem bilinCarl_bound (B : ℝ × V → G →L[ℝ] H →L[ℝ] F)
    {T K : ℝ} {C₁ C₂ : ℝ≥0∞} {d₁ : ℝ × V → G} {d₂ : ℝ × V → H}
    (hK : ∀ z, ‖B z‖ ≤ K) (hK0 : 0 ≤ K)
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
      (fun z ↦ ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) μ :=
    hm₁.add hm₂
  have hpoint : ∀ z : ℝ × V,
      ENNReal.ofReal ‖B z (d₁ z) (d₂ z)‖ ≤
        ENNReal.ofReal K *
          (ENNReal.ofReal (‖d₁ z‖ ^ 2) + ENNReal.ofReal (‖d₂ z‖ ^ 2)) := by
    intro z
    have hreal : ‖B z (d₁ z) (d₂ z)‖ ≤
        K * (‖d₁ z‖ ^ 2 + ‖d₂ z‖ ^ 2) := by
      exact (bilin_sq_bound (B z) (d₁ z) (d₂ z)).trans
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
    _ = ENNReal.ofReal K * (gradMass d₁ x R + gradMass d₂ x R) := by
      rw [lintegral_const_mul'' _ hmadd, lintegral_add_left' hm₁]
      rfl
    _ ≤ ENNReal.ofReal K *
          ((C₁ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) +
            C₂ * ENNReal.ofReal (R ^ Module.finrank ℝ V)) := by
      gcongr
      exact h₁.bound x R hR hRT
      exact h₂.bound x R hR hRT
    _ = (ENNReal.ofReal K * (C₁ + C₂)) *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
      ring

omit [NormedSpace ℝ F] in
/-- Addition in the rough `L¹` source Carleson class. -/
theorem srcCarl_add {T : ℝ} {C₁ C₂ : ℝ≥0∞}
    {f₁ f₂ : ℝ × V → F}
    (h₁ : SrcCarl T C₁ f₁) (h₂ : SrcCarl T C₂ f₂) :
    SrcCarl T (C₁ + C₂) (fun z ↦ f₁ z + f₂ z) := by
  refine ⟨h₁.ae.add h₂.ae, ?_⟩
  intro x R hR hRT
  let μ : Measure (ℝ × V) :=
    (stVolume : Measure (ℝ × V)).restrict (paraCyl x R)
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
    _ = srcMass f₁ x R + srcMass f₂ x R := by
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
