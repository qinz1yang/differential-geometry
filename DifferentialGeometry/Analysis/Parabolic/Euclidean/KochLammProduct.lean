import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Quadratic products in the Koch--Lamm source space

The quadratic-gradient term belongs to the ordinary Koch--Lamm source class:
the local `L² × L²` product gives the `L¹` arm, while the late
`L^(n+4) × L^(n+4)` product gives the `L^((n+4)/2)` arm.  Both scale factors
cancel exactly.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The local `L¹` source scale is the square of the local `L²` flux scale. -/
theorem klL1_eq_L2_sq {R : ℝ} (hR : 0 < R) :
    klL1Scale (V := V) R = klL2Scale (V := V) R ^ 2 := by
  unfold klL1Scale klL1ScaleR klL2Scale klL2ScaleR
  have hre :
      Real.rpow R (-klDim V) =
        (Real.rpow R (-klDim V / 2)) ^ 2 := by
    calc
      Real.rpow R (-klDim V) =
          Real.rpow R ((-klDim V / 2) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow R (-klDim V / 2)) (2 : ℝ) :=
        Real.rpow_mul hR.le _ _
      _ = (Real.rpow R (-klDim V / 2)) ^ 2 :=
        Real.rpow_natCast _ 2
  rw [hre]
  exact ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _) 2

omit [MeasurableSpace V] [BorelSpace V] in
/-- The late ordinary-source scale is the square of the late flux scale. -/
theorem klLq_eq_Lp_sq {R : ℝ} (hR : 0 < R) :
    klLqScale (V := V) R = klLpScale (V := V) R ^ 2 := by
  unfold klLqScale klLqScaleR klLpScale klLpScaleR
  have hre :
      Real.rpow R (4 / (klDim V + 4)) =
        (Real.rpow R (2 / (klDim V + 4))) ^ 2 := by
    calc
      Real.rpow R (4 / (klDim V + 4)) =
          Real.rpow R ((2 / (klDim V + 4)) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow R (2 / (klDim V + 4))) (2 : ℝ) :=
        Real.rpow_mul hR.le _ _
      _ = (Real.rpow R (2 / (klDim V + 4))) ^ 2 :=
        Real.rpow_natCast _ 2
  rw [hre]
  exact ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _) 2

omit [MeasurableSpace V] [BorelSpace V] in
/-- The exponents `n+4`, `n+4`, and `(n+4)/2` form a Hölder triple. -/
theorem klP_holder :
    ENNReal.HolderTriple (klP V) (klP V) (klQ V) := by
  let n4 : ℕ := Module.finrank ℝ V + 4
  let p : ℝ := n4
  have hp : 0 < p := by
    dsimp [p, n4]
    positivity
  have hr : Real.HolderTriple p p (p / 2) := by
    refine ⟨?_, hp, hp⟩
    field_simp [hp.ne']
    norm_num
  have hof : ENNReal.ofReal p = klP V := by
    change ENNReal.ofReal (n4 : ℝ) = klP V
    rw [ENNReal.ofReal_natCast]
    rfl
  have hofq : ENNReal.ofReal (p / 2) = klQ V := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), hof]
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    rfl
  have he := Real.HolderTriple.ennrealOfReal hr
  rw [hof, hofq] at he
  exact he

section Product

variable {X E G F : Type*}
  [MeasurableSpace X]
  {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Hölder's inequality for a space-dependent uniformly bounded bilinear
coefficient. -/
theorem eLpNorm_bilin_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (B : X → E →L[ℝ] G →L[ℝ] F) (d₁ : X → E) (d₂ : X → G)
    (K : ℝ≥0) (hK : ∀ x, ‖B x‖ ≤ (K : ℝ))
    (h₁ : AEStronglyMeasurable d₁ μ) (h₂ : AEStronglyMeasurable d₂ μ) :
    eLpNorm (fun x => B x (d₁ x) (d₂ x)) r μ ≤
      (K : ℝ≥0∞) * eLpNorm d₁ p μ * eLpNorm d₂ q μ := by
  have hpoint : ∀ x,
      ‖B x (d₁ x) (d₂ x)‖ ≤ (K : ℝ) * (‖d₁ x‖ * ‖d₂ x‖) := by
    intro x
    calc
      ‖B x (d₁ x) (d₂ x)‖ ≤ ‖B x (d₁ x)‖ * ‖d₂ x‖ :=
        (B x (d₁ x)).le_opNorm _
      _ ≤ (‖B x‖ * ‖d₁ x‖) * ‖d₂ x‖ :=
        mul_le_mul_of_nonneg_right ((B x).le_opNorm _) (norm_nonneg _)
      _ ≤ ((K : ℝ) * ‖d₁ x‖) * ‖d₂ x‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)) (norm_nonneg _)
      _ = (K : ℝ) * (‖d₁ x‖ * ‖d₂ x‖) := by ring
  have hmono :
      eLpNorm (fun x => B x (d₁ x) (d₂ x)) r μ ≤
        eLpNorm (fun x => (K : ℝ) * (‖d₁ x‖ * ‖d₂ x‖)) r μ := by
    apply eLpNorm_mono
    intro x
    simpa [Real.norm_of_nonneg
      (mul_nonneg (NNReal.coe_nonneg K)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))] using hpoint x
  have hscale :
      eLpNorm (fun x => (K : ℝ) * (‖d₁ x‖ * ‖d₂ x‖)) r μ =
        (K : ℝ≥0∞) * eLpNorm (fun x => ‖d₁ x‖ * ‖d₂ x‖) r μ := by
    change eLpNorm ((K : ℝ) • (fun x => ‖d₁ x‖ * ‖d₂ x‖)) r μ = _
    rw [eLpNorm_const_smul]
    simp
  have hhold :
      eLpNorm (fun x => ‖d₁ x‖ * ‖d₂ x‖) r μ ≤
        eLpNorm d₁ p μ * eLpNorm d₂ q μ := by
    have h₁n := h₁.norm
    have h₂n := h₂.norm
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (μ := μ) (p := p) (q := q) (r := r)
      (f := fun x => ‖d₁ x‖) (g := fun x => ‖d₂ x‖)
      h₁n h₂n (fun a b : ℝ => a * b) 1
      (ae_of_all μ fun x => by
        simp)
    simpa only [eLpNorm_norm, ENNReal.coe_one, one_mul] using h
  calc
    eLpNorm (fun x => B x (d₁ x) (d₂ x)) r μ
        ≤ eLpNorm (fun x => (K : ℝ) * (‖d₁ x‖ * ‖d₂ x‖)) r μ := hmono
    _ = (K : ℝ≥0∞) * eLpNorm (fun x => ‖d₁ x‖ * ‖d₂ x‖) r μ := hscale
    _ ≤ (K : ℝ≥0∞) *
          (eLpNorm d₁ p μ * eLpNorm d₂ q μ) :=
      mul_le_mul_right hhold _
    _ = (K : ℝ≥0∞) * eLpNorm d₁ p μ * eLpNorm d₂ q μ := by ring

end Product

section KochLammProduct

variable {E G F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product of two Koch--Lamm fluxes is an ordinary Koch--Lamm source. -/
theorem klBilin_source {T : ℝ}
    {A₂₁ Aₚ₁ A₂₂ Aₚ₂ K : ℝ≥0}
    (B : ℝ × V → E →L[ℝ] G →L[ℝ] F)
    (d₁ : ℝ × V → E) (d₂ : ℝ × V → G)
    (hK : ∀ z, ‖B z‖ ≤ (K : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => B z (d₁ z) (d₂ z))
      (klVolume : Measure (ℝ × V)))
    (h₁ : KLSource1 T A₂₁ Aₚ₁ d₁)
    (h₂ : KLSource1 T A₂₂ Aₚ₂ d₂) :
    KLSource0 T (K * A₂₁ * A₂₂) (K * Aₚ₁ * Aₚ₂)
      (fun z => B z (d₁ z) (d₂ z)) := by
  letI : ENNReal.HolderTriple 2 2 1 := by
    constructor
    rw [inv_one, ENNReal.inv_two_add_inv_two]
  letI : ENNReal.HolderTriple (klP V) (klP V) (klQ V) :=
    klP_holder (V := V)
  refine ⟨hmeas, ?_, ?_⟩
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (klVolume : Measure (ℝ × V)).restrict (klCyl x R)
    have hp := eLpNorm_bilin_le (p := 2) (q := 2) (r := 1)
      B d₁ d₂ K hK
      (h₁.ae.mono_measure Measure.restrict_le_self)
      (h₂.ae.mono_measure Measure.restrict_le_self :
        AEStronglyMeasurable d₂ μ)
    change klL1Scale (V := V) R *
        eLpNorm (fun z => B z (d₁ z) (d₂ z)) 1 μ ≤
      ((K * A₂₁ * A₂₂ : ℝ≥0) : ℝ≥0∞)
    calc
      klL1Scale (V := V) R *
          eLpNorm (fun z => B z (d₁ z) (d₂ z)) 1 μ ≤
        klL1Scale (V := V) R *
          ((K : ℝ≥0∞) * eLpNorm d₁ 2 μ * eLpNorm d₂ 2 μ) :=
        mul_le_mul_right hp _
      _ = (K : ℝ≥0∞) *
          (klL2Scale (V := V) R * eLpNorm d₁ 2 μ) *
          (klL2Scale (V := V) R * eLpNorm d₂ 2 μ) := by
        rw [klL1_eq_L2_sq (V := V) hR]
        ring
      _ ≤ (K : ℝ≥0∞) * (A₂₁ : ℝ≥0∞) * (A₂₂ : ℝ≥0∞) := by
        gcongr
        · exact h₁.local_l2 x R hR hRT
        · exact h₂.local_l2 x R hR hRT
      _ = ((K * A₂₁ * A₂₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)
    have hp := eLpNorm_bilin_le
      (p := klP V) (q := klP V) (r := klQ V)
      B d₁ d₂ K hK
      (h₁.ae.mono_measure Measure.restrict_le_self)
      (h₂.ae.mono_measure Measure.restrict_le_self :
        AEStronglyMeasurable d₂ μ)
    change klLqScale (V := V) R *
        eLpNorm (fun z => B z (d₁ z) (d₂ z)) (klQ V) μ ≤
      ((K * Aₚ₁ * Aₚ₂ : ℝ≥0) : ℝ≥0∞)
    calc
      klLqScale (V := V) R *
          eLpNorm (fun z => B z (d₁ z) (d₂ z)) (klQ V) μ ≤
        klLqScale (V := V) R *
          ((K : ℝ≥0∞) * eLpNorm d₁ (klP V) μ *
            eLpNorm d₂ (klP V) μ) := mul_le_mul_right hp _
      _ = (K : ℝ≥0∞) *
          (klLpScale (V := V) R * eLpNorm d₁ (klP V) μ) *
          (klLpScale (V := V) R * eLpNorm d₂ (klP V) μ) := by
        rw [klLq_eq_Lp_sq (V := V) hR]
        ring
      _ ≤ (K : ℝ≥0∞) * (Aₚ₁ : ℝ≥0∞) * (Aₚ₂ : ℝ≥0∞) := by
        gcongr
        · exact h₁.late_lp x R hR hRT
        · exact h₂.late_lp x R hR hRT
      _ = ((K * Aₚ₁ * Aₚ₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast

/-- A bounded quadratic expression in the gradient fields of two
Koch--Lamm paths is an ordinary Koch--Lamm source. -/
theorem klPathBilin_source {T : ℝ}
    {A₀₁ A₂₁ Aₚ₁ A₀₂ A₂₂ Aₚ₂ K : ℝ≥0}
    (B : ℝ × V → E →L[ℝ] G →L[ℝ] F)
    (u₁ d₁ : ℝ × V → E) (u₂ d₂ : ℝ × V → G)
    (hK : ∀ z, ‖B z‖ ≤ (K : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => B z (d₁ z) (d₂ z))
      (klVolume : Measure (ℝ × V)))
    (h₁ : KLPath T A₀₁ A₂₁ Aₚ₁ u₁ d₁)
    (h₂ : KLPath T A₀₂ A₂₂ Aₚ₂ u₂ d₂) :
    KLSource0 T (K * A₂₁ * A₂₂) (K * Aₚ₁ * Aₚ₂)
      (fun z => B z (d₁ z) (d₂ z)) := by
  apply klBilin_source B d₁ d₂ hK hmeas
  · exact ⟨h₁.grad_ae, h₁.grad_l2, h₁.grad_lp⟩
  · exact ⟨h₂.grad_ae, h₂.grad_l2, h₂.grad_lp⟩

end KochLammProduct

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
