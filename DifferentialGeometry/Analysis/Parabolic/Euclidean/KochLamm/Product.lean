import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Spaces
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Scaling

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem kochLammL1_eq_L2_sq {R : ℝ} (hR : 0 < R) :
    kochLammL1Scale (V := V) R = kochLammL2Scale (V := V) R ^ 2 := by
  unfold kochLammL1Scale kochLammL1ScaleR kochLammL2Scale kochLammL2ScaleR
  have hre :
      R ^ (-kochLammDim V) = (R ^ (-kochLammDim V / 2)) ^ 2 := by
    calc
      Real.rpow R (-kochLammDim V) =
          Real.rpow R ((-kochLammDim V / 2) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow R (-kochLammDim V / 2)) (2 : ℝ) :=
        Real.rpow_mul hR.le _ _
      _ = (Real.rpow R (-kochLammDim V / 2)) ^ 2 :=
        Real.rpow_natCast _ 2
  rw [hre]
  exact ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _) 2

omit [FiniteDimensional ℝ V] in
theorem kochLammLq_eq_Lp_sq {R : ℝ} (hR : 0 < R) :
    kochLammLqScale (V := V) R = kochLammLpScale (V := V) R ^ 2 := by
  unfold kochLammLqScale kochLammLqScaleR kochLammLpScale kochLammLpScaleR
  have hre :
      R ^ (4 / (kochLammDim V + 4)) = (R ^ (2 / (kochLammDim V + 4))) ^ 2 := by
    calc
      Real.rpow R (4 / (kochLammDim V + 4)) =
          Real.rpow R ((2 / (kochLammDim V + 4)) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow R (2 / (kochLammDim V + 4))) (2 : ℝ) :=
        Real.rpow_mul hR.le _ _
      _ = (Real.rpow R (2 / (kochLammDim V + 4))) ^ 2 :=
        Real.rpow_natCast _ 2
  rw [hre]
  exact ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _) 2

omit [FiniteDimensional ℝ V] in
theorem kochLammP_holderTriple :
    ENNReal.HolderTriple (kochLammP V) (kochLammP V) (kochLammQ V) := by
  let n4 : ℕ := Module.finrank ℝ V + 4
  let p : ℝ := n4
  have hp : 0 < p := by
    dsimp [p, n4]
    positivity
  have hr : Real.HolderTriple p p (p / 2) := by
    refine ⟨?_, hp, hp⟩
    field_simp [hp.ne']
    norm_num
  have hof : ENNReal.ofReal p = kochLammP V := by
    change ENNReal.ofReal (n4 : ℝ) = kochLammP V
    rw [ENNReal.ofReal_natCast]
    rfl
  have hofq : ENNReal.ofReal (p / 2) = kochLammQ V := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), hof]
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    rfl
  have he := Real.HolderTriple.ennrealOfReal hr
  rw [hof, hofq] at he
  exact he

end Scaling

section Product

variable {X E G F : Type*}
  [MeasurableSpace X]
  {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

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

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {E G F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem kochLammBilin_source {T : ℝ}
    {A₂₁ Aₚ₁ A₂₂ Aₚ₂ K : ℝ≥0}
    (B : ℝ × V → E →L[ℝ] G →L[ℝ] F)
    (d₁ : ℝ × V → E) (d₂ : ℝ × V → G)
    (hK : ∀ z, ‖B z‖ ≤ (K : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => B z (d₁ z) (d₂ z))
      (kochLammVolume : Measure (ℝ × V)))
    (h₁ : KochLammSourceOne T A₂₁ Aₚ₁ d₁)
    (h₂ : KochLammSourceOne T A₂₂ Aₚ₂ d₂) :
    KochLammSourceZero T (K * A₂₁ * A₂₂) (K * Aₚ₁ * Aₚ₂)
      (fun z => B z (d₁ z) (d₂ z)) := by
  let : ENNReal.HolderTriple 2 2 1 := by
    constructor
    rw [inv_one, ENNReal.inv_two_add_inv_two]
  let : ENNReal.HolderTriple (kochLammP V) (kochLammP V) (kochLammQ V) :=
    kochLammP_holderTriple (V := V)
  refine ⟨hmeas, ?_, ?_⟩
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R)
    have hp := eLpNorm_bilin_le (p := 2) (q := 2) (r := 1)
      B d₁ d₂ K hK
      (h₁.ae.mono_measure Measure.restrict_le_self)
      (h₂.ae.mono_measure Measure.restrict_le_self :
        AEStronglyMeasurable d₂ μ)
    change kochLammL1Scale (V := V) R *
        eLpNorm (fun z => B z (d₁ z) (d₂ z)) 1 μ ≤
      ((K * A₂₁ * A₂₂ : ℝ≥0) : ℝ≥0∞)
    calc
      kochLammL1Scale (V := V) R *
          eLpNorm (fun z => B z (d₁ z) (d₂ z)) 1 μ ≤
        kochLammL1Scale (V := V) R *
          ((K : ℝ≥0∞) * eLpNorm d₁ 2 μ * eLpNorm d₂ 2 μ) :=
        mul_le_mul_right hp _
      _ = (K : ℝ≥0∞) *
          (kochLammL2Scale (V := V) R * eLpNorm d₁ 2 μ) *
          (kochLammL2Scale (V := V) R * eLpNorm d₂ 2 μ) := by
        rw [kochLammL1_eq_L2_sq (V := V) hR]
        ring
      _ ≤ (K : ℝ≥0∞) * (A₂₁ : ℝ≥0∞) * (A₂₂ : ℝ≥0∞) := by
        gcongr
        · exact h₁.local_l2 x R hR hRT
        · exact h₂.local_l2 x R hR hRT
      _ = ((K * A₂₁ * A₂₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast
  · intro x R hR hRT
    let μ : Measure (ℝ × V) :=
      (kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)
    have hp := eLpNorm_bilin_le
      (p := kochLammP V) (q := kochLammP V) (r := kochLammQ V)
      B d₁ d₂ K hK
      (h₁.ae.mono_measure Measure.restrict_le_self)
      (h₂.ae.mono_measure Measure.restrict_le_self :
        AEStronglyMeasurable d₂ μ)
    change kochLammLqScale (V := V) R *
        eLpNorm (fun z => B z (d₁ z) (d₂ z)) (kochLammQ V) μ ≤
      ((K * Aₚ₁ * Aₚ₂ : ℝ≥0) : ℝ≥0∞)
    calc
      kochLammLqScale (V := V) R *
          eLpNorm (fun z => B z (d₁ z) (d₂ z)) (kochLammQ V) μ ≤
        kochLammLqScale (V := V) R *
          ((K : ℝ≥0∞) * eLpNorm d₁ (kochLammP V) μ *
            eLpNorm d₂ (kochLammP V) μ) := mul_le_mul_right hp _
      _ = (K : ℝ≥0∞) *
          (kochLammLpScale (V := V) R * eLpNorm d₁ (kochLammP V) μ) *
          (kochLammLpScale (V := V) R * eLpNorm d₂ (kochLammP V) μ) := by
        rw [kochLammLq_eq_Lp_sq (V := V) hR]
        ring
      _ ≤ (K : ℝ≥0∞) * (Aₚ₁ : ℝ≥0∞) * (Aₚ₂ : ℝ≥0∞) := by
        gcongr
        · exact h₁.late_lp x R hR hRT
        · exact h₂.late_lp x R hR hRT
      _ = ((K * Aₚ₁ * Aₚ₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast

theorem kochLammPathBilin_source {T : ℝ}
    {A₀₁ A₂₁ Aₚ₁ A₀₂ A₂₂ Aₚ₂ K : ℝ≥0}
    (B : ℝ × V → E →L[ℝ] G →L[ℝ] F)
    (u₁ d₁ : ℝ × V → E) (u₂ d₂ : ℝ × V → G)
    (hK : ∀ z, ‖B z‖ ≤ (K : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => B z (d₁ z) (d₂ z))
      (kochLammVolume : Measure (ℝ × V)))
    (h₁ : KochLammPath T A₀₁ A₂₁ Aₚ₁ u₁ d₁)
    (h₂ : KochLammPath T A₀₂ A₂₂ Aₚ₂ u₂ d₂) :
    KochLammSourceZero T (K * A₂₁ * A₂₂) (K * Aₚ₁ * Aₚ₂)
      (fun z => B z (d₁ z) (d₂ z)) := by
  apply kochLammBilin_source B d₁ d₂ hK hmeas
  · exact ⟨h₁.grad_ae, h₁.grad_l2, h₁.grad_lp⟩
  · exact ⟨h₂.grad_ae, h₂.grad_l2, h₂.grad_lp⟩

end KochLammProduct

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
