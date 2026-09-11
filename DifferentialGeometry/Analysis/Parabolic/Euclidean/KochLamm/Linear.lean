import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Spaces

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E F : Type*}
  [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eLpNorm_clm_le (A : X → E →L[ℝ] F) (d : X → E)
    (ε : ℝ≥0) (hA : ∀ x, ‖A x‖ ≤ (ε : ℝ)) (p : ℝ≥0∞) (μ : Measure X) :
    eLpNorm (fun x => A x (d x)) p μ ≤
      (ε : ℝ≥0∞) * eLpNorm d p μ := by
  calc
    eLpNorm (fun x => A x (d x)) p μ ≤
        eLpNorm (fun x => (ε : ℝ) • d x) p μ := by
      apply eLpNorm_mono
      intro x
      calc
        ‖A x (d x)‖ ≤ ‖A x‖ * ‖d x‖ := (A x).le_opNorm _
        _ ≤ (ε : ℝ) * ‖d x‖ :=
          mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)
        _ = ‖(ε : ℝ) • d x‖ := by
          rw [norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg ε)]
    _ = (ε : ℝ≥0∞) * eLpNorm d p μ := by
      change eLpNorm ((ε : ℝ) • d) p μ = _
      rw [eLpNorm_const_smul]
      simp

section KochLamm

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem KochLammSourceOne.clm_apply {T : ℝ} {A₂ Aₚ ε : ℝ≥0}
    (A : ℝ × V → E →L[ℝ] F) (d : ℝ × V → E)
    (hA : ∀ z, ‖A z‖ ≤ (ε : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => A z (d z))
      (kochLammVolume : Measure (ℝ × V)))
    (hd : KochLammSourceOne T A₂ Aₚ d) :
    KochLammSourceOne T (ε * A₂) (ε * Aₚ) (fun z => A z (d z)) := by
  refine ⟨hmeas, ?_, ?_⟩
  · intro x R hR hRT
    calc
      kochLammL2Scale (V := V) R *
          eLpNorm (fun z => A z (d z)) 2
            ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R)) ≤
        kochLammL2Scale (V := V) R *
          ((ε : ℝ≥0∞) * eLpNorm d 2
            ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R))) :=
          mul_le_mul_right (eLpNorm_clm_le A d ε hA 2 _) _
      _ = (ε : ℝ≥0∞) *
          (kochLammL2Scale (V := V) R *
            eLpNorm d 2
              ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammCylinder x R))) := by
        ac_rfl
      _ ≤ (ε : ℝ≥0∞) * (A₂ : ℝ≥0∞) :=
        mul_le_mul_right (hd.local_l2 x R hR hRT) _
      _ = ((ε * A₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast
  · intro x R hR hRT
    calc
      kochLammLpScale (V := V) R *
          eLpNorm (fun z => A z (d z)) (kochLammP V)
            ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R)) ≤
        kochLammLpScale (V := V) R *
          ((ε : ℝ≥0∞) * eLpNorm d (kochLammP V)
            ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R))) :=
          mul_le_mul_right (eLpNorm_clm_le A d ε hA (kochLammP V) _) _
      _ = (ε : ℝ≥0∞) *
          (kochLammLpScale (V := V) R *
            eLpNorm d (kochLammP V)
              ((kochLammVolume : Measure (ℝ × V)).restrict (kochLammLateCylinder x R))) := by
        ac_rfl
      _ ≤ (ε : ℝ≥0∞) * (Aₚ : ℝ≥0∞) :=
        mul_le_mul_right (hd.late_lp x R hR hRT) _
      _ = ((ε * Aₚ : ℝ≥0) : ℝ≥0∞) := by norm_cast

theorem kochLammPath_map_bound {T : ℝ} {A₀ A₂ Aₚ ε : ℝ≥0}
    (A : ℝ × V → E →L[ℝ] F) (u : ℝ × V → F) (d : ℝ × V → E)
    (hA : ∀ z, ‖A z‖ ≤ (ε : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => A z (d z))
      (kochLammVolume : Measure (ℝ × V)))
    (hd : KochLammPath T A₀ A₂ Aₚ u d) :
    KochLammSourceOne T (ε * A₂) (ε * Aₚ) (fun z => A z (d z)) := by
  apply KochLammSourceOne.clm_apply A d hA hmeas
  exact ⟨hd.grad_ae, hd.grad_l2, hd.grad_lp⟩

end KochLamm

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
