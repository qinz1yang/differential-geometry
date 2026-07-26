import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces

/-!
# Bounded linear coefficients on Koch--Lamm fluxes

A uniformly bounded linear coefficient preserves both the local `L²` and the
late `L^(n+4)` arms of a Koch--Lamm divergence source.  The norm radius is
multiplied by the coefficient bound, which is the critical small parameter in
the harmonic-map heat-flow principal flux.
-/

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

/-- A pointwise uniformly bounded family of continuous linear maps gives the
same bound on every `eLpNorm`. -/
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

/-- A bounded linear coefficient preserves a Koch--Lamm divergence source,
with both radii multiplied by the coefficient bound. -/
theorem kl1_map_bound {T : ℝ} {A₂ Aₚ ε : ℝ≥0}
    (A : ℝ × V → E →L[ℝ] F) (d : ℝ × V → E)
    (hA : ∀ z, ‖A z‖ ≤ (ε : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => A z (d z))
      (klVolume : Measure (ℝ × V)))
    (hd : KLSource1 T A₂ Aₚ d) :
    KLSource1 T (ε * A₂) (ε * Aₚ) (fun z => A z (d z)) := by
  refine ⟨hmeas, ?_, ?_⟩
  · intro x R hR hRT
    calc
      klL2Scale (V := V) R *
          eLpNorm (fun z => A z (d z)) 2
            ((klVolume : Measure (ℝ × V)).restrict (klCyl x R)) ≤
        klL2Scale (V := V) R *
          ((ε : ℝ≥0∞) * eLpNorm d 2
            ((klVolume : Measure (ℝ × V)).restrict (klCyl x R))) :=
          mul_le_mul_right (eLpNorm_clm_le A d ε hA 2 _) _
      _ = (ε : ℝ≥0∞) *
          (klL2Scale (V := V) R *
            eLpNorm d 2
              ((klVolume : Measure (ℝ × V)).restrict (klCyl x R))) := by
        ac_rfl
      _ ≤ (ε : ℝ≥0∞) * (A₂ : ℝ≥0∞) :=
        mul_le_mul_right (hd.local_l2 x R hR hRT) _
      _ = ((ε * A₂ : ℝ≥0) : ℝ≥0∞) := by norm_cast
  · intro x R hR hRT
    calc
      klLpScale (V := V) R *
          eLpNorm (fun z => A z (d z)) (klP V)
            ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R)) ≤
        klLpScale (V := V) R *
          ((ε : ℝ≥0∞) * eLpNorm d (klP V)
            ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R))) :=
          mul_le_mul_right (eLpNorm_clm_le A d ε hA (klP V) _) _
      _ = (ε : ℝ≥0∞) *
          (klLpScale (V := V) R *
            eLpNorm d (klP V)
              ((klVolume : Measure (ℝ × V)).restrict (klLateCyl x R))) := by
        ac_rfl
      _ ≤ (ε : ℝ≥0∞) * (Aₚ : ℝ≥0∞) :=
        mul_le_mul_right (hd.late_lp x R hR hRT) _
      _ = ((ε * Aₚ : ℝ≥0) : ℝ≥0∞) := by norm_cast

/-- A bounded linear coefficient applied to the gradient field of a
Koch--Lamm path produces a Koch--Lamm divergence source. -/
theorem klPath_map_bound {T : ℝ} {A₀ A₂ Aₚ ε : ℝ≥0}
    (A : ℝ × V → E →L[ℝ] F) (u : ℝ × V → F) (d : ℝ × V → E)
    (hA : ∀ z, ‖A z‖ ≤ (ε : ℝ))
    (hmeas : AEStronglyMeasurable (fun z => A z (d z))
      (klVolume : Measure (ℝ × V)))
    (hd : KLPath T A₀ A₂ Aₚ u d) :
    KLSource1 T (ε * A₂) (ε * Aₚ) (fun z => A z (d z)) := by
  apply kl1_map_bound A d hA hmeas
  exact ⟨hd.grad_ae, hd.grad_l2, hd.grad_lp⟩

end KochLamm

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
