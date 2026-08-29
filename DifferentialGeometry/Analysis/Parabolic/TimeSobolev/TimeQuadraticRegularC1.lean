import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeQuadraticRegularL1

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable {T : ℝ}

section Primitive

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem primitive_c1
    (hT : 0 < T) (F : ℝ → X)
    (hF : ContinuousOn F (Icc (0 : ℝ) T)) (c : X) :
    ContDiffOn ℝ 1 (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T) ∧
      EqOn (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T)) F (Icc (0 : ℝ) T) := by
  have hFint : IntegrableOn F (Icc (0 : ℝ) T) volume :=
    hF.integrableOn_compact isCompact_Icc
  have hd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s ↦ c + ∫ r in (0 : ℝ)..s, F r) (F t)
        (Icc (0 : ℝ) T) t := by
    intro t ht
    have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    have hint : IntervalIntegrable F volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable (by
        rw [uIcc_of_le ht.1]
        exact hFint.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hmeas : StronglyMeasurableAtFilter F
        (𝓝[Icc (0 : ℝ) T] t) volume :=
      ⟨Icc (0 : ℝ) T, self_mem_nhdsWithin,
        hF.aestronglyMeasurable measurableSet_Icc⟩
    exact (intervalIntegral.integral_hasDerivWithinAt_right hint hmeas
      (hF t ht)).const_add c
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have heq : EqOn
      (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T)) F (Icc (0 : ℝ) T) := by
    intro t ht
    exact (hd t ht).derivWithin (huniq.uniqueDiffWithinAt ht)
  refine ⟨?_, heq⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin huniq]
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hF.congr fun _ ht ↦ heq ht

end Primitive

section Inner

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]

theorem mom_rep_c1
    (hT : 0 < T)
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (F : ℝ → X)
    (hF : ContinuousOn F (Icc (0 : ℝ) T))
    (hEuler : ∀ v : timeH1 X T, v.init = 0 → v.toFun T = 0 →
      2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        ∫ t in Icc (0 : ℝ) T, inner ℝ (F t) (v.toFun t) = 0) :
    ∃ c : X,
      ((fun t ↦ (2 : ℝ) • A t (u.deriv t))
        =ᵐ[volume.restrict (Ioo (0 : ℝ) T)]
          fun t ↦ c + ∫ r in (0 : ℝ)..t, F r) ∧
      ContDiffOn ℝ 1 (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T) ∧
      EqOn (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (Icc (0 : ℝ) T)) F (Icc (0 : ℝ) T) := by
  have hFint : IntegrableOn F (Icc (0 : ℝ) T) volume :=
    hF.integrableOn_compact isCompact_Icc
  obtain ⟨c, hc⟩ := mom_primitive_l1 hT A hA C hC u F hFint hEuler
  obtain ⟨hc1, hderiv⟩ := primitive_c1 hT F hF c
  exact ⟨c, hc, hc1, hderiv⟩

end Inner

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
