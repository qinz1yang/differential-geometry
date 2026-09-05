import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace DifferentialGeometry.Topology.Morse

open Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isCriticalPointAt_transContinuousLinearEquiv_iff (I : ModelWithCorners ℝ E H) (e : E ≃L[ℝ] E')
    (f : M → ℝ) (x : M) :
    IsCriticalPointAt (I.transContinuousLinearEquiv e) f x ↔
      IsCriticalPointAt I f x := by
  let J : ModelWithCorners ℝ E' H := I.transContinuousLinearEquiv e
  let Φ : M ≃ₘ^1⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e
  have hΦ : MDifferentiableAt I J (Φ : M → M) x :=
    Φ.contMDiffAt.mdifferentiableAt one_ne_zero
  have hΦsymm : MDifferentiableAt J I (Φ.symm : M → M) x :=
    Φ.symm.contMDiffAt.mdifferentiableAt one_ne_zero
  change MDifferentiableAt I J (id : M → M) x at hΦ
  change MDifferentiableAt J I (id : M → M) x at hΦsymm
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · have hfJ : MDifferentiableAt J 𝓘(ℝ, ℝ) f x := by
      simpa only [Function.comp_id] using hf.comp x hΦsymm
    have hforward : mfderiv I 𝓘(ℝ, ℝ) f x =
        (mfderiv J 𝓘(ℝ, ℝ) f x).comp (mfderiv I J (id : M → M) x) := by
      simpa only [Function.comp_id, id_eq] using
        (mfderiv_comp (I := I) (I' := J) (I'' := 𝓘(ℝ, ℝ))
          (x := x) (g := f) (f := (id : M → M)) hfJ hΦ)
    have hbackward : mfderiv J 𝓘(ℝ, ℝ) f x =
        (mfderiv I 𝓘(ℝ, ℝ) f x).comp (mfderiv J I (id : M → M) x) := by
      simpa only [Function.comp_id, id_eq] using
        (mfderiv_comp (I := J) (I' := I) (I'' := 𝓘(ℝ, ℝ))
          (x := x) (g := f) (f := (id : M → M)) hf hΦsymm)
    unfold IsCriticalPointAt
    constructor
    · intro h
      rw [hforward, h]
      simp
    · intro h
      rw [hbackward, h]
      simp
  · have hfJ : ¬MDifferentiableAt J 𝓘(ℝ, ℝ) f x := by
      intro hfJ
      apply hf
      simpa only [Function.comp_id] using hfJ.comp x hΦ
    unfold IsCriticalPointAt
    change mfderiv J 𝓘(ℝ, ℝ) f x = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_zero_of_not_mdifferentiableAt hfJ,
      mfderiv_zero_of_not_mdifferentiableAt hf]
    simp

end
end DifferentialGeometry.Topology.Morse
