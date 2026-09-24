import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped ContDiff

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def radialDifference (f : E → F) (a : E) (p : ℝ × E) : F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (a + t • (p.1 • p.2)) p.2

variable [FiniteDimensional ℝ E] [CompleteSpace F]

private theorem radialDifference_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) :
    ContDiff ℝ ∞ (radialDifference f a) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hpath : ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ =>
      a + p.2 • (p.1.1 • p.1.2)) :=
    contDiff_const.add (contDiff_snd.smul (contDiff_fst.fst.smul contDiff_fst.snd))
  have hi : ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ =>
      fderiv ℝ f (a + p.2 • (p.1.1 • p.1.2)) p.1.2) :=
    (hfd.comp hpath).clm_apply contDiff_fst.snd
  exact contDiffOn_univ.mp (contDiffOn_paramIntervalIntegral
    (fun p : ℝ × E => fun t : ℝ => fderiv ℝ f (a + t • (p.1 • p.2)) p.2)
    hi.contDiffOn)

omit [FiniteDimensional ℝ E] in
private theorem smul_radialDifference {f : E → F} (hf : ContDiff ℝ ∞ f)
    (a : E) (s : ℝ) (x : E) :
    s • radialDifference f a (s, x) = f (a + s • x) - f a := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (a + t • (s • x)))
      (s • fderiv ℝ f (a + t • (s • x)) x) t := by
    intro t
    have hp : HasDerivAt (fun t : ℝ => a + t • (s • x)) (s • x) t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (s • x)).const_add a
    simpa only [Function.comp_def, map_smul] using
      ((hf.differentiable (by simp)) (a + t • (s • x))).hasFDerivAt.comp_hasDerivAt t hp
  have hc : Continuous (fun t : ℝ => s • fderiv ℝ f (a + t • (s • x)) x) :=
    continuous_const.smul ((hfd.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa only [radialDifference, intervalIntegral.integral_smul, one_smul, zero_smul,
    add_zero] using h

theorem exists_contDiff_rescaling {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) :
    ∃ L : ℝ × E → F, ContDiff ℝ ∞ L ∧
      (∀ x, L (0, x) = fderiv ℝ f a x) ∧
      (∀ s x, s • L (s, x) = f (a + s • x) - f a) ∧
      (∀ s, s ≠ 0 → ∀ x, L (s, x) = s⁻¹ • (f (a + s • x) - f a)) ∧
      ∀ x, L (1, x) = f (a + x) - f a := by
  refine ⟨radialDifference f a, radialDifference_contDiff hf a, ?_,
    smul_radialDifference hf a, ?_, ?_⟩
  · intro x
    simp [radialDifference]
  · intro s hs x
    have h := congrArg (fun y : F => s⁻¹ • y) (smul_radialDifference hf a s x)
    simpa only [inv_smul_smul₀ hs] using h
  · intro x
    simpa only [one_smul] using smul_radialDifference hf a 1 x

end DifferentialGeometry.Analysis.Calculus
