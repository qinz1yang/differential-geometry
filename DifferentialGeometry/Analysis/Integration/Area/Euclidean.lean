import DifferentialGeometry.Analysis.Calculus.Derivative.DifferentialComparison
import DifferentialGeometry.Geometry.Measure.Area.TwoJacobian
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set














noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]


def euclideanAreaDensity (u : ℂ → E) (z : ℂ) : ℝ :=
  twoJacobian (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)


def euclideanArea (u : ℂ → E) (s : Set ℂ) : ℝ := ∫ z in s, euclideanAreaDensity u z

theorem euclideanAreaDensity_nonneg (u : ℂ → E) (z : ℂ) :
    0 ≤ euclideanAreaDensity u z := twoJacobian_nonneg _ _

theorem euclideanArea_nonneg (u : ℂ → E) (s : Set ℂ) : 0 ≤ euclideanArea u s :=
  integral_nonneg (fun z => euclideanAreaDensity_nonneg u z)

theorem euclideanAreaDensity_eq_zero_of_not_differentiableAt {u : ℂ → E} {z : ℂ}
    (h : ¬ DifferentiableAt ℝ u z) : euclideanAreaDensity u z = 0 := by
  simp [euclideanAreaDensity, fderiv_zero_of_not_differentiableAt h]

@[simp] theorem euclideanAreaDensity_const (q : E) (z : ℂ) :
    euclideanAreaDensity (fun _ => q) z = 0 := by simp [euclideanAreaDensity]

@[simp] theorem euclideanArea_const (q : E) (s : Set ℂ) :
    euclideanArea (fun _ => q) s = 0 := by simp [euclideanArea]


theorem euclideanAreaDensity_smul (u : ℂ → E) (c : ℝ) (z : ℂ) :
    euclideanAreaDensity (c • u) z = c ^ 2 * euclideanAreaDensity u z := by
  simp only [euclideanAreaDensity, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, twoJacobian_smul]
  rw [← pow_two, abs_of_nonneg (sq_nonneg c)]

theorem euclideanArea_smul (u : ℂ → E) (c : ℝ) (s : Set ℂ) :
    euclideanArea (c • u) s = c ^ 2 * euclideanArea u s := by
  simp only [euclideanArea, euclideanAreaDensity_smul, integral_const_mul]


theorem euclideanAreaDensity_comp_le {u : ℂ → E} {f : E → F} {z : ℂ} {L : ℝ≥0}
    (hu : DifferentiableAt ℝ u z) (hcomp : DifferentiableAt ℝ (f ∘ u) z)
    (hf : LipschitzWith L f) :
    euclideanAreaDensity (f ∘ u) z ≤ (L : ℝ) ^ 2 * euclideanAreaDensity u z :=
  twoJacobian_linearMap_le (fderiv ℝ u z).toLinearMap
    (fderiv ℝ (f ∘ u) z).toLinearMap L.coe_nonneg
    (DifferentialGeometry.Analysis.norm_differential_comp_le hu.hasFDerivAt hcomp.hasFDerivAt hf) 1 Complex.I


theorem euclideanAreaDensity_le {u : ℂ → E} {C : ℝ≥0} (hu : LipschitzWith C u) (z : ℂ) :
    euclideanAreaDensity u z ≤ (C : ℝ) ^ 2 := by
  have hD := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := z)
  have h₁ : ‖fderiv ℝ u z 1‖ ≤ C := by
    simpa using (fderiv ℝ u z).le_opNorm (1 : ℂ) |>.trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg (1 : ℂ)))
  have hI : ‖fderiv ℝ u z Complex.I‖ ≤ C := by
    simpa using (fderiv ℝ u z).le_opNorm Complex.I |>.trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg Complex.I))
  calc
    euclideanAreaDensity u z ≤ ‖fderiv ℝ u z 1‖ * ‖fderiv ℝ u z Complex.I‖ :=
      twoJacobian_le_norm_mul _ _
    _ ≤ (C : ℝ) * C := mul_le_mul h₁ hI (norm_nonneg _) C.coe_nonneg
    _ = (C : ℝ) ^ 2 := (pow_two _).symm

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem measurable_euclideanAreaDensity (u : ℂ → E) : Measurable (euclideanAreaDensity u) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact continuous_twoJacobian.measurable.comp
    ((measurable_fderiv_apply_const ℝ u (1 : ℂ)).prodMk
      (measurable_fderiv_apply_const ℝ u Complex.I))


theorem integrableOn_euclideanAreaDensity {u : ℂ → E} {C : ℝ≥0} (hu : LipschitzWith C u)
    (s : Set ℂ) [IsFiniteMeasure (volume.restrict s)] : IntegrableOn (euclideanAreaDensity u) s := by
  apply Integrable.of_bound (measurable_euclideanAreaDensity u).aestronglyMeasurable ((C : ℝ) ^ 2)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (euclideanAreaDensity_nonneg u z)]
    exact euclideanAreaDensity_le hu z


theorem ae_euclideanAreaDensity_comp_le {u : ℂ → E} {f : E → F} {C L : ℝ≥0}
    (hu : LipschitzWith C u) (hf : LipschitzWith L f) :
    ∀ᵐ z ∂volume, euclideanAreaDensity (f ∘ u) z ≤ (L : ℝ) ^ 2 * euclideanAreaDensity u z := by
  filter_upwards [hu.ae_differentiableAt, (hf.comp hu).ae_differentiableAt] with z hz hz'
  exact euclideanAreaDensity_comp_le hz hz' hf



theorem euclideanArea_comp_le {u : ℂ → E} {f : E → F} {C L : ℝ≥0}
    (hu : LipschitzWith C u) (hf : LipschitzWith L f) (s : Set ℂ)
    [IsFiniteMeasure (volume.restrict s)] :
    euclideanArea (f ∘ u) s ≤ (L : ℝ) ^ 2 * euclideanArea u s := by
  rw [euclideanArea, euclideanArea, ← integral_const_mul]
  exact integral_mono_ae (integrableOn_euclideanAreaDensity (hf.comp hu) s)
    ((integrableOn_euclideanAreaDensity hu s).const_mul _)
    (ae_restrict_of_ae (ae_euclideanAreaDensity_comp_le hu hf))


theorem euclideanArea_union {u : ℂ → E} {C : ℝ≥0} (hu : LipschitzWith C u)
    {s t : Set ℂ} [IsFiniteMeasure (volume.restrict s)] [IsFiniteMeasure (volume.restrict t)]
    (hst : AEDisjoint volume s t) (ht : MeasurableSet t) :
    euclideanArea u (s ∪ t) = euclideanArea u s + euclideanArea u t :=
  setIntegral_union₀ hst ht.nullMeasurableSet
    (integrableOn_euclideanAreaDensity hu s) (integrableOn_euclideanAreaDensity hu t)

end FiniteDimensional

end DifferentialGeometry.Geometry
