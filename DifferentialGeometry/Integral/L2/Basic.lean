import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

/-!
# Integration wrappers for the Riemannian volume measure

This file provides thin, project-idiomatic wrappers over Mathlib's Bochner and Lebesgue
integrals, specialised to the Riemannian volume measure
`DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure g` built in the
`Integral.Measure` files.

The purpose of the wrappers is threefold:

* install the canonical Borel structure on the manifold `M` and the model space `E`
  locally, so callers never need to expose measurability prerequisites in their public
  signatures;
* rephrase standard Mathlib integrability / linearity lemmas directly in terms of the
  Riemannian volume measure, using the project's smooth Riemannian metric abbreviation;
* keep hypotheses minimal, in line with the project-wide rule that measure-theoretic
  structure is never part of an exported signature.

Each wrapper is a one-liner: all mathematical content already lives in Mathlib. The
value-add is typeclass hygiene and signature ergonomics.

## Main sections

* Measurability: `aestronglyMeasurable_of_continuous`,
  `aestronglyMeasurable_of_contMDiff`.
* Integrability against the Riemannian volume measure, in three flavours:
  continuous with compact support, smooth with compact support, and continuous on
  a closed manifold (automatic compact support).
* Linearity wrappers: `integral_add_of_riemannianVolume`,
  `integral_smul_of_riemannianVolume`, `integral_sub_of_riemannianVolume`,
  `integral_neg_of_riemannianVolume`, `integral_zero_of_riemannianVolume`,
  `integral_const_of_riemannianVolume`, `integral_congr_ae_of_riemannianVolume`.
* Non-negative integral wrappers: `lintegral_add_left_of_riemannianVolume`,
  `lintegral_const_mul_of_riemannianVolume`.
-/

noncomputable section

open Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A continuous function from a smooth manifold `M` into a second-countable normed
space `F` is almost-everywhere strongly measurable against any Borel measure on `M`. -/
theorem aestronglyMeasurable_of_continuous
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : M → F} (hf : Continuous f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable

/-- A smooth function from a smooth manifold `M` into a second-countable normed
space `F` is almost-everywhere strongly measurable against any Borel measure on `M`. -/
theorem aestronglyMeasurable_of_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

/-- Finite-order smoothness variant: `ContMDiff I _ n` for any `n` also yields
ae-strong-measurability. The continuity hypothesis is the content; higher-order
smoothness is irrelevant for the measurability side. -/
theorem aestronglyMeasurable_of_contMDiff_of_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {n : WithTop ℕ∞} {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) n f)
    (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

/-- A continuous compactly-supported function is integrable against the Riemannian
volume measure. Uses local finiteness on compacts of the volume measure. -/
theorem integrable_of_continuous_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hfc : Continuous f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  hfc.integrable_of_hasCompactSupport hfsup

/-- A smooth compactly-supported function is integrable against the Riemannian
volume measure. Reduces to the continuous case via `ContMDiff.continuous`. -/
theorem integrable_of_contMDiff_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hfc : ContMDiff I 𝓘(ℝ, F) ∞ f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  integrable_of_continuous_of_hasCompactSupport (I := I) (M := M) g
    hfc.continuous hfsup

/-- On a compact manifold, every continuous function is integrable against the
Riemannian volume measure: compact support is automatic and the volume measure is
a finite measure. -/
theorem integrable_of_continuous_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : Continuous f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  integrable_of_continuous_of_hasCompactSupport (I := I) (M := M) g hf
    (HasCompactSupport.of_compactSpace f)

/-- On a compact manifold, every smooth function is integrable against the
Riemannian volume measure. -/
theorem integrable_of_contMDiff_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  integrable_of_continuous_compactSpace (I := I) (M := M) g hf.continuous

/-- Additivity of the Bochner integral against the Riemannian volume measure. -/
theorem integral_add_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g))
    (hf' : MeasureTheory.Integrable f' (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, (f x + f' x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (∫ x, f' x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
  MeasureTheory.integral_add hf hf'

/-- Real-scalar homogeneity of the Bochner integral against the Riemannian volume
measure. The Bochner integral is `ℝ`-linear unconditionally; no integrability
hypothesis is required. -/
theorem integral_smul_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    (c : ℝ) (f : M → F) :
    ∫ x, c • f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = c • ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  MeasureTheory.integral_smul c f

/-- Subtractivity of the Bochner integral against the Riemannian volume measure. -/
theorem integral_sub_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g))
    (hf' : MeasureTheory.Integrable f' (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, (f x - f' x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          - (∫ x, f' x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
  MeasureTheory.integral_sub hf hf'

/-- Negation commutes with the Bochner integral against the Riemannian volume
measure. -/
theorem integral_neg_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M) (f : M → F) :
    ∫ x, -f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = -∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  MeasureTheory.integral_neg f

/-- The Bochner integral of the zero function against the Riemannian volume measure
is zero. -/
theorem integral_zero_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M) :
    ∫ _ : M, (0 : F) ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  MeasureTheory.integral_zero M F

/-- The Bochner integral of a constant function against the Riemannian volume
measure is the total volume scaled by the constant. -/
theorem integral_const_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : SmoothRiemannianMetric I M) (c : F) :
    ∫ _ : M, c ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = (riemannianVolumeMeasure (I := I) (M := M) g).real univ • c :=
  MeasureTheory.integral_const c

/-- Almost-everywhere equal functions have equal Bochner integrals against the
Riemannian volume measure. -/
theorem integral_congr_ae_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : SmoothRiemannianMetric I M)
    {f f' : M → F}
    (h : f =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] f') :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∫ x, f' x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  MeasureTheory.integral_congr_ae h

/-- Additivity of the lower Lebesgue integral against the Riemannian volume
measure, when the left summand is measurable. -/
theorem lintegral_add_left_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ≥0∞} (hf : Measurable f) (f' : M → ℝ≥0∞) :
    ∫⁻ x, f x + f' x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = (∫⁻ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          + (∫⁻ x, f' x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
  MeasureTheory.lintegral_add_left hf f'

/-- The lower Lebesgue integral pulls out a non-negative constant multiplier, when
the integrand is measurable. -/
theorem lintegral_const_mul_of_riemannianVolume
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (r : ℝ≥0∞) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, r * f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = r * ∫⁻ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  MeasureTheory.lintegral_const_mul r hf

end L2
end Integral
end DifferentialGeometry
