import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff

section MeanVariance

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [CompactSpace α]

private theorem mean_variance_pairing
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    {R : α → Real} (hR : Continuous R) :
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, r - R x ∂μ) = 0 ∧
      -(∫ x, R x * (r - R x) ∂μ) = ∫ x, (R x - r) ^ 2 ∂μ := by
  let A := μ.real Set.univ
  let C := ∫ x, R x ∂μ
  let r := C / A
  change (∫ x, r - R x ∂μ) = 0 ∧
    -(∫ x, R x * (r - R x) ∂μ) = ∫ x, (R x - r) ^ 2 ∂μ
  have hAne : A ≠ 0 := measureReal_univ_ne_zero
  have hRint : Integrable R μ :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ x, r - R x ∂μ) = 0 := by
    rw [integral_sub (integrable_const r) hRint, integral_const, smul_eq_mul]
    change A * (C / A) - C = 0
    field_simp [hAne]
    ring
  have hdevmean : (∫ x, R x - r ∂μ) = 0 := by
    rw [integral_sub hRint (integrable_const r), integral_const, smul_eq_mul]
    change C - A * (C / A) = 0
    field_simp [hAne]
    ring
  have hdevint : Integrable (fun x => R x - r) μ :=
    hRint.sub (integrable_const r)
  have hsquareint : Integrable (fun x => (R x - r) ^ 2) μ :=
    ((hR.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hmean, ?_⟩
  calc
    -(∫ x, R x * (r - R x) ∂μ) = ∫ x, -(R x * (r - R x)) ∂μ :=
      (integral_neg _).symm
    _ = ∫ x, ((R x - r) ^ 2 + r * (R x - r)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = (∫ x, (R x - r) ^ 2 ∂μ) + r * (∫ x, R x - r ∂μ) := by
      rw [integral_add hsquareint (hdevint.const_mul r), integral_const_mul]
    _ = ∫ x, (R x - r) ^ 2 ∂μ := by rw [hdevmean, mul_zero, add_zero]

end MeanVariance

section MetricScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [CompactSpace M] [Nonempty M]

local instance entropyPairingMeasurable : MeasurableSpace M := borel M
local instance entropyPairingBorel : BorelSpace M := ⟨rfl⟩

theorem surfaceEntropy_poisson_rhs_integral_zero
    (g : SmoothRiemannianMetric I M) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, r - R x ∂μ) = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact (mean_variance_pairing μ (metricScalar_smooth g).continuous).1

theorem surfaceEntropy_poisson_gradient_pairing [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g f x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, g.inner x
      ((gradG (I := I) g ⟨R, metricScalar_smooth g⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ) =
      ∫ x, (R x - r) ^ 2 ∂μ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let r := (∫ x, R x ∂μ) / μ.real Set.univ
  let : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g (metricScalar_smooth g) f.contMDiff
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ x, g.inner x
      ((gradG (I := I) g ⟨R, metricScalar_smooth g⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ) =
        -(∫ x, R x * ΔG (I := I) g f x ∂μ) := hgreen
    _ = -(∫ x, R x * (r - R x) ∂μ) := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => congrArg (fun z => R x * z) (hpoisson x))
    _ = ∫ x, (R x - r) ^ 2 ∂μ :=
      (mean_variance_pairing μ (metricScalar_smooth g).continuous).2

end MetricScalar

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
