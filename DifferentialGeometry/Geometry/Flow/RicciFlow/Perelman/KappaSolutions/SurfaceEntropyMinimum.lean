import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

section FiniteMeasure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [CompactSpace α] [Nonempty α]

theorem entropy_minimum_and_eq_iff_constant
    (μ : Measure α) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {R : α → Real} (hRcont : Continuous R) (hRnonneg : ∀ x, 0 ≤ R x) :
    let A := μ.real Set.univ
    let C := ∫ x, R x ∂μ
    let N := ∫ x, R x * Real.log (R x * A) ∂μ
    C * Real.log C ≤ N ∧ (N = C * Real.log C ↔ ∃ c : Real, ∀ x, R x = c) := by
  let A := μ.real Set.univ
  let C := ∫ x, R x ∂μ
  let N := ∫ x, R x * Real.log (R x * A) ∂μ
  let Z : α → Real := fun x => A * R x
  change C * Real.log C ≤ N ∧ (N = C * Real.log C ↔ ∃ c : Real, ∀ x, R x = c)
  have hApos : 0 < A := measureReal_univ_pos
  have hAne : A ≠ 0 := hApos.ne'
  have hZcont : Continuous Z := continuous_const.mul hRcont
  have hZint : Integrable Z μ :=
    hZcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPhiZint : Integrable (fun x => Z x * Real.log (Z x)) μ :=
    (Real.continuous_mul_log.comp hZcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZmem : ∀ᵐ x ∂μ, Z x ∈ Set.Ici (0 : Real) :=
    Eventually.of_forall (fun x => mul_nonneg hApos.le (hRnonneg x))
  have havgZ : (⨍ x, Z x ∂μ) = C := by
    rw [average_eq, smul_eq_mul]
    change A⁻¹ * (∫ x, A * R x ∂μ) = C
    rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hAne, one_mul]
  have hPhiZ : (fun x => Z x * Real.log (Z x)) =
      fun x => A * (R x * Real.log (R x * A)) := by
    funext x
    dsimp only [Z]
    rw [mul_comm A (R x)]
    ring
  have havgPhiZ : (⨍ x, Z x * Real.log (Z x) ∂μ) = N := by
    rw [average_eq, smul_eq_mul, hPhiZ]
    change A⁻¹ * (∫ x, A * (R x * Real.log (R x * A)) ∂μ) = N
    rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hAne, one_mul]
  have hJensen := Real.convexOn_mul_log.map_average_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hZmem hZint hPhiZint
  have hminimum : C * Real.log C ≤ N := by
    simpa only [havgZ, havgPhiZ] using hJensen
  refine ⟨hminimum, ?_⟩
  constructor
  · intro heq
    obtain hconst | hstrict :=
      Real.strictConvexOn_mul_log.ae_eq_const_or_map_average_lt
        Real.continuous_mul_log.continuousOn isClosed_Ici hZmem hZint hPhiZint
    · have hZeq : Z = fun _ => C := by
        apply MeasureTheory.Measure.eq_of_ae_eq (μ := μ) _ hZcont continuous_const
        filter_upwards [hconst] with x hx
        exact hx.trans havgZ
      refine ⟨C / A, ?_⟩
      intro x
      apply (eq_div_iff hAne).2
      have hx : A * R x = C := congrFun hZeq x
      simpa only [mul_comm] using hx
    · have hlt : C * Real.log C < N := by
        simpa only [havgZ, havgPhiZ] using hstrict
      exact False.elim (hlt.ne heq.symm)
  · rintro ⟨c, hc⟩
    have hZeq : Z = fun _ => A * c := by
      funext x
      exact congrArg (fun r => A * r) (hc x)
    have hCeq : C = A * c := by
      rw [← havgZ, hZeq]
      exact average_const μ (A * c)
    calc
      N = ⨍ x, Z x * Real.log (Z x) ∂μ := havgPhiZ.symm
      _ = (A * c) * Real.log (A * c) := by
        rw [hZeq]
        exact average_const μ ((A * c) * Real.log (A * c))
      _ = C * Real.log C := by rw [hCeq]

end FiniteMeasure

section MetricScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [CompactSpace M] [Nonempty M]

local instance surfaceEntropyMeasurable : MeasurableSpace M := borel M
local instance surfaceEntropyBorel : BorelSpace M := ⟨rfl⟩

theorem surfaceEntropy_minimum
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let A := μ.real Set.univ
    let C := ∫ x, R x ∂μ
    let N := ∫ x, R x * Real.log (R x * A) ∂μ
    C * Real.log C ≤ N ∧
      (N = C * Real.log C ↔ ∃ c : Real, ∀ x, metricScalarAt (I := I) g x = c) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact entropy_minimum_and_eq_iff_constant μ (metricScalar_smooth g).continuous
    (fun x => (hpositive x).le)

end MetricScalar

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
