import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Analysis.Integration.L2.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

theorem integral_normSq0S_pos
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) {s : ℕ}
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (hα : α x₀ ≠ 0) :
    0 < ∫ x, normSq0S (I := I) g x s (α x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hcont : Continuous (fun x : M => normSq0S (I := I) g x s (α x)) :=
    normSq0S_cont (I := I) g α
  have hnonneg : ∀ x : M, 0 ≤ normSq0S (I := I) g x s (α x) :=
    fun x => normSq0S_nonneg (I := I) g x s (α x)
  have hint : Integrable (fun x : M => normSq0S (I := I) g x s (α x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hcont
  haveI : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen (Function.support (fun x : M => normSq0S (I := I) g x s (α x))) :=
    hcont.isOpen_support
  refine hopen.measure_pos _ ⟨x₀, ?_⟩
  rw [Function.mem_support]
  exact (normSq0S_pos_of_ne_zero (I := I) g x₀ s (α x₀) hα).ne'

end L2
end Integral
end DifferentialGeometry
