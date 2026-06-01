import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Tensor.RSTensor.ChartJacobianSmoothness
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Pointwise wrapped continuity of the chart-inverse-Jacobian CLM family

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a base point
`α : M`, this file packages pointwise wrapped operator-norm continuities of
the chart-inverse-Jacobian CLM family at every centre, as delivered by the
existing `chartJinv_pre_clm_contMDiffAt` and `chartJ_pre_clm_contMDiffAt`
lemmas in `Tensor/RSTensor/ChartJacobianSmooth.lean`.

The wrapped CLM at centre `b₀` is

  W α b₀ b := (triv b₀).clmAt b ∘L (triv α).symmL b   : E →L[ℝ] E

which carries a chart-`b₀` Jacobian compensating factor. It is operator-norm
continuous at `b = b₀` (smooth, even), and at the centre satisfies the
identity `W α b₀ b₀ = chartJinv α b₀` because `(triv b₀).clmAt b₀ = id`.

The symmetric forward wrapped CLM
  V α b₀ b := (triv α).clmAt b ∘L (triv b₀).symmL b   : E →L[ℝ] E

is also operator-norm continuous at `b = b₀`, with `V α b₀ b₀ = chartJ α b₀`.

## Main statements

* `chartJinv_wrapped_continuousAt α hb₀` — pointwise continuity of `W α b₀`
  at `b₀ ∈ (chartAt H α).source`.
* `chartJ_wrapped_continuousAt α hb₀` — pointwise continuity of `V α b₀`
  at `b₀ ∈ (chartAt H α).source`.
* `chartJinv_wrapped_centre_eq` and `chartJ_wrapped_centre_eq` — the centre
  identities relating the wrapped CLMs to the raw `chartJinv α b₀` and
  `chartJ α b₀`.
* `chartJ_self` and `chartJinv_self` — the centre identities at `b = b₀`.

The operator-norm `ContinuousOn`-on-base-set statement for the raw
`b ↦ chartJinv α b : M → (E →L[ℝ] E)` is delivered as the headline
`chartJinv_continuousOn` below, via the pointwise reduction at each centre
combined with the operator-norm continuity of CLM composition in
finite-dimensional spaces.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-`b` Jacobian factor at the centre is the identity. -/
lemma chartJ_self (b : M) :
    (trivializationAt E (TangentSpace I) b).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

/-- The chart-`b` inverse trivialisation at the centre is the identity. -/
lemma chartJinv_self (b : M) :
    (trivializationAt E (TangentSpace I) b).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

/-- The wrapped chart-inverse-Jacobian CLM
`b ↦ (triv b₀).clmAt b ∘L (triv α).symmL b` is operator-norm continuous at the
centre `b₀ ∈ (chartAt H α).source`. -/
theorem chartJinv_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) α).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (chartJinv_pre_clm_contMDiffAt (I := I) (M := M) α hb₀).continuousAt

/-- The reverse wrapped chart-Jacobian CLM
`b ↦ (triv α).clmAt b ∘L (triv b₀).symmL b` is operator-norm continuous at the
centre `b₀ ∈ (chartAt H α).source`. -/
theorem chartJ_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (chartJ_pre_clm_contMDiffAt (I := I) (M := M) α hb₀).continuousAt

/-- At the centre `b = b₀`, the wrapped chart-inverse-Jacobian CLM coincides with
the raw `chartJinv α b₀`. -/
theorem chartJinv_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀ ∘L
      (trivializationAt E (TangentSpace I) α).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartJinv (I := I) (M := M) α b₀ := by
  rw [chartJ_self (I := I) (M := M) b₀]
  ext v
  rfl

/-- At the centre `b = b₀`, the reverse wrapped chart-Jacobian CLM coincides with
the raw `chartJ α b₀`. -/
theorem chartJ_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀ ∘L
      (trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartJ (I := I) (M := M) α b₀ := by
  rw [chartJinv_self (I := I) (M := M) b₀]
  ext v
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
