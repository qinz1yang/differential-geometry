import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.Pairing.CauchySchwarz
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Pre-Hilbert structure on compactly-supported smooth tensor sections

This file installs the inner-product-space structure on the wrapper
`SmoothCcTensor g r s` from `SmoothSections.Defs` using the global
metric-induced `L²` pairing `tensorL2Inner` from `GlobalPairing.Defs`.

## Main constructions

* A `PreInnerProductSpace.Core ℝ (SmoothCcTensor g r s)` instance whose
  inner product is the global `L²` pairing of the underlying maps.
* The induced `SeminormedAddCommGroup (SmoothCcTensor g r s)` and
  `InnerProductSpace ℝ (SmoothCcTensor g r s)` instances, derived from
  the core via `InnerProductSpace.Core.toSeminormedAddCommGroup` and
  `InnerProductSpace.ofCore`.

The instance is a *pre*-inner-product space: the kernel of the seminorm
contains all sections vanishing almost everywhere (with respect to the
Riemannian volume measure), so the seminorm is not a norm.

## Strategy

The four `PreInnerProductSpace.Core` axioms reduce to algebraic
properties of `tensorL2Inner` already established in
`GlobalPairing.Algebra` and `GlobalPairing.CauchySchwarz`:

* `conj_inner_symm` reduces to `tensorL2Inner_symm` (real conjugation is
  trivial);
* `re_inner_nonneg` reduces to `tensorL2Inner_nonneg`;
* `add_left` reduces to `tensorL2Inner_add_left`, with cross
  integrability supplied by `SmoothCcTensor.integrable_inner_cross`;
* `smul_left` reduces to `tensorL2Inner_smul_left` (real conjugation is
  trivial; lemma is unconditional).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

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

section PreHilbert

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- The pre-inner-product core on compactly-supported smooth `(r, s)`-tensor
sections, whose inner product is the global metric-induced `L²` pairing
`tensorL2Inner g r s S.toFun T.toFun`. -/
noncomputable instance instPreInnerProductSpaceCore :
    PreInnerProductSpace.Core ℝ (SmoothCcTensor g r s) where
  inner S T := tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
  conj_inner_symm S T := by
    change (tensorL2Inner (I := I) (M := M) g r s T.toFun S.toFun : ℝ) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    exact tensorL2Inner_symm (I := I) (M := M) g r s T.toFun S.toFun
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun
    exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  add_left S₁ S₂ T := by
    change tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  smul_left S T c := by
    change tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
      c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun

set_option linter.unusedSectionVars false in
/-- The seminormed structure on `SmoothCcTensor g r s` derived from the
pre-inner-product core. The seminorm is `√(tensorL2Inner g r s S.toFun
S.toFun) = tensorL2Norm g r s S.toFun`. -/
noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (SmoothCcTensor g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in
/-- The inner-product-space structure on `SmoothCcTensor g r s` derived
from the pre-inner-product core. -/
noncomputable instance instInnerProductSpace :
    InnerProductSpace ℝ (SmoothCcTensor g r s) :=
  InnerProductSpace.ofCore _

set_option linter.unusedSectionVars false in
/-- The inner product on `SmoothCcTensor g r s` is the global `L²`
pairing of the underlying maps. -/
@[simp] theorem SmoothCcTensor.inner_def (S T : SmoothCcTensor g r s) :
    ⟪S, T⟫_ℝ = tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := rfl

set_option linter.unusedSectionVars false in
/-- The seminorm on `SmoothCcTensor g r s` is the global `L²` norm of the
underlying map. -/
theorem SmoothCcTensor.norm_def (S : SmoothCcTensor g r s) :
    ‖S‖ = tensorL2Norm (I := I) (M := M) g r s S.toFun := rfl

end PreHilbert

section InstanceTests

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensor g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensor g r s) := inferInstance

end InstanceTests

end L2
end Integral
end DifferentialGeometry

end
