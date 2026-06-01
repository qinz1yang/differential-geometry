import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.FDerivDecomp
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement

/-!
# Concrete Christoffel-style decomposition of `fderiv (tensorTrivProj ∘ φ⁻¹)`

This file ships the **concrete** chart-coordinate decomposition of the
Fréchet derivative of the chart-`α`-trivialised `(r, s)`-tensor function

```
tensorTrivProj g r s S α ∘ (extChartAt I α).symm  :  E → TensorRSModel r s ℝ E
```

at a point `extChartAt I α b`, in terms of the chart-frame `(r, s)`-tensor
covariant derivative `chartTensorRSCovariantDerivative` and the explicit
input-slot and output-slot Christoffel corrections that appear in its
definition.

Two layers of identifications are used:

* The **basic factorisation** of `fderiv (tensorTrivProj S α ∘ φ⁻¹)` through
  `tensorRSIntrinsicChartCLM r s α S.toSection b`, which is exposed by the
  chart-frame `(r, s)`-tensor covariant derivative construction in
  `ChartTensorRSCovariantDerivative.lean`. The fact that
  `tensorTrivProj g r s S α` coincides with
  `tensorRSChartE_section_repr r s α S.toSection` as a function on `M` is a
  direct unfolding identity.

* The **chart-frame / abstract agreement** of
  `chartTensorRSCovariantDerivative` with the bundled
  `tensorRSCovariantDerivative` from the Levi-Civita connection
  (`ChartTensorRSCovariantDerivativeAgreement.lean`). This lets us re-express
  the intrinsic chart Fréchet derivative as the abstract covariant derivative
  plus / minus the same slot-Christoffel pieces.

Both pieces combine into a single concrete formula:

```
fderiv (tensorTrivProj S α ∘ φ⁻¹) (φ b) w
  = (triv).continuousLinearMapAt ℝ b
      ( chartTensorRSCovariantDerivative r s g α S.toSection X b
        + ∑ k chartTensorRSInputSlotCorrection r s g α S.toSection X b k
        - ∑ l chartTensorRSOutputSlotCorrection r s g α S.toSection X b l )
```

valid on the chart-`α` Levi-Civita good set, for any direction `w : E` and
any smooth tangent vector field `X` with `X b = trivFromE α b w`.

## Main results

* `fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic` — basic
  factorisation through the intrinsic chart CLM.
* `fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov` —
  Christoffel decomposition through the chart-frame covariant derivative.
* `fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov` — Christoffel
  decomposition through the bundled / abstract covariant derivative
  (Layer D agreement).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- `tensorTrivProj g r s S α` equals the chart-α-trivialised representation
of `S.toSection` (as a section of the `(r, s)`-tensor bundle). Both definitions
are `(triv).continuousLinearMapAt ℝ x (S.toSection x)`. -/
lemma tensorTrivProj_eq_tensorRSChartE_section_repr
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tensorTrivProj (I := I) (M := M) g r s S α =
      tensorRSChartE_section_repr (I := I) r s α (fun b => S.toSection b) := by
  funext x
  rfl

/-- **Basic factorisation.** On the chart-α Levi-Civita good set, the Fréchet
derivative of `tensorTrivProj S α ∘ φ⁻¹` at `φ b`, applied to a direction
`w : E`, factors as `triv.continuousLinearMapAt ℝ b` applied to the intrinsic
chart CLM action on `trivFromE α b w`. -/
theorem fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (tensorRSIntrinsicChartCLM (I := I) r s α (fun b' => S.toSection b') b
          (trivFromE (I := I) α b w)) := by
  classical
  rw [tensorTrivProj_eq_tensorRSChartE_section_repr (I := I) (M := M) g r s S α]
  rw [tensorRSIntrinsicChartCLM_apply
    (I := I) r s α (fun b' => S.toSection b') b
    (trivFromE (I := I) α b w)]
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [trivToE_trivFromE (I := I) α hb_base w]
  unfold tensorRSChartFiberFromModel
  have hb_baseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet)
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb_base
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb_base
  exact ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
    (R := ℝ) hb_baseRS _).symm

/-- The intrinsic chart CLM acting on `X b` is the chart-frame covariant
derivative plus the input-slot sum minus the output-slot sum (this is just
the algebraic definition rearranged). -/
private lemma tensorRSIntrinsicChartCLM_apply_eq_cov
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) :
    tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T X b
        - (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := by
  classical
  rw [chartTensorRSCovariantDerivative_def
    (I := I) r s g α T X b]
  abel

/-- **Concrete Christoffel decomposition (chart-frame form).** On the chart-α
Levi-Civita good set, the Fréchet derivative of
`tensorTrivProj S α ∘ φ⁻¹` at `φ b`, applied to a direction `w : E`,
decomposes through the chart-frame `(r, s)`-tensor covariant derivative
along any smooth vector field `X` with `X b = trivFromE α b w`, plus the
input-slot Christoffel sum minus the output-slot Christoffel sum, all
pushed forward through `triv.continuousLinearMapAt ℝ b`. -/
theorem fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X b = trivFromE (I := I) α b w) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') X b
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l) ) := by
  classical
  rw [fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb w]
  rw [show trivFromE (I := I) α b w = X b from hXb.symm]
  rw [tensorRSIntrinsicChartCLM_apply_eq_cov
    (I := I) r s g α (fun b' => S.toSection b') X b]

/-- **Concrete Christoffel decomposition (abstract form).** On the chart-α
Levi-Civita good set, the Fréchet derivative of
`tensorTrivProj S α ∘ φ⁻¹` at `φ b`, applied to a direction `w : E`,
decomposes through the bundled `tensorRSCovariantDerivative` of the
Levi-Civita connection, plus the input-slot Christoffel sum minus the
output-slot Christoffel sum, pushed forward through
`triv.continuousLinearMapAt ℝ b`. The decomposition is parametrised by a
smooth tangent vector field `X` with `X b = trivFromE α b w`. -/
theorem fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X.toFun b = trivFromE (I := I) α b w) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X.toFun b)
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X.toFun b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X.toFun b l) ) := by
  classical
  rw [fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov
    (I := I) (M := M) g r s α S X.toFun hb w hXb]
  have hcov_eq :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X.toFun b =
        TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X.toFun b) :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet
      (I := I) (M := M) g r s α S.toSection X hb
  rw [hcov_eq]

/-- **Manifold-derivative form of the basic factorisation.** -/
theorem mfderiv_tensorTrivProj_apply_eq_triv_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) v =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (tensorRSIntrinsicChartCLM (I := I) r s α (fun b' => S.toSection b') b v) := by
  classical
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [mfderiv_tensorTrivProj_eq_chart_fderiv
    (I := I) (M := M) g r s S α hb_chart hb_int v]
  rw [fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb (trivToE (I := I) α b v)]
  rw [trivFromE_trivToE (I := I) α hb_base v]

/-- **Manifold-derivative form of the Christoffel decomposition (chart-frame
form).** -/
theorem mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) (X b) =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') X b
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l) ) := by
  classical
  rw [mfderiv_tensorTrivProj_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb (X b)]
  rw [tensorRSIntrinsicChartCLM_apply_eq_cov
    (I := I) r s g α (fun b' => S.toSection b') X b]

example (g : SmoothRiemannianMetric I M) (α : M)
    (S : SmoothCcTensor g 1 2) (b : M)
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g 1 2 S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (trivializationAt (TensorRSModel 1 2 ℝ E)
          (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
        (tensorRSIntrinsicChartCLM (I := I) 1 2 α (fun b' => S.toSection b') b
          (trivFromE (I := I) α b w)) :=
  fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (I := I) (M := M) g 1 2 α S hb w

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
