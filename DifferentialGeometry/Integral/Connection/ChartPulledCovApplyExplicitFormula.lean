import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

/-!
# Chart-pulled explicit formula for the first covariant derivative on the
`(r, s)`-tensor bundle

Given a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, and a smooth tangent vector field `B`, this file
expresses the chart-`α`-trivialised model-fibre value
`tensorRSChartE_section_repr r s α (covApply cov_RS B T) b` (an element of
`TensorRSModel r s ℝ E`) at a chart-`α` Levi-Civita good-set point `b` as the
sum of three explicit pieces:

* an **intrinsic Fréchet-derivative piece**, the value at the chart-pushforward
  `trivToE α b (B b)` of the Fréchet derivative of the chart-pulled
  representation `tensorRSChartE_section_repr r s α T ∘ (extChartAt I α).symm`
  at `extChartAt I α b` — these are the first chart-coordinate partial
  derivatives `∂_a T^I_J`;
* a finite sum of **upper-slot (input) Christoffel corrections** indexed by
  `k : Fin r`, with each summand the trivialised representation of the
  per-slot CLM `chartTensorRSInputSlotCorrection r s g α T B b k`;
* a finite sum of **lower-slot (output) Christoffel corrections** indexed by
  `l : Fin s`, with each summand the trivialised representation of the
  per-slot CLM `chartTensorRSOutputSlotCorrection r s g α T B b l`.

Each per-slot Christoffel correction is *polynomial in the chart-frame
components of `T` and `B`*, weighted by the chart-`α` Levi-Civita parallel
CLM (i.e. the chart Christoffel data of the metric `g`), so the right-hand
side is the textbook formula

  `(∇_B T)^I_J(b) = B^a(b) · ∂_a T^I_J(b) + Γ-terms in T^I_J and B^a`.

The intrinsic piece is the `∂_a` contribution and the two slot sums are the
`Γ`-terms.

## Main result

* `chart_pulled_covApply_explicit_formula` — the headline equality, valid for
  smooth sections at chart-`α` Levi-Civita good-set points.

The chart-target version (with `b = (extChartAt I α).symm y` for `y` in the
chart target) is then a direct one-step consequence; we ship it as
`chart_pulled_covApply_explicit_formula_target` for downstream uses that
prefer the `y`-parametrisation.

## Strategy

1. Apply the first-derivative chart agreement
   `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet` to rewrite
   `cov_RS T b (B b)` as the chart-frame value
   `chartTensorRSCovariantDerivative r s g α T B b`.
2. Unfold via `chartTensorRSCovariantDerivative_def` into the three-piece sum
   (intrinsic + ∑ input-slot - ∑ output-slot).
3. Push the chart-`α` `continuousLinearMapAt` through the sum / negation via
   `map_add`, `map_sub`, `map_sum` (the trivialisation is a CLM on the fibre).
4. For the intrinsic piece, unfold `tensorRSIntrinsicChartCLM_apply`. The
   inner `tensorRSChartFiberFromModel` is `symmL ℝ b`, and on the
   chart-`α` `(r, s)`-bundle base set its composition with
   `continuousLinearMapAt ℝ b` is the identity
   (`continuousLinearMapAt_symmL`), leaving the bare Fréchet derivative.

The base-set membership at `b` follows from
`chartLeviCivitaGoodSet_mem_baseSet` (with the `(r, s)`-bundle base set being
the intersection of the `(0, r)` and `(0, s)` factor base sets, each of which
is the tangent base set).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private lemma good_set_mem_baseSet_rs
    (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    b ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  classical
  change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
    ((trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet)
  refine ⟨?_, ?_⟩
  · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb

/-- **Chart-pulled explicit formula for the first covariant derivative.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
`(r, s)`-tensor section `T`, a smooth tangent vector field `B`, and a
chart-`α` Levi-Civita good-set point `b`, the chart-`α`-trivialised model-fibre
value `tensorRSChartE_section_repr r s α (covApply cov_RS B T) b` decomposes
as the sum of:

* the **intrinsic Fréchet-derivative piece** — the value at the chart
  pushforward `trivToE α b (B b)` of the Fréchet derivative
  `fderiv ℝ (tensorRSChartE_section_repr r s α T ∘ (extChartAt I α).symm)
  (extChartAt I α b)` (these are the first chart-coordinate partial
  derivatives `∂_a T^I_J(b)`);

* the **input-slot Christoffel corrections** — a finite sum indexed by
  `k : Fin r` of the trivialised representations of
  `chartTensorRSInputSlotCorrection r s g α T B b k`, polynomial in the
  chart-frame components of `T` and `B` weighted by the chart-`α` Levi-Civita
  parallel CLM (i.e. the chart Christoffel data of `g`);

* the **output-slot Christoffel corrections** — a finite sum indexed by
  `l : Fin s` of the trivialised representations of
  `chartTensorRSOutputSlotCorrection r s g α T B b l`, also polynomial in the
  chart-frame components of `T` and `B` weighted by the chart Christoffel
  data of `g`.

Together the three pieces realise the textbook formula
`(∇_B T)^I_J(b) = B^a(b) · ∂_a T^I_J(b) + Γ-terms`. -/
theorem chart_pulled_covApply_explicit_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) b =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b l) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  have hb_baseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet :=
    good_set_mem_baseSet_rs (I := I) r s α hb
  have hb_baseT : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hAgree :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
      g r s α T B (b := b) hb
  have hLHS_eq :
      tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            T.toFun B.toFun b) := by
    change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b) = _
    change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T.toFun b (B.toFun b)) = _
    rw [hAgree.symm]
  rw [hLHS_eq]
  rw [chartTensorRSCovariantDerivative_def (I := I) r s g α T.toFun B.toFun b]
  rw [map_sub, map_add]
  rw [show (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) =
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) from
    map_sum ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [show (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) =
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) from
    map_sum ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T.toFun b (B.toFun b)]
  unfold tensorRSChartFiberFromModel
  rw [(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]

/-- **Chart-target version of the chart-pulled explicit formula.**

For a chart-target point `y` whose preimage `(extChartAt I α).symm y` lies in
the chart-`α` Levi-Civita good set, the same three-piece decomposition holds
with the base point `(extChartAt I α).symm y`. The intrinsic piece simplifies
slightly because `extChartAt I α ((extChartAt I α).symm y) = y` (provided `y`
lies in the chart target). -/
theorem chart_pulled_covApply_explicit_formula_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) l) := by
  classical
  have h := chart_pulled_covApply_explicit_formula (I := I) (M := M)
    g r s α T B (b := (extChartAt I α).symm y) hy_good
  have hround : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy_target
  simp only [Function.comp_apply]
  rw [hround] at h
  exact h

/-- **Chart-target version for `SmoothCcTensor`.** Specialisation of
`chart_pulled_covApply_explicit_formula_target` to a smooth, compactly
supported `(r, s)`-tensor section `T : SmoothCcTensor g r s`. -/
theorem chart_pulled_covApply_explicit_formula_target_smoothCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun b : M => T.toSection b)) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun b : M => T.toSection b) ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) l) :=
  chart_pulled_covApply_explicit_formula_target (I := I) (M := M)
    g r s α T.toSection B hy_target hy_good

end Connection
end Integral
end DifferentialGeometry

end
