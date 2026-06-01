import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Pointwise bound on the chart-trivialised first covariant derivative by the
chart-frame scalar components and their chart-coordinate Fréchet derivative

For a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model `I`,
a chart-centre `α : M`, a fixed smooth tangent vector field `B`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, this file ships a pointwise
upper bound for the model-fiber norm of the chart-α-trivialised
representation of the section
`covApply cov_RS B T = b ↦ cov_RS T b (B b)`,
in terms of the chart-coordinate Fréchet derivative and the pointwise values of
the scalar chart-frame components of `T`.

Concretely, on the chart-α partition-of-unity tsupport, for every smooth
compactly-supported `(r, s)`-tensor section `T`, the bound takes the form

  `‖tensorRSChartE_section_repr r s α (covApply cov_RS B T) b‖
      ≤ K * ∑_{Idx, Jdx}
          (‖fderiv ℝ (tensorChartComponentRaw g r s T α Idx Jdx ∘
              (extChartAt I α).symm) (extChartAt I α b)‖
            + |tensorChartComponentRaw g r s T α Idx Jdx b|)`

with `K` depending only on the metric `g`, the chart at `α`, the locality
hypothesis, the ranks `r`, `s`, and on `B`; in particular `K` is independent
of `T`.

## Strategy

1. Use the chart-frame agreement `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet`
   to identify `covApply cov_RS B T b` with the chart-frame value
   `chartTensorRSCovariantDerivative r s g α T.toSection.toFun B.toFun b` on
   the chart-α Levi-Civita good set (which contains the POU tsupport under
   `[I.Boundaryless]`).
2. Pass through the forward fiber op-norm bound
   `tensorRSChartFiberToModel_opNorm_isBounded_on_compact` to bound the
   model-fiber norm of `tensorRSChartE_section_repr r s α (covApply ...) b`
   by a constant times the fiber norm of `covApply ... b`.
3. Apply the chart-frame op-norm bound
   `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` to bound the
   fiber norm of `chartTensorRSCovariantDerivative r s g α T B b` by

       `C * MX(B, b) * (‖fderiv (repr T ∘ symm)(extChartAt b)‖ * ‖B b‖ + ‖T b‖)`.

4. `‖B b‖` and `MX(B, b)` are bounded uniformly over the POU tsupport because
   `B` is smooth and the POU tsupport is compact.
5. Decompose `repr T = Σ_{Idx, Jdx} comp(repr T) • basis-elt`. Linearity of
   `fderiv` gives

       `fderiv (repr T ∘ symm) = Σ_{Idx, Jdx} fderiv (comp(repr T) ∘ symm) ⊗ basis-elt`.

   The bound on its operator norm by `Σ_{Idx, Jdx} ‖fderiv(scalar comp ∘ symm)‖
   * ‖basis-elt‖` follows from `norm_sum_le` and `ContinuousLinearMap.smulRight`.
6. The reverse fiber bound `tensorRSSpace_norm_le_chartRepr_norm_on_compact`
   bounds `‖T b‖` by a constant times `‖repr T b‖`, which is then bounded by
   `Σ_{Idx, Jdx} |comp(repr T b)| * ‖basis-elt‖` via the basis recovery
   `tensorRSModel_eq_sum_basis`. Each `comp(repr T b)` equals
   `tensorChartComponentRaw g r s T α Idx Jdx b` by definition.
7. Combine and absorb all uniform constants into a single `K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The model-fiber norm of the chart-α-trivialised representation of a smooth
compactly-supported `(r, s)`-tensor section at `b` is bounded by the sum of the
absolute values of its chart-frame components, times the basis-element norm
constant. -/
lemma reprNorm_le_sum_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| *
            tensorChartBasisNormConstant (E := E) r s := by
  classical
  set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
    r s α (fun y : M => T.toSection y) b with hR_def
  have hR_recover : R =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComponentProjection (E := E) r s Idx Jdx R •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
    tensorRSModel_eq_sum_basis (E := E) r s R
  have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComponentProjection (E := E) r s Idx Jdx R =
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
    intro Idx Jdx
    rw [tensorChartComponentRaw_def]
    rfl
  change ‖R‖ ≤ _
  rw [hR_recover]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [norm_smul, Real.norm_eq_abs, hcomp_eq Idx Jdx]
  exact mul_le_mul_of_nonneg_left
    (tensorChartBasisElement_norm_le (E := E) r s Idx Jdx)
    (abs_nonneg _)

/-- Each chart-frame scalar component pulled by `(extChartAt I α).symm` is
Fréchet-differentiable at the chart-coord image of any chart-source point. -/
lemma chart_pulled_component_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α b) := by
  classical
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro y hy
    have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  have hb_src : b ∈ (extChartAt I α).source :=
    (extChartAt_source (I := I) α).symm ▸ hb_chart
  have hb_target : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have h_open_target : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hcomp.contDiffOn
  have hcdAt : ContDiffWithinAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcontDiffOn _ hb_target
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcdAt.differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open_target.mem_nhds hb_target)

/-- The chart-coordinate Fréchet derivative of the chart-pulled
chart-α-trivialised representation of `T.toSection` at the chart-coord point
`extChartAt I α b` has operator norm bounded by

  `Σ_{Idx, Jdx} ‖fderiv ℝ (component_Idx_Jdx ∘ symm) (extChartAt b)‖
                  * ‖basis-elt(Idx, Jdx)‖`. -/
lemma fderiv_repr_opNorm_le_sum_fderiv_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖ *
            ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ := by
  classical
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  have hdiff_each := fun Idx Jdx =>
    chart_pulled_component_differentiableAt (I := I) (M := M)
      g r s T α Idx Jdx hb_chart
  have hfderiv_sum :
      fderiv ℝ
        (fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
        (extChartAt I α b) =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          fderiv ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := by
    have hd_inner : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
          DifferentiableAt ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := fun Idx Jdx => (hdiff_each Idx Jdx).smul_const _
    have hd_inner_sum : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ
          (fun y : E => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
              tensorChartBasisElement (E := E) r s Idx Jdx)
          (extChartAt I α b) := fun Idx =>
      DifferentiableAt.fun_sum (fun Jdx _ => hd_inner Idx Jdx)
    rw [fderiv_fun_sum (fun Idx _ => hd_inner_sum Idx)]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    exact fderiv_fun_sum (fun Jdx _ => hd_inner Idx Jdx)
  rw [hfderiv_sum]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [fderiv_smul_const (hdiff_each Idx Jdx)]
  rw [ContinuousLinearMap.norm_smulRight_apply]

end Connection
end Integral
end DifferentialGeometry

end
