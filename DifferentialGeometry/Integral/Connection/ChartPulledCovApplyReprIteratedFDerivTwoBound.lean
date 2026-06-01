import DifferentialGeometry.Integral.Connection.IntrinsicPieceIteratedFDerivTwoBound
import DifferentialGeometry.Integral.Connection.SlotCorrectionIteratedFDerivTwoBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.IteratedFDerivFourTensorReprChartCompBound

/-!
# Squared order-2 iterated Fréchet derivative bound for the chart-pulled
representation of `covApply ∇ B T`

Combining the intrinsic-piece order-2 iteratedFDeriv bound with the input /
output Christoffel slot-correction order-2 iteratedFDeriv bounds yields a
uniform bound on the squared norm of the order-2 iterated Fréchet derivative
of the chart-pulled representation of `covApply ∇ B T` at chart-coordinate
points whose preimage lies in the partition-of-unity tsupport intersected
with the chart-`α` Levi-Civita good set.

Concretely, for a smooth Riemannian manifold `(M, g)`, a chart-centre
`α : M`, ranks `r, s : ℕ`, a smooth tangent vector field `B`, and a smooth
compactly supported `(r, s)`-tensor section `T`, there is a constant
`K ≥ 0` (depending on `g`, the chart at `α`, the ranks `r`, `s`,
and `B`, but independent of `T` and `b`) such that for any `b ∈ tsupport
(POU α) ∩ chartLeviCivitaGoodSet α`, the squared norm of the order-2 iterated
Fréchet derivative of the chart-pulled representation of `covApply ∇ B T` at
`extChartAt I α b` is bounded by

```
K * Σ_{j ∈ Fin 4} ‖iteratedFDeriv ℝ j.val (repr T ∘ symm) (extChartAt I α b)‖²
```

where `repr T = tensorRSChartE_section_repr r s α T.toSection`.

## Strategy

1. By `chart_pulled_covApply_repr_eventuallyEq`, the chart-pulled
   representation of `covApply ∇ B T` equals an explicit three-piece sum
   (intrinsic piece + input-slot Christoffel correction sum − output-slot
   Christoffel correction sum) on a neighbourhood of `extChartAt I α b`.

2. `Filter.EventuallyEq.iteratedFDeriv` then identifies the order-2 iterated
   Fréchet derivative of the LHS with that of the three-piece sum at the
   chart point.

3. Each individual piece is `ContDiffAt 2`, so the order-2 iterated Fréchet
   derivative distributes across the sums and the subtraction via
   `iteratedFDeriv_fun_sum_apply`, `iteratedFDeriv_add_apply`, and
   `iteratedFDeriv_sub_apply`.

4. The triangle inequality and the three per-piece bounds
   (`intrinsic_piece_iteratedFDeriv_two_bound`,
   `inputSlot_correction_iteratedFDeriv_two_bound`,
   `outputSlot_correction_iteratedFDeriv_two_bound`) bound the order-2
   iteratedFDeriv norm by `K' · (‖iter 3 F‖ + ‖iter 2 F‖ + ‖fderiv F‖ + ‖F‖)`
   where `F = repr T ∘ symm`.

5. Squaring and using `(a+b+c+d)² ≤ 4(a² + b² + c² + d²)` together with
   `norm_iteratedFDeriv_zero` and `norm_iteratedFDeriv_one` then expresses
   the bound as `K · Σ_{j ∈ Fin 4} ‖iter j F‖²`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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

/-- The intrinsic piece is `ContDiffAt ∞` at `extChartAt I α b` whenever `b`
lies in the chart-`α` Levi-Civita good set. -/
private lemma intrinsicPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hc_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)) U :=
    hF_cd.fderiv_of_isOpen hU_open h_le
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hc_at : ContDiffAt ℝ 2
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by intro h; exact absurd h (by simp)
    have h_at_top : ContDiffAt ℝ ∞
        (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm))
        (extChartAt I α b) :=
      (hc_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hu_at : ContDiffAt ℝ 2
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hu_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  exact hc_at.clm_apply hu_at

/-- The chart-pulled input-slot correction is `ContDiffAt 2` at the chart
point. -/
private lemma inputSlotPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  have hK_cd : ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B k
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hK_at : ContDiffAt ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))
        (extChartAt I α b) :=
      (hK_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hF_at : ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hF_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have h_kernel_F_at : ContDiffAt ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y))
      (extChartAt I α b) := hK_at.clm_apply hF_at
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    exact chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx'_inv]; exact hx'_src) k
  exact h_kernel_F_at.congr_of_eventuallyEq h_evt

/-- The chart-pulled output-slot correction is `ContDiffAt 2` at the chart
point. -/
private lemma outputSlotPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  have hK_cd : ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B l
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hK_at : ContDiffAt ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))
        (extChartAt I α b) :=
      (hK_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hF_at : ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hF_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have h_kernel_F_at : ContDiffAt ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y))
      (extChartAt I α b) := hK_at.clm_apply hF_at
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    exact chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx'_inv]; exact hx'_src) l
  exact h_kernel_F_at.congr_of_eventuallyEq h_evt

/-- The chart-pulled representation of `covApply ∇ B T` is, on an open
neighbourhood of `extChartAt I α b`, equal to the intrinsic piece plus
input-slot Christoffel corrections minus output-slot Christoffel
corrections. Re-derived here (mirrors the helper in
`ChartPulledCovApplyReprFderivBound`) to avoid relying on a private lemma. -/
private lemma chart_pulled_covApply_repr_eventuallyEq'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y)))
        + ∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
              ℝ ((extChartAt I α).symm y)
              (chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) k)
        - ∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
              ℝ ((extChartAt I α).symm y)
              (chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) l)) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hmem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  refine Filter.eventually_of_mem (hU_open.mem_nhds hmem) ?_
  intro y hy
  rcases hy with ⟨x, hx_good, hxy⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hx_extsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hy_target : y ∈ (extChartAt I α).target := by
    rw [← hxy]; exact (extChartAt I α).map_source hx_extsrc
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have hsymm_good :
      (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [hx_inv]; exact hx_good
  exact chart_pulled_covApply_explicit_formula_target_smoothCc
    (I := I) (M := M) g r s α T B hy_target hsymm_good

end Connection
end Integral
end DifferentialGeometry

end
