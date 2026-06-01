import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula

/-!
# Bound on the Fréchet derivative of the chart-pulled representation of
`covApply ∇ B T`

Combining the intrinsic-piece Fréchet-derivative bound with the input/output
Christoffel slot-correction Fréchet-derivative bounds, we obtain a uniform
bound on the operator norm of the Fréchet derivative of the chart-pulled
representation of `covApply ∇ B T` at chart-coordinate points whose preimage
lies in the partition-of-unity tsupport intersected with the chart-`α`
Levi-Civita good set.

Concretely, for a smooth Riemannian manifold `(M, g)`, a chart-centre
`α : M`, ranks `r, s : ℕ`, a smooth tangent vector field `B`, and a smooth
compactly supported `(r, s)`-tensor section `T`, there is a constant
`K ≥ 0` (depending on `g`, the chart at `α`, the locality hypothesis on the
chart atlas, the ranks `r`, `s`, and `B`, but independent of `T` and `b`)
such that for any `b ∈ tsupport (POU α) ∩ chartLeviCivitaGoodSet α` and any
hypothesis `hF2_diff` that the chart-pulled representation `repr T ∘ symm`
is differentiable in its Fréchet derivative at `extChartAt I α b`, the
operator norm of the Fréchet derivative of the chart-pulled representation
of `covApply ∇ B T` at `extChartAt I α b` is bounded by

```
K * (‖repr T b‖
     + ‖fderiv ℝ (repr T ∘ symm) (extChartAt I α b)‖
     + ‖iteratedFDeriv ℝ 2 (repr T ∘ symm) (extChartAt I α b)‖)
```

## Strategy

1. The chart-pulled formula
   `chart_pulled_covApply_explicit_formula_target_smoothCc` expresses
   `repr (covApply ∇ B T) ∘ symm y` as the sum of an intrinsic
   Fréchet-derivative piece, a finite sum of input-slot Christoffel
   corrections, minus a finite sum of output-slot Christoffel corrections,
   at every point `y` of the chart target image of the Levi-Civita good set.

2. This holds on an open neighbourhood of `extChartAt I α b` whenever
   `b ∈ chartLeviCivitaGoodSet α`. We use `Filter.EventuallyEq.fderiv_eq` to
   rewrite the LHS's Fréchet derivative as the Fréchet derivative of the
   three-piece sum.

3. We distribute the Fréchet derivative across `+`, `-`, and finite sums via
   `fderiv_add`, `fderiv_sub`, `fderiv_fun_sum`. This requires each piece to
   be differentiable at the chart point.

4. The intrinsic piece's differentiability follows from
   `DifferentiableAt.clm_apply` applied to `fderiv (repr T ∘ symm)` (whose
   differentiability is `hF2_diff`) and the chart-pulled `B` representation
   (smooth on the chart-target image of the good set).

5. Each slot-correction piece's differentiability follows from
   `Filter.EventuallyEq.differentiableAt_iff` against the kernel-form
   factorisation, then `DifferentiableAt.clm_apply` for the kernel form.

6. The bounds on each summand come from `intrinsic_piece_fderiv_bound`,
   `chart_pulled_input_slot_correction_fderiv_bound`,
   `chart_pulled_output_slot_correction_fderiv_bound`. Summing and absorbing
   the constants into `K := K_I + ∑ K_in + ∑ K_out` gives the headline.
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

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled tensor representation. Re-derived here to avoid relying on
a private helper. -/
private lemma reprT_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (T.toSection x)) :=
    T.toSection.contMDiff
  have hbase :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  have hcm_on_source :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        ((chartAt H α).source) := by
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x
        (T.toSection x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hcm_on_good :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        (chartLeviCivitaGoodSet (I := I) α) := by
    rw [h_good_eq_source]; exact hcm_on_source
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hx_good, rfl⟩
  set F : M → TensorRSModel r s ℝ E :=
    fun b : M => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => T.toSection y') b with hF_def
  have hF_at : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞ F x :=
    hcm_on_good.contMDiffAt (hgood_open.mem_nhds hx_good)
  set φ := extChartAt I α
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hxφ_src : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_on :
      ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_tgt
  have hF_at' : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

/-- Smoothness of the chart-pulled `B`-representation on the chart-target
image of the good set. -/
private lemma uB_contDiffOn_goodSet
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  exact chartE_pullback_contDiffOn_goodSet (I := I) α hB_on

/-- Differentiability of the intrinsic Fréchet-derivative piece at the chart
point. -/
private lemma intrinsicPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hF2_diff : DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b)) :
    DifferentiableAt ℝ
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    uB_contDiffOn_goodSet (I := I) α B
  have hu_diff : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hu_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  exact hF2_diff.clm_apply hu_diff

/-- Differentiability of the chart-pulled input-slot Christoffel correction at
the chart point. -/
private lemma inputSlotPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ
      (fun y : E => tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    inputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B k hb_good
  have hK_diff : DifferentiableAt ℝ
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm y)) (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  have h_clm_diff : DifferentiableAt ℝ
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm y)
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y)))
      (extChartAt I α b) := hK_diff.clm_apply hR_diff
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    have h_factor :=
      chartTensorRSInputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := (extChartAt I α).symm y)
        (by rw [hx'_inv]; exact hx'_src) k
    exact h_factor
  exact (h_evt.differentiableAt_iff).mpr h_clm_diff

/-- Differentiability of the chart-pulled output-slot Christoffel correction
at the chart point. -/
private lemma outputSlotPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ
      (fun y : E => tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    outputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B l hb_good
  have hK_diff : DifferentiableAt ℝ
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm y)) (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  have h_clm_diff : DifferentiableAt ℝ
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm y)
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y)))
      (extChartAt I α b) := hK_diff.clm_apply hR_diff
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    have h_factor :=
      chartTensorRSOutputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := (extChartAt I α).symm y)
        (by rw [hx'_inv]; exact hx'_src) l
    exact h_factor
  exact (h_evt.differentiableAt_iff).mpr h_clm_diff

/-- The chart-pulled representation of `covApply ∇ B T` is, on an open
neighbourhood of `extChartAt I α b`, equal to the intrinsic piece plus
input-slot Christoffel corrections minus output-slot Christoffel
corrections. -/
private lemma chart_pulled_covApply_repr_eventuallyEq
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
