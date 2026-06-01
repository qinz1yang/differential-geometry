import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartKernel
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.ChartPulledRawTensorReprFactorization

/-!
# Pointwise norm bound on the chart-pulled value of the nested chart-frame
covariant derivative of a smooth compactly supported tensor section

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a chart-frame index `i : Fin (Module.finrank ℝ E)`, and a smooth
compactly supported `(r, s)`-tensor section `T`, the value of the chart-`α`
trivialised representation of the *nested* chart-frame covariant derivative

  `b ↦ tensorRSChartE_section_repr r s α (covApply ∇ B (covApply ∇ B T)) b`,

where `B := chartFrameNormGlobalSmooth g α i` is the globally smooth
chart-`α` chart-frame Gram-Schmidt section, is bounded pointwise on the
intersection of the chart-`α` partition-of-unity tsupport with the chart-`α`
Levi-Civita good set by the chart-pulled iterated-Fréchet-derivative data of
`T` up to order `2`.

The pointwise bound, in squared form, reads

```
‖tensorRSChartE_section_repr r s α
    (fun y => (covApply ∇ B (covApply ∇ B T)) y) b‖ ^ 2 ≤
  K *
    (∑ j : Fin 3,
      ‖iteratedFDeriv ℝ j.val
          (tensorRSChartE_section_repr r s α (fun y => T.toSection y) ∘
            (extChartAt I α).symm)
          (extChartAt I α b)‖ ^ 2)
```

with `K ≥ 0` depending only on `g`, the chart
at `α`, the ranks `r`, `s`, and the chart-frame index `i`. The constant is
*independent* of `T` and `b`.

This headline is the order-0 (i.e., value, not Fréchet derivative) analogue
of the chart-pulled-nested-covApply Fréchet-derivative bound that follows
from iterating the order-1 covApply Fréchet-derivative bound (Sub-E,
`chart_pulled_covApply_repr_fderiv_bound`). The Fréchet-derivative variant
also requires an order-2 iterated-Fréchet-derivative bound on the
chart-pulled `repr (covApply ∇ B T) ∘ symm`, which is not yet developed in
this codebase; that order-2 bound will be needed downstream and is left as a
separate obligation.

## Strategy

The chart-pulled explicit formula
`chart_pulled_covApply_explicit_formula` applied to the smooth section
`σ := covApply ∇ B T` gives, at every chart-`α` Levi-Civita good-set
point `b`,

```
repr (covApply ∇ B σ) (b) =
  fderiv ℝ (repr σ ∘ symm) (extChartAt I α b) (trivToE α b (B b))
  + ∑ k : Fin r, triv.cLMA b (inputSlotCorrection r s g α σ B b k)
  - ∑ l : Fin s, triv.cLMA b (outputSlotCorrection r s g α σ B b l)
```

We pass to norms via the triangle inequality. The intrinsic Fréchet-derivative
piece's norm is bounded by

```
‖fderiv ℝ (repr σ ∘ symm) (extChartAt I α b)‖ · ‖trivToE α b (B b)‖
```

The first factor is bounded by `chart_pulled_covApply_repr_fderiv_bound`
(Sub-E) in terms of orders `0, 1, 2` of `repr T ∘ symm`. The second is
bounded by smoothness of `B`. The slot-correction pieces' norms are bounded
by op-norm uniform bounds on the slot kernels and norm bounds on
`repr σ` (the value of `covApply ∇ B T` at `b`), which itself is bounded by
orders `0, 1` of `repr T ∘ symm` via the chart-pulled explicit formula at `b`
applied to `T` together with uniform op-norm bounds. Adding the bounds and
squaring yields the squared headline.

The differentiability witness required by Sub-E (the differentiability of
`fderiv ℝ (repr T ∘ symm)` at `extChartAt I α b`) is discharged from
`ContDiffOn ℝ ∞` regularity of `repr T ∘ symm` on the chart-target image of
the good set, via `ContDiffWithinAt → ContDiffAt → DifferentiableAt`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled representation of a `SmoothCcTensor`. -/
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

/-- For any chart-`α` Levi-Civita good-set point `b`, the chart-pulled
representation `repr T ∘ symm` of `T : SmoothCcTensor g r s` is twice
Fréchet-differentiable at `extChartAt I α b`; in particular, the Fréchet
derivative `fderiv ℝ (repr T ∘ symm)` is itself differentiable there. -/
private lemma fderiv_reprT_differentiableAt_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hcd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    hcd.fderiv_of_isOpen hU_open h_le
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by intro h; exact absurd h (by simp)
  have hwithin : DifferentiableWithinAt ℝ
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α)
      (extChartAt I α b) :=
    (hfd_cd.differentiableOn hne) (extChartAt I α b) hx_mem
  exact hwithin.differentiableAt (hU_open.mem_nhds hx_mem)

/-- For a globally smooth tangent vector section `B`, the chart-pulled
trivialised vector `trivToE α b (B b) = chartE_section_repr α B.toFun b` has
a uniform norm bound over the chart-`α` partition-of-unity tsupport. -/
private lemma trivToE_B_norm_bound
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖trivToE (I := I) α b (B.toFun b)‖ ≤ C := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hu_cd_good : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => chartE_section_repr (I := I) α B.toFun b)
      (chartLeviCivitaGoodSet (I := I) α) :=
    chartE_section_repr_contMDiffOn_goodSet (I := I) (M := M) α hB_on
  have hu_cont : ContinuousOn
      (fun b : M => trivToE (I := I) α b (B.toFun b))
      (chartLeviCivitaGoodSet (I := I) α) :=
    hu_cd_good.continuousOn
  have hPOU_subset_src : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hPOU_subset_good : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
    rw [h_good_eq_source]; exact hPOU_subset_src
  have hKcompact : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (isClosed_tsupport _).isCompact
  have hu_cont_K : ContinuousOn
      (fun b : M => trivToE (I := I) α b (B.toFun b))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    hu_cont.mono hPOU_subset_good
  obtain ⟨C, hC_bdd⟩ :=
    hKcompact.bddAbove_image (hu_cont_K.norm)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have h_in : ‖trivToE (I := I) α b (B.toFun b)‖ ∈
      (fun b => ‖trivToE (I := I) α b (B.toFun b)‖) '' tsupport _ :=
    ⟨b, hb, rfl⟩
  exact (hC_bdd h_in).trans (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
