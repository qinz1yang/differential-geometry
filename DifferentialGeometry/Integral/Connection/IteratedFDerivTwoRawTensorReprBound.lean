import DifferentialGeometry.Integral.Connection.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.ChartPulledRawTensorReprFactorization
import DifferentialGeometry.Integral.Connection.IteratedFDerivFourTensorReprChartCompBound
import DifferentialGeometry.Integral.Connection.IteratedFDerivTwoRawTensorConnLapChartCompBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartKernel
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.Connection.RawTensorConnLapPointwiseBound
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Pointwise order-2 squared norm bound on the chart-pulled representation of
the raw tensor connection Laplacian by orders 0..4 of the chart-pulled
representation of `T`

This file is part of the chain of squared-norm bounds connecting the bundled
raw tensor connection Laplacian to a manifold Sobolev norm of the underlying
smooth compactly supported tensor section.

## Smoothness regularity prerequisite

The downstream order-2 iterated-Fréchet-derivative bound rests on the
`ContDiffOn ℝ ∞` regularity of the chart-pulled representation
`(tensorRSChartE_section_repr r s α (raw T)) ∘ (extChartAt I α).symm` on
the chart-target image of the chart-`α` Levi-Civita good set. This regularity
is the analog of `reprT_contDiffOn_goodSet` (already present in
`RawTensorConnLapNormSqChartPulledReprBound.lean`) but for the raw tensor
connection Laplacian section instead of an arbitrary smooth compactly
supported tensor section. It follows immediately from the bundled smoothness
of `rawTensorConnLapSmooth g r s T : SmoothCcTensor g r s` by applying the
existing template.

This file ships the regularity lemma.

The order-2 squared norm bound proper — namely

```
‖iteratedFDeriv ℝ 2 ((repr (raw T)) ∘ symm) (extChartAt I α b)‖ ^ 2 ≤
  K * ∑ j : Fin 5,
    ‖iteratedFDeriv ℝ j.val ((repr T) ∘ symm) (extChartAt I α b)‖ ^ 2
```

— requires combining (a) the chart-pulled covApply explicit-formula
expansion of `(repr (raw T)) ∘ symm` into Fréchet-derivative pieces in
`(repr T) ∘ symm` together with smooth bounded chart coefficients, (b)
applying the higher-order Leibniz rule and chain rule to differentiate twice
in chart coordinates, and (c) per-summand bounds in terms of orders 0..4 of
`(repr T) ∘ symm` with uniform coefficient bounds drawn from the chart frame
normalisation, the chart Christoffel data, and the chart-pulled covApply
Fréchet-derivative kernel. That step is the next sub-task in the dependency
graph for the chart-pulled order-2 raw tensor representation bound; it is
out of scope for this file and is left to a follow-on file. -/

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

private lemma raw_reprT_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (rawTensorConnLapSmooth (I := I) g r s T).toSection y) ∘
        (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  set S : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s T
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
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
          (fun y : M => S.toSection y) b)
        ((chartAt H α).source) := by
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x
        (S.toSection x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hcm_on_good :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) b)
        (chartLeviCivitaGoodSet (I := I) α) := by
    rw [h_good_eq_source]; exact hcm_on_source
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hx_good, rfl⟩
  set F : M → TensorRSModel r s ℝ E :=
    fun b : M => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => S.toSection y') b with hF_def
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

/-- **Public smoothness regularity statement.** For any smooth compactly
supported `(r, s)`-tensor section `T`, the chart-pulled representation of
`rawTensorConnLapSmooth g r s T` is `ContDiffOn ℝ ∞` on the chart-target
image of the chart-`α` Levi-Civita good set. This regularity statement is the
foundational ingredient for any pointwise order-`N` Fréchet-derivative bound
on `(repr (raw T)) ∘ symm`. -/
theorem rawTensorRepr_chart_pulled_contDiffOn_goodSet_image
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (rawTensorConnLapSmooth (I := I) g r s T).toSection y) ∘
        (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
  raw_reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T

/-- `ContDiffAt ℝ N` at a good-set chart-coord point for any `N : ℕ`. -/
theorem rawTensorRepr_chart_pulled_contDiffAt_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) (N : ℕ) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ N
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (rawTensorConnLapSmooth (I := I) g r s T).toSection y) ∘
        (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hcd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (rawTensorConnLapSmooth (I := I) g r s T).toSection y) ∘
        (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    rawTensorRepr_chart_pulled_contDiffOn_goodSet_image
      (I := I) (M := M) g r s α T
  have hat : ContDiffAt ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (rawTensorConnLapSmooth (I := I) g r s T).toSection y) ∘
        (extChartAt I α).symm)
      (extChartAt I α b) :=
    hcd.contDiffAt (hU_open.mem_nhds hx_mem)
  have hN_le : (N : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (N : ℕ∞) ≤ ⊤)
  exact hat.of_le hN_le

end Connection
end Integral
end DifferentialGeometry

end
