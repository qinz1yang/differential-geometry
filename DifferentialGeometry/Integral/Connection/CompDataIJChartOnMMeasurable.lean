import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartFormLowerOrder
import DifferentialGeometry.Analysis.Sobolev.Chart.MeasurablePullback

/-!
# Borel measurability on `M` of the chart-`α` pulled-back iterated-Fréchet-derivative
data of a raw chart-frame tensor scalar component

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a chart
base point `α : M`, a pair of multi-indices `(Idx, Jdx)`, and a derivative order
`j : ℕ`, the function

```
F_E : E → ℝ := tensorChartComponentRaw g r s T₀ α Idx Jdx ∘ (extChartAt I α).symm
```

is `C^∞` on the open Euclidean chart target `(extChartAt I α).target` (see
`chartPushedRaw_tensorChartComponentRaw_contDiffOn` of
`Analysis/Laplacian/TensorRegularity/CovDerivChartFormLowerOrder.lean`). On the
chart target, the `j`-th iterated Fréchet derivative `iteratedFDeriv ℝ j F_E` is
continuous. Composing with the chart map `extChartAt I α : M → E` and taking
norms gives a function on `M` whose Borel-measurability is the subject of this
file. Because the Mathlib partial-equiv `extChartAt I α` has unspecified
behaviour outside the chart source, we use the Borel-measurable global extension
`extChartAtExt α : M → E` from `Analysis/Sobolev/Chart/MeasurablePullback.lean`,
which agrees with `extChartAt I α` on the chart source (where the partition of
unity weights live in downstream applications).

## Main result

* `compDataIJ_chart_on_M_measurable` — the function
  `b ↦ ‖iteratedFDeriv ℝ j (tensorChartComponentRaw … ∘ (extChartAt I α).symm)
        (extChartAtExt α b)‖ ^ 2`
  is Borel-measurable on `M`.
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
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- On the open Euclidean chart target `(extChartAt I α).target`, the `j`-th
iterated Fréchet derivative of the composite
`tensorChartComponentRaw g r s T₀ α Idx Jdx ∘ (extChartAt I α).symm` is
continuous. This follows from the `C^∞`-on-target witness
`chartPushedRaw_tensorChartComponentRaw_contDiffOn` together with
`ContDiffOn.continuousOn_iteratedFDerivWithin` and the open-set identification
`iteratedFDerivWithin = iteratedFDeriv` on open sets. -/
lemma iteratedFDeriv_tensorChartComponentRaw_comp_symm_continuousOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    ContinuousOn
      (fun y : E =>
        iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx ∘
            (extChartAt I α).symm)
          y)
      ((extChartAt I α).target) := by
  classical
  have hraw_src : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M)
      g r s T₀ α Idx Jdx
  have hraw_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
      ((extChartAt I α).source) := by
    rw [extChartAt_source]; exact hraw_src
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hraw_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp_E.contDiffOn
  have hopen : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  have hcontWithin :
      ContinuousOn
        (iteratedFDerivWithin ℝ j
          ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
            (extChartAt I α).symm)
          (extChartAt I α).target)
        ((extChartAt I α).target) :=
    hcontDiff_E.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
      hopen.uniqueDiffOn
  refine hcontWithin.congr (fun y hy => ?_)
  exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
      (extChartAt I α).symm) j hopen hy).symm

/-- The composite `b ↦ iteratedFDeriv ℝ j F_E (extChartAt I α b)` (with
`F_E := tensorChartComponentRaw g r s T₀ α Idx Jdx ∘ (extChartAt I α).symm`) is
continuous on the chart source `(chartAt H α).source`. -/
private lemma comp_extChartAt_continuousOn_chart_source
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    ContinuousOn
      (fun b : M =>
        iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx ∘
            (extChartAt I α).symm)
          ((extChartAt I α) b))
      ((chartAt H α).source) := by
  classical
  have hcont_target :=
    iteratedFDeriv_tensorChartComponentRaw_comp_symm_continuousOn
      (I := I) (M := M) g r s T₀ α Idx Jdx j
  have hext_cont : ContinuousOn (fun b : M => (extChartAt I α) b)
      ((extChartAt I α).source) := continuousOn_extChartAt (I := I) α
  have hsrc_eq : (extChartAt I α).source = (chartAt H α).source :=
    extChartAt_source (I := I) α
  rw [hsrc_eq] at hext_cont
  have hmaps : Set.MapsTo (fun b : M => (extChartAt I α) b)
      ((chartAt H α).source) ((extChartAt I α).target) := by
    intro b hb
    have hb' : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hb
    exact (extChartAt I α).map_source hb'
  exact hcont_target.comp hext_cont hmaps

/-- The composite `b ↦ iteratedFDeriv ℝ j F_E (extChartAtExt α b)` is continuous
on the chart source. On the chart source, `extChartAtExt α = extChartAt I α`, so
this reduces to `comp_extChartAt_continuousOn_chart_source`. -/
private lemma comp_extChartAtExt_continuousOn_chart_source
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    ContinuousOn
      (fun b : M =>
        iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx ∘
            (extChartAt I α).symm)
          (extChartAtExt (I := I) α b))
      ((chartAt H α).source) := by
  classical
  have hcont :=
    comp_extChartAt_continuousOn_chart_source
      (I := I) (M := M) g r s T₀ α Idx Jdx j
  refine hcont.congr (fun b hb => ?_)
  have h_eq : extChartAtExt (I := I) α b = (extChartAt I α) b :=
    extChartAtExt_apply_of_mem (I := I) (α := α) hb
  rw [h_eq]

/-- **Borel-measurability on `M` of the chart-`α` pulled-back iterated Fréchet
derivative data.**

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported tensor section `T₀`, a chart base point `α`, multi-indices
`(Idx, Jdx)`, and an order `j : ℕ`, the function

```
b ↦ ‖iteratedFDeriv ℝ j (tensorChartComponentRaw … ∘ (extChartAt I α).symm)
       (extChartAtExt α b)‖ ^ 2
```

is Borel-measurable on `M`. Here `extChartAtExt α : M → E` is the globally
Borel-measurable extension of `extChartAt I α`, taking the value `0` outside the
chart source. On the chart source it agrees pointwise with `extChartAt I α`, so
this measurability statement covers all downstream uses inside any integrand
multiplied by a chart-`α`-subordinate weight (in particular the partition of
unity, whose `tsupport` is contained in the chart source).

The proof identifies the composite with a function continuous on the open chart
source and constant (zero) outside, then invokes
`ContinuousOn.measurable_piecewise`. -/
theorem compDataIJ_chart_on_M_measurable
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    Measurable (fun b : M =>
      ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx ∘
            (extChartAt I α).symm)
          (extChartAtExt (I := I) α b)‖ ^ 2) := by
  classical
  set f : M → (E [×j]→L[ℝ] ℝ) := fun b =>
    iteratedFDeriv ℝ j
      ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAtExt (I := I) α b) with hf_def
  have hf_cont_src : ContinuousOn f ((chartAt H α).source) := by
    rw [hf_def]
    exact comp_extChartAtExt_continuousOn_chart_source
      (I := I) (M := M) g r s T₀ α Idx Jdx j
  have hsrc_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hsrc_meas : MeasurableSet ((chartAt H α).source) := hsrc_open.measurableSet
  have hzero_cont : ContinuousOn (fun _ : M => (0 : (E [×j]→L[ℝ] ℝ)))
      ((chartAt H α).source)ᶜ := continuous_const.continuousOn
  set f_pw : M → (E [×j]→L[ℝ] ℝ) := ((chartAt H α).source).piecewise f (fun _ => 0)
    with hf_pw_def
  have hf_pw_meas : Measurable f_pw := by
    rw [hf_pw_def]
    exact ContinuousOn.measurable_piecewise hf_cont_src hzero_cont hsrc_meas
  set c : E [×j]→L[ℝ] ℝ :=
    iteratedFDeriv ℝ j
      ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
        (extChartAt I α).symm) 0 with hc_def
  have h_target_eq : (fun b : M => ‖f b‖ ^ 2) =
      ((chartAt H α).source).piecewise
        (fun b : M => ‖f b‖ ^ 2)
        (fun _ : M => ‖c‖ ^ 2) := by
    funext b
    by_cases hb : b ∈ (chartAt H α).source
    · rw [Set.piecewise_eq_of_mem _ _ _ hb]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hb]
      have hext_zero : extChartAtExt (I := I) α b = 0 :=
        extChartAtExt_apply_of_notMem (I := I) (α := α) hb
      have hf_b : f b = c := by
        change iteratedFDeriv ℝ j
            ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
              (extChartAt I α).symm)
            (extChartAtExt (I := I) α b) = _
        rw [hext_zero]
      rw [hf_b]
  rw [h_target_eq]
  have hf_norm_sq_cont : ContinuousOn (fun b : M => ‖f b‖ ^ 2)
      ((chartAt H α).source) :=
    (hf_cont_src.norm).pow 2
  have hconst_cont : ContinuousOn (fun _ : M => ‖c‖ ^ 2)
      ((chartAt H α).source)ᶜ := continuous_const.continuousOn
  exact ContinuousOn.measurable_piecewise hf_norm_sq_cont hconst_cont hsrc_meas

end Connection
end Integral
end DifferentialGeometry
