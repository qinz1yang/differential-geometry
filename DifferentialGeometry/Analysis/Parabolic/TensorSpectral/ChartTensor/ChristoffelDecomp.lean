import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Integral.Connection.ChartSection
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Chain-rule decomposition of partial derivatives of `(r, s)`-tensor chart components

Let `S : SmoothCcTensor g r s` be a smooth, compactly-supported `(r, s)`-tensor
section over a closed Riemannian manifold `(M, g)`, and let `α : M` be a chart
center. For each pair of multi-indices `Idx : Fin r → Fin n` and
`Jdx : Fin s → Fin n` (with `n := Module.finrank ℝ E`), the file
`Analysis/Parabolic/TensorSpectral/ChartTensor/Components.lean` defines the
chart-`α`-trivialised scalar component

```
tensorChartComponentRaw g r s S α Idx Jdx : M → ℝ.
```

This file exposes the **chain-rule decomposition** of the Fréchet derivative
of the chart-pulled-back component

```
tensorChartComponentRaw g r s S α Idx Jdx ∘ (extChartAt I α).symm  :  E → ℝ
```

at any point `extChartAt I α b` in the interior of the chart target with
`b ∈ baseSet`. The decomposition factors through the chart-trivialised
tensor function

```
tensorTrivProj g r s S α : M → TensorRSModel r s ℝ E
```

(itself smooth on the chart source by
`tensorTrivProj_contMDiffOn_chart_source`), exposing the Fréchet derivative of
the scalar component as the composition of the (constant) component
projection `tensorChartComponentProjection r s Idx Jdx` with the Fréchet
derivative of `tensorTrivProj g r s S α ∘ (extChartAt I α).symm`.

## Why this is the right decomposition

The Fréchet derivative of the scalar component at the chart point
`extChartAt I α b` is a linear functional on `E`. Splitting it via the chain
rule gives:

* a **tensorial** Fréchet derivative on `E` — the derivative of the
  chart-trivialised section as an `E → TensorRSModel`-valued function — which
  in canonical chart coordinates picks up the partial-derivative-and-Christoffel
  decomposition; and
* a **fixed** continuous linear functional — the component projection
  `tensorChartComponentProjection` — that selects the `(Idx, Jdx)` coordinate
  from a model-fibre tensor.

Downstream consumers integrating `eLpNorm`-type quantities of the scalar
component's partial derivatives only need the bound

```
‖∂_k component‖ ≤ ‖tensorChartComponentProjection‖_op · ‖∂_k (tensorTrivProj ∘ φ⁻¹)‖
```

which is immediate from this chain-rule decomposition.

## Main results

* `tensorTrivProj_chart_pullback_hasFDerivAt`
* `tensorChartComponentRaw_chart_pullback_hasFDerivAt`
* `tensorChartComponentRaw_partial_decomp`
* `tensorChartComponentRaw_mfderiv_decomp`
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The trivialization-at-`α` projection of `S.toSection` is smooth on the
chart source. -/
lemma tensorTrivProj_contMDiffOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorTrivProj (I := I) (M := M) g r s S α)
      ((chartAt H α).source) := by
  classical
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
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  refine ContMDiffOn.congr hrewrite ?_
  intro x hx
  have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [hbase]; exact hx
  unfold tensorTrivProj
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x (S.toSection x) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]

/-- `MDifferentiableAt` of `tensorTrivProj g r s S α` at a chart-source
point. -/
lemma mdifferentiableAt_tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E))
      (tensorTrivProj (I := I) (M := M) g r s S α) b := by
  have hcontMDiff := tensorTrivProj_contMDiffOn_chart_source
    (I := I) (M := M) g r s S α
  have hAt : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorTrivProj (I := I) (M := M) g r s S α) b :=
    hcontMDiff.contMDiffAt ((chartAt H α).open_source.mem_nhds hb_chart)
  exact hAt.mdifferentiableAt (by simp)

/-- The chart pull-back `tensorTrivProj g r s S α ∘ (extChartAt I α).symm` is
`DifferentiableAt ℝ` at an interior point of the chart target. -/
lemma differentiableAt_tensorTrivProj_pullback
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set φ : PartialEquiv M E := extChartAt I α
  have hf_at : MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b :=
    mdifferentiableAt_tensorTrivProj (I := I) (M := M) g r s S α hb_chart
  have hb_src : b ∈ φ.source := by
    have hb_src' : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact hb_src'
  have hbridge :
      MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b ↔
        MDifferentiableWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E))
          (fE ∘ φ.symm) (range I) (φ b) :=
    mdifferentiableAt_iff_source_of_mem_source (x := α) (x' := b) hb_chart
  have hwithin :
      MDifferentiableWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E))
        (fE ∘ φ.symm) (range I) (φ b) :=
    hbridge.mp hf_at
  have htgt : (extChartAt I α).target ⊆ range I :=
    extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hrange_nhds : range I ∈ 𝓝 (φ b) :=
    Filter.mem_of_superset (hint_open.mem_nhds hb_int)
      (interior_subset.trans htgt)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hwithin
  exact hwithin.differentiableAt hrange_nhds

/-- **Manifold derivative of `tensorTrivProj` in chart coordinates.** At a
point `b` in the chart source whose chart image lies in the interior of the
chart target, the manifold derivative of `tensorTrivProj g r s S α` at `b`
applied to a tangent vector `v` equals the Fréchet derivative of the chart
pull-back at `extChartAt I α b` applied to the canonical trivialisation
image of `v`. -/
theorem mfderiv_tensorTrivProj_eq_chart_fderiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) v =
      fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set φ : PartialEquiv M E := extChartAt I α
  set y₀ : E := φ b
  set gE : E → TensorRSModel r s ℝ E := fE ∘ φ.symm
  have hb_src : b ∈ φ.source := by
    rw [extChartAt_source]; exact hb_chart
  have hfE_eqOn : ∀ y, y ∈ φ.source → fE y = gE (φ y) := by
    intro y hy
    change fE y = fE (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hsrc_nhds : φ.source ∈ 𝓝 b :=
    extChartAt_source_mem_nhds' (I := I) hb_src
  have hev : fE =ᶠ[𝓝 b] gE ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hfE_eqOn y hy
  have hmfderiv_eq :
      mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b =
        mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) (gE ∘ φ) b :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ b :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hb_chart
  have hgE_diff : DifferentiableAt ℝ gE y₀ :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S α hb_chart hb_int
  have hgE_mdiff : MDifferentiableAt (𝓘(ℝ, E))
      (𝓘(ℝ, TensorRSModel r s ℝ E)) gE y₀ :=
    hgE_diff.mdifferentiableAt
  have hchain :
      mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E)) (gE ∘ φ) b =
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E)) gE (φ b)).comp
          (mfderiv I (𝓘(ℝ, E)) φ b) :=
    mfderiv_comp b hgE_mdiff hφ_mdiff
  have hmf_to_fderiv :
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, TensorRSModel r s ℝ E)) gE (φ b) =
        fderiv ℝ gE (φ b) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := TensorRSModel r s ℝ E)
      (f := gE) (x := φ b)
  have htriv_eq :
      mfderiv I (𝓘(ℝ, E)) (extChartAt I α) b =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := b) hb_chart).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ gE (φ b))
        ((mfderiv I (𝓘(ℝ, E)) (extChartAt I α) b) v) =
      fderiv ℝ gE y₀
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)
  rw [htriv_eq]
  rfl

/-- **HasFDerivAt for the chart-pulled-back `tensorTrivProj`.** At an interior
chart-target point, the function
`tensorTrivProj g r s S α ∘ (extChartAt I α).symm` has Fréchet derivative
equal to `fderiv` of itself. (This is a restatement of
`DifferentiableAt.hasFDerivAt`.) -/
theorem tensorTrivProj_chart_pullback_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b))
      (extChartAt I α b) :=
  (differentiableAt_tensorTrivProj_pullback (I := I) (M := M) g r s S α
    hb_chart hb_int).hasFDerivAt

/-- The chart pull-back of `tensorChartComponentRaw` equals
`tensorChartComponentProjection r s Idx Jdx` applied to the chart pull-back
of `tensorTrivProj`. -/
private lemma tensorChartComponentRaw_pullback_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm =
      (tensorChartComponentProjection (E := E) r s Idx Jdx) ∘
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm) := by
  funext y
  rfl

/-- **HasFDerivAt for the chart-pulled-back scalar component.** At an interior
chart-target point, the function
`tensorChartComponentRaw g r s S α Idx Jdx ∘ (extChartAt I α).symm`
has Fréchet derivative equal to the composition of the (constant) CLM
`tensorChartComponentProjection r s Idx Jdx` with the Fréchet derivative of
`tensorTrivProj g r s S α ∘ (extChartAt I α).symm`. -/
theorem tensorChartComponentRaw_chart_pullback_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm)
      ((tensorChartComponentProjection (E := E) r s Idx Jdx).comp
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)))
      (extChartAt I α b) := by
  classical
  have hfact := tensorChartComponentRaw_pullback_eq
    (I := I) (M := M) g r s S α Idx Jdx
  rw [hfact]
  have htriv := tensorTrivProj_chart_pullback_hasFDerivAt
    (I := I) (M := M) g r s S α hb_chart hb_int
  have hCLM_hasFDeriv :
      HasFDerivAt (tensorChartComponentProjection (E := E) r s Idx Jdx)
        ((tensorChartComponentProjection (E := E) r s Idx Jdx) :
          TensorRSModel r s ℝ E →L[ℝ] ℝ)
        ((tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)) :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).hasFDerivAt
  exact HasFDerivAt.comp (extChartAt I α b) hCLM_hasFDeriv htriv

/-- **Fréchet derivative of the chart-pulled-back component, formula form.**
The `fderiv` of `tensorChartComponentRaw g r s S α Idx Jdx ∘ (extChartAt I α).symm`
at `extChartAt I α b` equals the CLM composition `projection ∘L fderiv (triv ∘ symm)`. -/
theorem tensorChartComponentRaw_chart_pullback_fderiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b)) :=
  (tensorChartComponentRaw_chart_pullback_hasFDerivAt
    (I := I) (M := M) g r s S α Idx Jdx hb_chart hb_int).fderiv

/-- **Headline partial-derivative formula.** For `b` in the chart source at
`α` with `extChartAt I α b` in the interior of the chart target, the `k`-th
partial derivative of the chart-pulled-back scalar component
`tensorChartComponentRaw g r s S α Idx Jdx ∘ (extChartAt I α).symm` at
`extChartAt I α b` equals the component projection applied to the `k`-th
partial derivative of the chart-pulled-back tensor function
`tensorTrivProj g r s S α ∘ (extChartAt I α).symm`. -/
theorem tensorChartComponentRaw_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : E) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        (fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
          (extChartAt I α b) w) := by
  classical
  rw [tensorChartComponentRaw_chart_pullback_fderiv
    (I := I) (M := M) g r s S α Idx Jdx hb_chart hb_int]
  rfl

/-- **Manifold-derivative form of the partial-decomposition formula.** The
manifold derivative `mfderiv I 𝓘(ℝ) (tensorChartComponentRaw g r s S α Idx
Jdx) b` applied to a tangent vector `v` equals the component projection
applied to `mfderiv I 𝓘(ℝ, TensorRSModel r s ℝ E) (tensorTrivProj g r s S α)
b` applied to `v`. -/
theorem tensorChartComponentRaw_mfderiv_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b) v =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
          (tensorTrivProj (I := I) (M := M) g r s S α) b) v) := by
  classical
  set fE : M → TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α
  set P : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have hf_mdiff : MDifferentiableAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) fE b :=
    mdifferentiableAt_tensorTrivProj (I := I) (M := M) g r s S α hb_chart
  have hP_mdiff : MDifferentiableAt (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ))
      (P : TensorRSModel r s ℝ E → ℝ) (fE b) := by
    have hP_diff : ContMDiff (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ)) ∞
        (P : TensorRSModel r s ℝ E → ℝ) := P.contMDiff
    exact (hP_diff.contMDiffAt).mdifferentiableAt (by simp)
  have hcomp_eq :
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx =
        (P : TensorRSModel r s ℝ E → ℝ) ∘ fE := by
    funext x
    rfl
  rw [hcomp_eq]
  rw [mfderiv_comp b hP_mdiff hf_mdiff]
  have hP_fderiv : fderiv ℝ (P : TensorRSModel r s ℝ E → ℝ) (fE b) =
      (P : TensorRSModel r s ℝ E →L[ℝ] ℝ) :=
    P.fderiv (x := fE b)
  have hP_eq :
      mfderiv (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ))
          (P : TensorRSModel r s ℝ E → ℝ) (fE b) =
        fderiv ℝ (P : TensorRSModel r s ℝ E → ℝ) (fE b) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := TensorRSModel r s ℝ E) (E' := ℝ)
      (f := (P : TensorRSModel r s ℝ E → ℝ)) (x := fE b)
  rw [hP_eq, hP_fderiv]
  rfl

/-- **`k`-th chart-frame partial of the scalar chart component.** Feeding the
`k`-th chart-frame tangent vector at `b` into the manifold derivative of
`tensorChartComponentRaw` gives the projection of the `k`-th chart-frame
partial of `tensorTrivProj`. -/
theorem tensorChartComponentRaw_chartBasis_partial
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b)
      (chartBasisVecFiber (I := I) α k b) =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
          (tensorTrivProj (I := I) (M := M) g r s S α) b)
          (chartBasisVecFiber (I := I) α k b)) :=
  tensorChartComponentRaw_mfderiv_decomp
    (I := I) (M := M) g r s α S hb_chart Idx Jdx _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
