import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartCoeffPullback
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Action of a smooth tangent section on a smooth scalar function

For a smooth tangent section `X` and a smooth scalar function `f : M → ℝ`,
the *tangent action* `tangentSectionAction X f x := mfderiv I 𝓘(ℝ) f x (X x)` is
the directional derivative of `f` along `X` at `x`. This is an intrinsic
operation — no chart appears in the definition.

This file develops two facts about `tangentSectionAction`:

1. **Smoothness**: if `X` is a smooth tangent section and `f` is smooth, then
   `tangentSectionAction X f` is a smooth real-valued function on `M`.
2. **Chart-local representation**: in any chart `α : M`, on the chart base set,
   `tangentSectionAction X f x = ∑ i, chartCoeff α X i x · partialDeriv i (f ∘ symm) (φ x)`,
   where `partialDeriv` is the model-space partial derivative in the direction
   of the `i`-th model basis vector.

These are the standard coordinate identities. Together they provide the
intrinsic right-hand side of the chart-local integration-by-parts identity used
later for chart-invariance of the chart-local Voss–Weyl divergence.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The action of a smooth tangent section `X` on a smooth scalar function
`f : M → ℝ` at a point `x : M`. By definition, this is the directional
derivative `mfderiv I 𝓘(ℝ) f x (X x)`. -/
def tangentSectionAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) : M → ℝ :=
  fun x => mfderiv I 𝓘(ℝ) f x (X x)

@[simp] lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x) := rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
/-- The tangent action obeys the scalar Leibniz rule at points where both
factors are manifold-differentiable. -/
theorem tangent_mul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    tangentSectionAction (I := I) X (fun y => f y * h y) x =
      f x * tangentSectionAction (I := I) X h x +
        h x * tangentSectionAction (I := I) X f x := by
  have hmul := (hf.hasMFDerivAt.mul hh.hasMFDerivAt).mfderiv
  unfold tangentSectionAction
  change (mfderiv I 𝓘(ℝ, ℝ) (f * h) x) (X x) = _
  rw [hmul]
  rfl

/-- The pullback of `f : M → ℝ` through the chart inverse, viewed as a function
on the chart target `(extChartAt I α).target ⊆ E`. -/
def scalarOnE (α : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I α).symm y)

@[simp] lemma scalarOnE_def (α : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) α f y = f ((extChartAt I α).symm y) := rfl

/-- The chart pullback of a scalar function, extended by zero outside the
extended-chart target. -/
def chartPullZero (α : M) (f : M → ℝ) : E → ℝ :=
  (extChartAt I α).target.indicator (scalarOnE (I := I) α f)

lemma chartPullZero_mem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = scalarOnE (I := I) α f y :=
  Set.indicator_of_mem hy _

lemma chartPullZero_nmem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = 0 :=
  Set.indicator_of_notMem hy _

/-- The map `f : M → ℝ` on the chart source equals the composition of its
chart-pullback `scalarOnE α f` with the extended chart. -/
lemma scalarOnE_extChartAt (α : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I α).source) :
    scalarOnE (I := I) α f (extChartAt I α x) = f x := by
  change f ((extChartAt I α).symm (extChartAt I α x)) = f x
  rw [(extChartAt I α).left_inv hx]

/-- Smoothness of the pullback `scalarOnE α f` of a smooth function `f`. -/
lemma scalarOnE_contDiffOn (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hf_on.comp hsymm (fun _ _ => mem_univ _)
  exact hcomp.contDiffOn

/-- Smoothness of the chart-pulled-back function `scalarOnE α f`, restricted
to a continuous-differentiability statement on `E`. -/
lemma scalarOnE_contDiffWithinAt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target y :=
  scalarOnE_contDiffOn (I := I) α hf y hy

/-- At a point where the scalar chart pullback is differentiable, the
manifold derivative on a chart-basis vector is the corresponding Euclidean
partial derivative. -/
lemma mfderiv_chart_diff (α : M)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) α f) (extChartAt I α x))
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hcomp_eq : ∀ᶠ y in 𝓝 x,
      f y = (scalarOnE (I := I) α f) (φ y) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x]
      (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  rw [Filter.EventuallyEq.mfderiv_eq hcong]
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (scalarOnE (I := I) α f) (φ x) := hf.mdifferentiableAt
  rw [mfderiv_comp x hg_diff hφ_diff]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) =
      fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x) = (chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : chartBasisVecFiber (I := I) α i x =
        T.symm x ((chartModelBasis E) i) := rfl
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i)) =
          (chartModelBasis E) i := by
      have : T.symm x ((chartModelBasis E) i) =
          T.symmL ℝ x ((chartModelBasis E) i) := by
        rw [Trivialization.symmL_apply]
      rw [this, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)) = _
  rw [hmfderiv_chartBasis]
  rfl

/-- Decomposition: applying `mfderiv` of `f` at `x` to the chart-basis frame
vector at index `i`, using the chart at `α`. The model space is `E`, so this is
just `partialDeriv i (scalarOnE α f) (φ_α x)`. To prove this we use the chain
rule `f = scalarOnE α f ∘ extChartAt I α` near `x`, plus the fact that
`mfderiv (extChartAt I α) x` sends the chart-basis frame at `α` to the model
basis (as a continuous linear map). -/
lemma mfderiv_chartBasisVecFiber (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (chartBasisVecFiber (I := I) α i x)
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  have hscalar_smooth :=
    scalarOnE_contDiffOn (I := I) α hf
  have hint_open : IsOpen (interior φ.target) := isOpen_interior
  have hsubset : interior φ.target ⊆ φ.target := interior_subset
  have hscalar_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (φ x) := by
    have h_within : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α f) φ.target (φ x) := hscalar_smooth (φ x) (hsubset hx_int)
    exact h_within.contDiffAt (mem_nhds_iff.mpr ⟨interior φ.target, hsubset, hint_open, hx_int⟩)
  have hscalar_diff : DifferentiableAt ℝ (scalarOnE (I := I) α f) (φ x) :=
    hscalar_at.differentiableAt (by simp)
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  set L : E →L[ℝ] ℝ := fderiv ℝ (scalarOnE (I := I) α f) (φ x)
  have hf_mfderiv := hf_mdiff_at.mfderiv
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) :=
    hscalar_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_diff hphi_diff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)
        = (chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : chartBasisVecFiber (I := I) α i x = T.symm x ((chartModelBasis E) i) :=
      rfl
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i))
          = (chartModelBasis E) i := by
      have : T.symm x ((chartModelBasis E) i)
            = T.symmL ℝ x ((chartModelBasis E) i) := by
        rw [Trivialization.symmL_apply]
      rw [this, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (chartBasisVecFiber (I := I) α i x))
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

/-- **Chart-local representation of `tangentSectionAction`.**
For `f : M → ℝ` smooth, `X` a smooth tangent section, `α : M`, and `x` in
the chart base set at `α` whose chart image lies in the interior of the chart
target,
`tangentSectionAction X f x = ∑ᵢ chartCoeff α X i x * partialDeriv i (scalarOnE α f) (φ_α x)`.
Both sides are equal as values in `ℝ`. The right-hand side depends on `α`
even though the left-hand side does not — this is the standard component-vs-action
duality. -/
theorem tangentSectionAction_chartLocal
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
        chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  rw [mfderiv_chartBasisVecFiber (I := I) α hf hx hx_int i]
  exact smul_eq_mul ..

/-- Under `[I.Boundaryless]`, the chart target is open and equals its interior. -/
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

/-- At a differentiability point of the zero-extended chart pullback, a
smooth tangent section acts by the corresponding finite sum of coordinate
line derivatives. -/
theorem tangent_chart_diff [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (chartPullZero (I := I) α f)
      (extChartAt I α x)) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          lineDeriv ℝ (chartPullZero (I := I) α f) (extChartAt I α x)
            ((chartModelBasis E) i) := by
  classical
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hx
  have hxy : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have heq : chartPullZero (I := I) α f =ᶠ[𝓝 (extChartAt I α x)]
      scalarOnE (I := I) α f := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hxy] with y hy
    exact chartPullZero_mem (I := I) α f hy
  have hscalar : DifferentiableAt ℝ (scalarOnE (I := I) α f)
      (extChartAt I α x) := hf.congr_of_eventuallyEq heq.symm
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
      chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, mfderiv_chart_diff (I := I) α hx hscalar i]
  unfold partialDeriv
  rw [← heq.fderiv_eq, ← hf.lineDeriv_eq_fderiv]
  exact smul_eq_mul ..

/-- Under `[I.Boundaryless]`, the chart-local representation holds for any
point in the chart base set. -/
theorem tangentSectionAction_chartLocal_of_boundaryless [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact tangentSectionAction_chartLocal (I := I) α X hf hx hx_int

/-- The pulled-back partial derivative is smooth on the interior of the chart
target. -/
private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- The pulled-back partial derivative composed with the chart map is smooth
on the smoothness domain. -/
private lemma partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hpartial : ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
        (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

/-- `tangentSectionAction X f` is `C^∞` on the chart base set at `α` whose chart
image lies in the interior of the chart target. -/
theorem tangentSectionAction_contMDiffOn
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  set U : Set M := (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target with hU_def
  have hcongr : ∀ x ∈ U,
      tangentSectionAction (I := I) X f x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α X i x *
            partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro x hx
    have hx_chart : x ∈ (chartAt H α).source := by
      have := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact tangentSectionAction_chartLocal (I := I) α X hf hx_chart hx.2
  refine ContMDiffOn.congr ?_ hcongr
  refine contMDiffOn_finset_sum (fun i _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartCoeff_contMDiffOn (I := I) α X i
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · exact partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf i

/-- Under `[I.Boundaryless]`, `tangentSectionAction X f` is `C^∞` on the entire
chart base set at `α`. -/
theorem tangentSectionAction_contMDiffOn_baseSet [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H α).source := by
  refine (tangentSectionAction_contMDiffOn (I := I) α X hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

/-- `tangentSectionAction X f` is `C^∞` on `M` (under `[I.Boundaryless]`),
since smoothness can be established locally in any chart. -/
theorem tangentSectionAction_contMDiff [I.Boundaryless]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H x).source :=
    tangentSectionAction_contMDiffOn_baseSet (I := I) x X hf
  exact (hsmooth x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DivergenceTheorem
end Integral
end DifferentialGeometry
