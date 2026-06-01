import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Global
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Gradient of a smooth function on a Riemannian manifold (with boundary)

This file extends the construction of the metric gradient `gradFun g f` from the
boundaryless case to manifolds whose local model `I : ModelWithCorners ℝ E H`
may carry a non-trivial boundary.

The Riesz machinery — the musical flat linear equivalence
`metricFlatMap g x : TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ)`, the
sharp `metricSharp g x α := (metricFlatMap g x).symm α`, and the resulting
pointwise gradient `gradFun g f x := metricSharp g x (mfderiv f x).toLinearMap`
— is purely fiberwise linear algebra and is reused verbatim from the boundaryless
file. None of these constructions reference the chart target, so they are
boundary-agnostic.

The new content of this file is:

* the chart-local representation `gradChartLocalWithin` of the gradient using
  `partialDerivWithin (extChartAt I α).target` instead of the Fréchet partial
  derivative `partialDeriv`, which is well posed at every chart-source point
  (including boundary points of the chart target);
* the identification `gradChartLocalWithin g α f = gradFun g f` on the chart
  base set; and
* the smoothness of `gradFun g f` as a tangent-bundle section on the manifold
  interior `I.interior M`.

On the manifold interior, `gradFun g f` agrees with the boundaryless gradient
and inherits all of its properties through the boundary-agnostic intrinsic
identities.

## Main definitions

* `gradChartLocalWithin g α f x` — the chart-local representation of the
  gradient at `x`, in the chart at `α`, using `partialDerivWithin` on the chart
  target.
* `grad_g_with_boundary g f` — the underlying pointwise gradient function,
  defined as `gradFun g f`. Smooth as a function on `I.interior M`; junk
  outside.

## Main results

* `gradChartLocalWithin_eq_gradFun` — the within chart-local formula equals the
  intrinsic gradient on the chart base set.
* `gradFun_contMDiffOn_interior` — `C^∞` smoothness of the underlying pointwise
  gradient as a tangent-bundle section on the manifold interior.
* `tangentSectionAction_grad_g_with_boundary_eq_inner` — duality with the
  tangent-section action: the action of any smooth tangent section on a smooth
  function equals the metric inner product with the gradient.
* `inner_grad_g_with_boundary_symm` — symmetry of the metric on two gradients.
* `support_grad_g_with_boundary_subset` — the support of the gradient is
  contained in the topological support of the underlying scalar function.
* `hasCompactSupport_grad_g_with_boundary` — compact-support transfer to the
  gradient when the underlying function has compact support contained in the
  manifold interior.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

export DifferentialGeometry.Integral.DivergenceTheorem
  (metricFlatLinear metricFlatLinear_apply metricFlatLinear_injective
    metricFlatMap metricFlatMap_apply metricFlatMap_apply_symm
    metricSharp metricSharp_def
    inner_metricSharp inner_metricSharp_right
    gradFun gradFun_def
    inner_gradFun inner_gradFun_right
    gradFun_eq_zero_of_mfderiv_eq_zero
    gradFun_eq_zero_of_eventuallyEq_zero
    support_gradFun_subset
    chartInvGramMatrix
    chartInvGramMatrix_mul_chartGramMatrix
    chartGramMatrix_mul_chartInvGramMatrix
    chartInvGramMatrix_entry_contMDiffOn)

/-- The `i`-th chart-basis component of the gradient at `x`, in the chart at
`α`, computed via `partialDerivWithin` on the chart target.

This is the with-boundary analogue of the boundaryless `gradChartCoeff`: the
formula coincides with `gradChartCoeff` at every interior point of the chart
target (where `partialDerivWithin` reduces to `partialDeriv`), and is
well-posed even at boundary points. -/
def gradChartCoeffWithin (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma gradChartCoeffWithin_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradChartCoeffWithin (I := I) g α f i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDerivWithin (E := E) (extChartAt I α).target j
            (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

/-- The chart-local representation of the gradient as a linear combination of
the chart-basis frame at `α`, using `partialDerivWithin` on the chart target. -/
def gradChartLocalWithin (g : SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (x : M) : TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    gradChartCoeffWithin (I := I) g α f i x •
      chartBasisVecFiber (I := I) α i x

/-- Auxiliary: the chart-pullback `scalarOnE α f` is `MDifferentiableWithinAt`
on the chart target at any chart-target point, when `f` is smooth on `M`. -/
private lemma scalarOnE_mdifferentiableWithinAt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (scalarOnE (I := I) α f) (extChartAt I α).target y := by
  have hcont : ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target y :=
    scalarOnE_contDiffWithinAt (I := I) α hf hy
  have hdiff : DifferentiableWithinAt ℝ (scalarOnE (I := I) α f)
      (extChartAt I α).target y :=
    hcont.differentiableWithinAt (by simp)
  exact hdiff.mdifferentiableWithinAt

/-- Auxiliary: the chart map `extChartAt I α : M → E` sends every chart-source
point into the chart target. -/
private lemma extChartAt_mapsTo_target_of_chart_source (α : M) :
    Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
  intro x hx
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hx'

/-- Auxiliary: the chart-basis vector identity. The mfderiv of `extChartAt I α`
applied to the chart-basis vector returns the constant model-basis vector. This
is intrinsic — it holds at every chart-source point, no interior precondition.
-/
private lemma mfderiv_extChartAt_chartBasisVecFiber'
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
        (chartBasisVecFiber (I := I) α i x)
      = (chartModelBasis E) i := by
  classical
  let T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hbase : x ∈ T.baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (T.continuousLinearMapAt ℝ x : TangentSpace I x →L[ℝ] E) := by
    change mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :
        TangentSpace I x →L[ℝ] E)
    exact (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx).symm
  rw [hmfderiv_eq]
  change T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i))
    = (chartModelBasis E) i
  rw [show T.symm x ((chartModelBasis E) i) =
        T.symmL ℝ x ((chartModelBasis E) i) from by
      rw [Trivialization.symmL_apply]]
  exact Trivialization.continuousLinearMapAt_symmL (R := ℝ) T (b := x) hbase
    ((chartModelBasis E) i)

/-- Auxiliary: equality of `mfderivWithin` on an open set with `mfderiv`. -/
private lemma mfderivWithin_extChartAt_open (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) (chartAt H α).source x =
      mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x :=
  mfderivWithin_of_isOpen (chartAt H α).open_source hx

/-- Auxiliary: equality of `mfderivWithin` of `f` on an open set with
`mfderiv`. -/
private lemma mfderivWithin_chart_source_of_mdiff'
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (f : M → ℝ) :
    mfderivWithin I 𝓘(ℝ, ℝ) f (chartAt H α).source x = mfderiv I 𝓘(ℝ, ℝ) f x :=
  mfderivWithin_of_isOpen (chartAt H α).open_source hx

/-- Within-aware factorisation of `mfderiv` for a smooth `f : M → ℝ` through
the chart map. -/
private lemma mfderiv_factor_through_extChartAt'
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ) f x v =
      (fderivWithin ℝ (scalarOnE (I := I) α f)
          (extChartAt I α).target ((extChartAt I α) x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x) v) := by
  classical
  set s : Set M := (chartAt H α).source with hs_def
  have hs_open : IsOpen s := (chartAt H α).open_source
  have hxs : x ∈ s := hx
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  have hphi_mdiff_at : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  set y₀ : E := (extChartAt I α) x
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    extChartAt_mapsTo_target_of_chart_source (I := I) α hx
  have hf_mdiffWithin : MDifferentiableWithinAt I 𝓘(ℝ, ℝ) f s x :=
    hf_mdiff_at.mdifferentiableWithinAt
  have hphi_mdiffWithin : MDifferentiableWithinAt I 𝓘(ℝ, E) (extChartAt I α) s x :=
    hphi_mdiff_at.mdifferentiableWithinAt
  have hsubset : s ⊆ (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
    fun z hz => extChartAt_mapsTo_target_of_chart_source (I := I) α hz
  have hscalar_mdiffWithin :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f)
        (extChartAt I α).target y₀ :=
    scalarOnE_mdifferentiableWithinAt (I := I) α hf hy₀_target
  have hcomp_eq : ∀ z ∈ s, f z = (scalarOnE (I := I) α f) ((extChartAt I α) z) := by
    intro z hz
    have hzsrc : z ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hz
    rw [scalarOnE_def, (extChartAt I α).left_inv hzsrc]
  have hcomp_evEq : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := by
    filter_upwards [hs_open.mem_nhds hxs] with z hz
    exact hcomp_eq z hz
  have huniq : UniqueMDiffWithinAt I s x := hs_open.uniqueMDiffWithinAt hxs
  have hcomp_within :
      mfderivWithin I 𝓘(ℝ, ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) s x =
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f)
            (extChartAt I α).target y₀).comp
          (mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) s x) :=
    mfderivWithin_comp x hscalar_mdiffWithin hphi_mdiffWithin hsubset huniq
  have hmfderiv_phi :
      mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) s x =
        mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x :=
    mfderivWithin_extChartAt_open (I := I) α hx
  have hmfderiv_f_eq :
      mfderiv I 𝓘(ℝ, ℝ) f x =
        mfderiv I 𝓘(ℝ, ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) x :=
    Filter.EventuallyEq.mfderiv_eq hcomp_evEq
  have hmfderiv_comp_within_to_full :
      mfderivWithin I 𝓘(ℝ, ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) s x =
        mfderiv I 𝓘(ℝ, ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) x :=
    mfderivWithin_chart_source_of_mdiff' (I := I) α hx _
  have hgoal_full :
      mfderiv I 𝓘(ℝ, ℝ) f x =
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f)
            (extChartAt I α).target y₀).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x) := by
    rw [hmfderiv_f_eq, ← hmfderiv_comp_within_to_full, hcomp_within, hmfderiv_phi]
  have hscalar_mfd_eq_fd :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f)
          (extChartAt I α).target y₀ =
        fderivWithin ℝ (scalarOnE (I := I) α f)
          (extChartAt I α).target y₀ :=
    mfderivWithin_eq_fderivWithin
  rw [hgoal_full, hscalar_mfd_eq_fd]
  rfl

/-- The within chart-basis evaluation lemma: `mfderiv I 𝓘(ℝ) f x` applied to
`chartBasisVecFiber α i x` equals
`partialDerivWithin (extChartAt I α).target i (scalarOnE α f) ((extChartAt I α) x)`,
for any chart-source point `x` and any smooth `f : M → ℝ`. -/
lemma mfderiv_chartBasisVecFiber_within_of_smooth
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f x
        (chartBasisVecFiber (I := I) α i x) =
      partialDerivWithin (E := E) (extChartAt I α).target i
        (scalarOnE (I := I) α f) ((extChartAt I α) x) := by
  classical
  rw [mfderiv_factor_through_extChartAt' (I := I) α hf hx
        (chartBasisVecFiber (I := I) α i x)]
  rw [mfderiv_extChartAt_chartBasisVecFiber' (I := I) α hx i]
  rfl

/-- The inner product of `gradChartLocalWithin g α f x` with a chart-basis frame
vector `e_k` equals the `k`-th within partial derivative of the chart-pullback
of `f`. Pure linear-algebra step using only the inverse Gram matrix identity
and the symmetry of `g`. -/
lemma inner_gradChartLocalWithin_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (gradChartLocalWithin (I := I) g α f x)
        (chartBasisVecFiber (I := I) α k x)
      = partialDerivWithin (E := E) (extChartAt I α).target k
          (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  unfold gradChartLocalWithin
  rw [show g.inner x (∑ i, gradChartCoeffWithin (I := I) g α f i x •
            chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α k x) =
        ∑ i, gradChartCoeffWithin (I := I) g α f i x *
          g.inner x (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [show (g.inner x (∑ i, gradChartCoeffWithin (I := I) g α f i x •
              chartBasisVecFiber (I := I) α i x)) =
          (∑ i, gradChartCoeffWithin (I := I) g α f i x •
              g.inner x (chartBasisVecFiber (I := I) α i x)) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  have ha : ∀ i, gradChartCoeffWithin (I := I) g α f i x =
      ∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f) (extChartAt I α x) := fun _ => rfl
  rw [show ∑ i, gradChartCoeffWithin (I := I) g α f i x *
            g.inner x (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α k x) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α x)) *
              chartGramMatrix (I := I) g α x i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    rfl
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              partialDerivWithin (E := E) (extChartAt I α).target j
                (scalarOnE (I := I) α f) (extChartAt I α x)) *
                chartGramMatrix (I := I) g α x i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α x) from ?_]
  swap
  · rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                partialDerivWithin (E := E) (extChartAt I α).target j
                  (scalarOnE (I := I) α f) (extChartAt I α x)) *
                  chartGramMatrix (I := I) g α x i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α x i j *
                  chartGramMatrix (I := I) g α x i k) *
                  partialDerivWithin (E := E) (extChartAt I α).target j
                    (scalarOnE (I := I) α f) (extChartAt I α x) from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hsym : ∀ i, chartGramMatrix (I := I) g α x i k =
      chartGramMatrix (I := I) g α x k i := fun _ => g.symm x _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
        chartGramMatrix (I := I) g α x i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) =
            (∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    have hidentity : (chartGramMatrix (I := I) g α x *
          chartInvGramMatrix (I := I) g α x) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
            chartGramMatrix (I := I) g α x i k) *
              partialDerivWithin (E := E) (extChartAt I α).target j
                (scalarOnE (I := I) α f) (extChartAt I α x) =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α x) from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The chart-local representation `gradChartLocalWithin` agrees with the
intrinsic gradient `gradFun` at every chart-source point, for any smooth
`f : M → ℝ`. No interior precondition is required. -/
theorem gradChartLocalWithin_eq_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    gradChartLocalWithin (I := I) g α f x = gradFun (I := I) g f x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hf'_def
  have hmfderiv_basis : ∀ k, f' (chartBasisVecFiber (I := I) α k x) =
      partialDerivWithin (E := E) (extChartAt I α).target k
        (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    rw [hf'_def]
    exact mfderiv_chartBasisVecFiber_within_of_smooth (I := I) α hf hx k
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradChartLocalWithin (I := I) g α f x) v =
    g.inner x (gradFun (I := I) g f x) v
  rw [inner_gradFun (I := I) g f x v]
  change g.inner x (gradChartLocalWithin (I := I) g α f x) v = f' v
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hbase
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => b.repr v k
  have hv_decomp : v = ∑ k, c k • chartBasisVecFiber (I := I) α k x := by
    have h1 : v = ∑ k, b.repr v k • b k := (b.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartBasisFamily_apply (I := I) α hbase k]
  rw [hv_decomp]
  rw [show g.inner x (gradChartLocalWithin (I := I) g α f x)
        (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * g.inner x (gradChartLocalWithin (I := I) g α f x)
          (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show f' (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * f' (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_gradChartLocalWithin_chartBasis (I := I) g α f hbase k,
    hmfderiv_basis k]

/-- The within chart-coefficient `gradChartCoeffWithin g α f i` is `C^∞` on
the smoothness domain (chart source intersected with the preimage of the
interior of the chart target). -/
private lemma gradChartCoeffWithin_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeffWithin (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
      uniqueDiffOn_extChartAt_target (I := I) α
    have hbase : ContDiffOn ℝ ∞
        (scalarOnE (I := I) α f) (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α hf
    have hpartial_target : ContDiffOn ℝ ∞
        (partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f))
        (extChartAt I α).target :=
      partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
    have hpartial : ContDiffOn ℝ ∞
        (partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) :=
      hpartial_target.mono interior_subset
    have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f))
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

/-- The chart-local within-representation `gradChartLocalWithin g α f` is
smooth as a tangent-bundle section on the smoothness domain. -/
private lemma gradChartLocalWithin_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocalWithin (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞
      (gradChartCoeffWithin (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    fun i => gradChartCoeffWithin_contMDiffOn (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeffWithin (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, gradChartCoeffWithin (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum

/-- The interior of the manifold is open. Direct application of
`ModelWithCorners.isOpen_interior`. -/
private lemma isOpen_interior_M' : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

/-- For a manifold-interior point of the chart source, the chart image lies in
the interior of the chart target. Wrapper of
`extChartAt_mem_interior_target_of_isInteriorPoint`. -/
private lemma extChartAt_mem_interior_target_of_interior
    (α : M) {x : M} (hx_src : x ∈ (chartAt H α).source)
    (hx_int : x ∈ I.interior M) :
    extChartAt I α x ∈ interior (extChartAt I α).target :=
  extChartAt_mem_interior_target_of_isInteriorPoint
    (I := I) α hx_src hx_int

/-- On the open neighborhood `(chartAt H x₀).source ∩ I.interior M`, the
intrinsic gradient `gradFun g f` agrees pointwise with the chart-local
within-formula `gradChartLocalWithin g x₀ f`. This is the local agreement that
underlies the smoothness on the interior. -/
private lemma gradFun_eq_gradChartLocalWithin_on_chart_inter_interior
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∀ y ∈ (chartAt H x₀).source ∩ I.interior M,
      gradFun (I := I) g f y =
        gradChartLocalWithin (I := I) g x₀ f y := by
  intro y hy
  exact (gradChartLocalWithin_eq_gradFun (I := I) g x₀ hf hy.1).symm

/-- The chart-local within-representation, viewed as a tangent-bundle section,
is `C^∞` on `(chartAt H x₀).source ∩ I.interior M`. -/
private lemma gradChartLocalWithin_contMDiffOn_chart_inter_interior
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y
        (gradChartLocalWithin (I := I) g x₀ f y))
      ((chartAt H x₀).source ∩ I.interior M) := by
  refine (gradChartLocalWithin_contMDiffOn_total
    (I := I) g x₀ hf).mono ?_
  intro y hy
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy.1
  · exact extChartAt_mem_interior_target_of_interior (I := I) x₀ hy.1 hy.2

/-- The intrinsic gradient `gradFun g f` is `C^∞` as a tangent-bundle section
on the open neighborhood `(chartAt H x₀).source ∩ I.interior M`. Combines the
local agreement with `gradChartLocalWithin` and the smoothness of the latter.
-/
private lemma gradFun_contMDiffOn_chart_inter_interior
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradFun (I := I) g f y))
      ((chartAt H x₀).source ∩ I.interior M) := by
  have hsmooth :=
    gradChartLocalWithin_contMDiffOn_chart_inter_interior
      (I := I) g x₀ hf
  have hcongr := gradFun_eq_gradChartLocalWithin_on_chart_inter_interior
    (I := I) g x₀ hf
  refine hsmooth.congr ?_
  intro y hy
  have h := hcongr y hy
  change TotalSpace.mk' E y (gradFun (I := I) g f y) =
    TotalSpace.mk' E y (gradChartLocalWithin (I := I) g x₀ f y)
  rw [h]

/-- **Smoothness of the gradient on the manifold interior.** The intrinsic
gradient `gradFun g f`, viewed as a tangent-bundle section, is `C^∞` on
`I.interior M`. The proof is local-to-global via the chart-local
within-representation. -/
theorem gradFun_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (I.interior M) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x hx_int
  refine ⟨(chartAt H x).source, ?_, ?_, ?_⟩
  · exact (chartAt H x).open_source
  · exact mem_chart_source H x
  · have hsm := gradFun_contMDiffOn_chart_inter_interior
      (I := I) g x hf
    have hset_eq : I.interior M ∩ (chartAt H x).source =
        (chartAt H x).source ∩ I.interior M := by
      rw [Set.inter_comm]
    rw [hset_eq]
    exact hsm

/-- The metric gradient of a smooth function as a fiber-valued function on the
manifold. Smooth on `I.interior M` (see `gradFun_contMDiffOn_interior`). On
boundary points the value is well-defined intrinsically (from `mfderiv` and the
fiberwise Riesz isomorphism), but smoothness is not asserted there. -/
abbrev grad_g_with_boundary
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    ∀ x : M, TangentSpace I x :=
  gradFun (I := I) g f

@[simp] lemma grad_g_with_boundary_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    grad_g_with_boundary (I := I) g f x = gradFun (I := I) g f x := rfl

/-- Re-statement of `gradFun_contMDiffOn_interior` for the named alias
`grad_g_with_boundary`. -/
theorem grad_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (grad_g_with_boundary (I := I) g f x))
      (I.interior M) :=
  gradFun_contMDiffOn_interior (I := I) g hf

set_option linter.unusedVariables false in
/-- **Duality of gradient and tangent action (with boundary).** The action of a
smooth tangent section `X` on a smooth scalar `f` equals the metric inner
product of `X` with the gradient `gradFun g f`. The identity is intrinsic and
holds at every point of the manifold (interior or boundary).

The smoothness hypothesis on `f` is recorded for API consistency with the
downstream integration-by-parts theorems; the identity itself follows from the
intrinsic Riesz representation `inner_gradFun_right` and does not in fact
require smoothness. -/
theorem tangentSectionAction_grad_g_with_boundary_eq_inner
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x) (grad_g_with_boundary (I := I) g f x) := by
  rw [grad_g_with_boundary_apply]
  rw [inner_gradFun_right (I := I) g f x (X x)]
  rfl

set_option linter.unusedVariables false in
/-- Symmetric form: the action equals the inner product with the gradient on
either side. -/
theorem tangentSectionAction_grad_g_with_boundary_eq_inner_left
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (grad_g_with_boundary (I := I) g f x) (X x) := by
  rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf X x]
  exact g.symm x (X x) (grad_g_with_boundary (I := I) g f x)

set_option linter.unusedVariables false in
/-- The metric inner product on two gradients is symmetric. Direct from the
symmetry of the metric tensor `g.symm`. The smoothness hypotheses on `f` and
`h` are recorded for API consistency. -/
theorem inner_grad_g_with_boundary_symm
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    g.inner x (grad_g_with_boundary (I := I) g f x)
        (grad_g_with_boundary (I := I) g h x) =
      g.inner x (grad_g_with_boundary (I := I) g h x)
        (grad_g_with_boundary (I := I) g f x) :=
  g.symm x _ _

/-- The support of `grad_g_with_boundary g f` is contained in the topological
support of `f`. Re-stated from the boundary-agnostic
`support_gradFun_subset`. -/
lemma support_grad_g_with_boundary_subset
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Function.support (fun x : M => grad_g_with_boundary (I := I) g f x) ⊆
      tsupport f :=
  support_gradFun_subset (I := I) g f

/-- If `f` is locally zero near `x`, then `grad_g_with_boundary g f` vanishes
at `x`. Re-stated from `gradFun_eq_zero_of_eventuallyEq_zero`. -/
lemma grad_g_with_boundary_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ))) :
    grad_g_with_boundary (I := I) g f x = (0 : TangentSpace I x) :=
  gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hf

/-- If `f` has compact support, then so does `grad_g_with_boundary g f` (as a
fiber-valued function). The compact-support transfer needs no smoothness
hypothesis on `f`: the support inclusion alone is enough. -/
lemma hasCompactSupport_grad_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf_cs : HasCompactSupport f) :
    IsCompact
      (tsupport (fun x : M => grad_g_with_boundary (I := I) g f x)) := by
  refine IsCompact.of_isClosed_subset (hf_cs : IsCompact (tsupport f))
    (isClosed_tsupport _) ?_
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  exact support_grad_g_with_boundary_subset (I := I) g f hx

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
