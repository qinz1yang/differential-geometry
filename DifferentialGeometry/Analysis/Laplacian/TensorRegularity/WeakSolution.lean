import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartWeakIdentity

/-!
# Per-component scalar weak solutions of the tensor connection Laplacian

For a smooth Riemannian metric `g` on a closed manifold `(M, g)`, a chart center
`α : M`, tensor ranks `(r, s)`, and a component multi-index `P₀`, this file
performs the final assembly step of the chart-local elliptic-regularity analysis
of the connection Laplacian on `(r, s)`-tensor sections: it routes the chart
scalar component of an `(r, s)`-tensor section into the Euclidean
divergence-form weak-solution predicate
`SmoothEllipticBilinearForm.IsSmoothWeakSolution`.

## The chart scalar component as a Euclidean function

The chart-coordinate covariant derivative — and hence the `H^1` Dirichlet form
of the connection Laplacian — is computed from the *raw* chart-frame scalar
components `tensorChartComponentRaw g r s T α Idx Jdx` (no partition-of-unity
weight). The Euclidean object on which the chart-local divergence-form analysis
runs is therefore the Euclidean push-forward of this raw chart component,
`tensorComponentEuclid g r s T α P₀` — the `(r, s)`-tensor analogue of the
scalar chart pull-back `chartPullback`. When the section `T` is supported inside
the chart source, this push-forward is globally `C^∞` (extension by zero across
the closed-off complement of the chart target).

## The principal-part bilinear form

The component-diagonal principal part of the connection Laplacian's chart
Dirichlet form is the scalar Laplace–Beltrami principal part, packaged as the
`SmoothEllipticBilinearForm` `tensorPrincipalForm g α hK hK_target` for a chosen
compact `K ⊆ chartTargetEuclid α`. Its zeroth-order coefficient vanishes, and on
`K` its principal coefficient matrix is the volume-weighted inverse Gram matrix.

## Main definitions

* `tensorComponentEuclid g r s T α P₀` — the Euclidean push-forward of the raw
  chart-frame scalar component of `T` at the component multi-index `P₀`.

## Main results

* `tensorComponentEuclid_contDiffOn` — the push-forward is `ContDiffOn ℝ ∞` on
  the Euclidean chart target.
* `tensorComponentEuclid_contDiff` — for a section `T` supported inside the
  chart source, the push-forward is globally `C^∞`.
* `tensorComponentEuclid_tsupport_subset` — for a chart-supported section the
  push-forward has compact support inside a compact subset of the Euclidean
  chart target.
* `tensorComponent_isSmoothWeakSolution_of_chartIdentity` — the headline
  (hypothesis-bearing form): given the chart-pulled scalar bilinear identity
  for the principal-part form `tensorPrincipalForm`, the Euclidean chart
  component `tensorComponentEuclid g r s T α P₀` is a smooth weak solution of
  `tensorPrincipalForm` with the supplied right-hand side.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **The Euclidean chart component of an `(r, s)`-tensor section.** For a chart
center `α` and a component multi-index `P₀ : CompIdx E r s`, this is the
Euclidean push-forward `chartPushedRaw I α` of the raw chart-frame scalar
component `tensorChartComponentRaw g r s T α P₀.1 P₀.2`: a function
`EuclN → ℝ`, equal on the chart target to the raw chart component read at the
chart-source preimage, and `0` off the chart target.

It is the tensor analogue of the scalar chart pull-back `chartPullback`: it is
the function on which the chart-local divergence-form elliptic analysis of the
connection Laplacian's component-diagonal principal part operates. -/
noncomputable def tensorComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)

/-- Unfolding lemma for `tensorComponentEuclid`. -/
lemma tensorComponentEuclid_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ =
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) := rfl

/-- On the Euclidean chart target the Euclidean chart component
`tensorComponentEuclid g r s T α P₀` equals the raw chart-frame scalar component
read at the chart-source preimage of the point. -/
lemma tensorComponentEuclid_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y =
      tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

/-- Off the Euclidean chart target the Euclidean chart component vanishes. -/
lemma tensorComponentEuclid_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y = 0 := by
  rw [tensorComponentEuclid_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

/-- The Euclidean chart component `tensorComponentEuclid g r s T α P₀` is
`ContDiffOn ℝ ∞` on the Euclidean chart target — a restatement of
`chartPushedRaw_tensorChartComponentRaw_contDiffOn`. -/
theorem tensorComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α P₀.1 P₀.2

/-- The raw chart-frame scalar component of a section vanishes wherever the
underlying section vanishes: it is the chart-frame component projection of the
trivialization projection of `T.toSection`, both continuous-linear, so a zero
input produces a zero output. -/
private lemma tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {x : M} (hx : T.toSection x = 0) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x = 0 := by
  classical
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [hx, map_zero, map_zero]

/-- The topological support of the raw chart-frame scalar component is contained
in the topological support of `T.toFun`: the component vanishes wherever
`T.toSection` (equivalently `T.toFun`) vanishes. -/
lemma tensorChartComponentRaw_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport T.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  have hzero : T.toFun x = 0 := image_eq_zero_of_notMem_tsupport hx_notsupp
  have hsec : T.toSection x = 0 := by
    have hmod : TensorRSSpace.toModel (T.toSection x) = 0 := hzero
    have := (tensorRSSpace_continuousLinearEquiv (I := I) r s x).injective
      (a₁ := T.toSection x) (a₂ := 0)
    apply this
    rw [show (tensorRSSpace_continuousLinearEquiv (I := I) r s x) (T.toSection x) =
        TensorRSSpace.toModel (T.toSection x) from rfl, hmod, map_zero]
  exact hx (tensorChartComponentRaw_eq_zero_of_section_eq_zero
    (I := I) (M := M) g r s T α Idx Jdx hsec)

/-- For a section `T` supported inside the chart source, the raw chart-frame
scalar component is supported inside the chart source. -/
private lemma tensorChartComponentRaw_tsupport_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) ⊆
      (chartAt H α).source :=
  (tensorChartComponentRaw_tsupport_subset (I := I) (M := M) g r s T α Idx Jdx).trans
    hT_supp

/-- For a section `T` supported inside the chart source, the Euclidean chart
component `tensorComponentEuclid g r s T α P₀` is globally `C^∞`.

The raw chart component is `C^∞` on the chart source and supported there
(`tensorChartComponentRaw_tsupport_subset_chart_source`); the Euclidean
push-forward `chartPushedRaw I α` of such a function is `ContDiffOn ℝ ∞` on the
open chart target and vanishes off a compact subset of it, so it is globally
`C^∞` by the extension-by-zero argument. -/
theorem tensorComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact ((tensorComponentEuclid_contDiffOn (I := I) (M := M)
      g r s T α P₀).contDiffWithinAt hy).contDiffAt (hopen.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hK_target h)
    have hKc_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    refine (contDiff_const (c := (0 : ℝ))).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hKc_open.mem_nhds hyK] with z hz
    by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
    · exact chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hzT hz
    · exact tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hzT

/-- For a section `T` supported inside the chart source, the Euclidean chart
component `tensorComponentEuclid g r s T α P₀` has compact support inside the
compact Euclidean image of the raw chart component's support, which lies inside
the open Euclidean chart target. -/
theorem tensorComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact (closure_minimal hsupp hK_compact.isClosed).trans hK_target

/-- For a section `T` supported inside the chart source, the Euclidean chart
component `tensorComponentEuclid g r s T α P₀` has compact support: its
`Function.support` is contained in the compact Euclidean image of the raw chart
component's support. -/
theorem tensorComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hraw_supp : tsupport
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) ⊆
      (chartAt H α).source :=
    tensorChartComponentRaw_tsupport_subset_chart_source
      (I := I) (M := M) g r s T α P₀.1 P₀.2 hT_supp
  set K : Set EuclN :=
    toEuclidean '' ((extChartAt I α) ''
      (tsupport (tensorChartComponentRaw (I := I) (M := M)
        g r s T α P₀.1 P₀.2))) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_extChartAt_tsupport_compact
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M)
      (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
      (α := α) hraw_supp
  have hsupp : Function.support
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyK
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
        (I := I) (M := M)
        (u := tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2)
        α hyT hyK)
    · exact hy (tensorComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s T α P₀ hyT)
  exact HasCompactSupport.of_support_subset_isCompact hK_compact hsupp

/-- **Per-component scalar weak solution of the connection Laplacian
(hypothesis-bearing form).**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless)
smooth manifold `M`, let `α : M` be a chart center, and let `T` be a smooth
compactly-supported `(r, s)`-tensor section supported inside the chart source.
Let `K ⊆ chartTargetEuclid α` be compact, and `P₀ : CompIdx E r s` a component
multi-index.

If, for every smooth compactly-supported Euclidean test function `φ`, the
chart-pulled scalar bilinear identity
```
(tensorPrincipalForm g α hK hK_target).bilin (tensorComponentEuclid g r s T α P₀) φ
  = ∫ y, f y * φ y
```
holds, then the Euclidean chart component `tensorComponentEuclid g r s T α P₀`
is a smooth weak solution of the principal-part elliptic bilinear form
`tensorPrincipalForm g α hK hK_target` with right-hand side `f`.

The role of the hypothesis: in applications the manifold-side global `H^1` weak
equation `∫_M ⟨∇T, ∇v⟩ dμ_g = ∫_M ⟨F, v⟩ dμ_g` of the connection Laplacian is
chart-pulled and the inverse-Gram-rotated test section `rotatedTestSection`
substituted; the principal part collapses (`covPrincipalIntegrand_rotated_collapse`)
to the scalar elliptic principal integrand of `tensorPrincipalForm`
(`weightedInvGram_principalIntegrand_eq`), and the lower-order remainder and
the source pairing are collected into the right-hand side `f`. -/
theorem tensorComponent_isSmoothWeakSolution_of_chartIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (f : EuclN → ℝ)
    (hbilin :
      ∀ φ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set EuclN) →
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
          ∫ y in (Set.univ : Set EuclN), f y * φ y) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) f := by
  classical
  refine ⟨tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp, ?_⟩
  intro φ hφ hφ_cs hφ_supp
  exact hbilin φ hφ hφ_cs hφ_supp

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
