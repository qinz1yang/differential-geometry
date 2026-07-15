import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl

/-!
# Differentiated chart-bilinear identity

This module packages the **differentiated** chart-bilinear variational identity
on `chartTargetEuclid α` obtained by formally differentiating the variational
identity of a `ChartBilinearH1ComplData g α` along a coordinate direction
`l : Fin n`.

Mathematically, if the base data records the identity
```
∫ ∑_{i,j} (√det g · g^{ij}) · (weak_partial i) · ∂_j ψ
  + ∫ √det g · u_chart · ψ
  = ∫ √det g · f_chart · ψ
```
for every smooth test function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`,
then applying `∂_l` (Leibniz) leaves us with the *differentiated* identity for
the weak `l`-partial derivatives of `u_chart` and `f_chart`:
```
∫ ∑_{i,j} (√det g · g^{ij}) · ∂_l(weak_partial i) · ∂_j ψ
  + ∫ √det g · ∂_l(u_chart) · ψ
  = ∫ √det g · ∂_l(f_chart) · ψ
    - ∫ ∑_{i,j} ∂_l(√det g · g^{ij}) · (weak_partial i) · ∂_j ψ
    - ∫ ∂_l(√det g) · u_chart · ψ
    + ∫ ∂_l(√det g) · f_chart · ψ.
```

The chart-side coefficients `√det g · g^{ij}` (`weightedInvGramOnEuclid`) and
`√det g` (`densityOnEuclid`) are smooth on `chartTargetEuclid α`, so their
`l`-partial derivatives are smooth functions on the same open set.

This identity is the input to a per-chart elliptic regularity step at one
order higher than the base step: applying the Nirenberg difference-quotient
machinery to the weak `l`-partial derivatives of `u_chart` produces second
weak partials, and iterating in `l` over all coordinate directions yields the
full second-order regularity bootstrap.

## Main definitions

* `DiffChartBilinearH1ComplData`: packaged data for the differentiated
  chart-bilinear identity, recording the base data, the direction `l`, the
  weak `l`-partials of `u_chart`, `f_chart`, each `weak_partial i`, the
  smooth Leibniz cross-coefficients, and the differentiated variational
  identity.
* `weightedInvGramDerivOnEuclid`: the `l`-partial Frechet derivative of
  `weightedInvGramOnEuclid g α i j` evaluated against the `l`-th unit
  vector. Smooth on `chartTargetEuclid α`.
* `densityDerivOnEuclid`: the `l`-partial Frechet derivative of
  `densityOnEuclid g α`. Smooth on `chartTargetEuclid α`.

## Main results

* `differentiated_chart_bilinear_identity`: hypothesis-bearing form of the
  differentiated chart-bilinear identity, expressed via the data structure.
* `weightedInvGramDerivOnEuclid_contDiffOn`,
  `densityDerivOnEuclid_contDiffOn`: smoothness of the cross-coefficient
  fields on `chartTargetEuclid α`.
* `weightedInvGramDerivOnEuclid_continuousOn`,
  `densityDerivOnEuclid_continuousOn`: continuity wrappers.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The `l`-partial Frechet derivative of `weightedInvGramOnEuclid g α i j`,
evaluated against the `l`-th Euclidean unit vector. Smooth on
`chartTargetEuclid α`; junk values elsewhere. -/
def weightedInvGramDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
    (EuclideanSpace.single l 1)

/-- The `l`-partial Frechet derivative of `densityOnEuclid g α`, evaluated
against the `l`-th Euclidean unit vector. Smooth on `chartTargetEuclid α`;
junk values elsewhere. -/
def densityDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l 1)

/-- The `l`-partial Frechet derivative of `weightedInvGramOnEuclid g α i j` is
smooth on `chartTargetEuclid α`. -/
lemma weightedInvGramDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (weightedInvGramOnEuclid (I := I) g α i j)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (weightedInvGramOnEuclid (I := I) g α i j) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- The `l`-partial Frechet derivative of `densityOnEuclid g α` is smooth on
`chartTargetEuclid α`. -/
lemma densityDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densityDerivOnEuclid (I := I) g α l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
        (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ (densityOnEuclid (I := I) g α) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- Continuity wrapper for `weightedInvGramDerivOnEuclid`. -/
lemma weightedInvGramDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l).continuousOn

/-- Continuity wrapper for `densityDerivOnEuclid`. -/
lemma densityDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (densityDerivOnEuclid (I := I) g α l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn

/-- The Leibniz cross-coefficient `weightedInvGramDerivOnEuclid` is bounded on
every compact subset of `chartTargetEuclid α`. -/
lemma weightedInvGramDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramDerivOnEuclid (I := I) g α i j l y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramDerivOnEuclid (I := I) g α i j l) K :=
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramDerivOnEuclid (I := I) g α i j l y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramDerivOnEuclid (I := I) g α i j l y_max|, ?_⟩
  intro y hy
  exact h_max hy

/-- The Leibniz cross-coefficient `densityDerivOnEuclid` is bounded on every
compact subset of `chartTargetEuclid α`. -/
lemma densityDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |densityDerivOnEuclid (I := I) g α l y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn (densityDerivOnEuclid (I := I) g α l) K :=
    (densityDerivOnEuclid_continuousOn (I := I) g α l).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densityDerivOnEuclid (I := I) g α l y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densityDerivOnEuclid (I := I) g α l y_max|, ?_⟩
  intro y hy
  exact h_max hy

/-- Packaged data describing the *differentiated* chart-bilinear identity on
`chartTargetEuclid α` obtained by formally differentiating a base
`ChartBilinearH1ComplData` in direction `direction : Fin n`.

The structure records:

(1) the base data `base : ChartBilinearH1ComplData g α`;
(2) the differentiation direction `direction : Fin (Module.finrank ℝ E)`;
(3) the weak `direction`-partials `u_chart_deriv`, `f_chart_deriv`,
    `weak_partial_deriv i` of the base scalar fields and weak partials;
(4) DeGiorgi-style witnesses that each `_deriv` field is indeed a weak
    `direction`-partial of the corresponding base field, and local-`L²`
    regularity on every compact subset of `chartTargetEuclid α`;
(5) the differentiated variational identity, expressing the integrated
    Leibniz expansion as a balance of principal `L²` terms (involving
    `weak_partial_deriv` and `u_chart_deriv`) and lower-order Leibniz
    cross-terms (involving `weightedInvGramDerivOnEuclid`,
    `densityDerivOnEuclid`, and the base `weak_partial`, `u_chart`,
    `f_chart`).

The principal integrand uses the EXPLICIT weak partial
`weak_partial_deriv i`, not the classical Fréchet derivative
`fderiv ℝ (base.weak_partial i)` (which would vanish a.e. in non-smooth
contexts). The Leibniz cross-terms `weightedInvGramDerivOnEuclid` and
`densityDerivOnEuclid` are *smooth* on `chartTargetEuclid α`, so they
contribute lower-order (zero-th and first-order) corrections to the
variational identity.

The differentiated identity has the form
```
∫ ∑_{i,j} weightedInvGramOnEuclid · weak_partial_deriv i · ∂_j ψ
  + ∫ densityOnEuclid · u_chart_deriv · ψ
  = ∫ densityOnEuclid · f_chart_deriv · ψ
    - ∫ ∑_{i,j} weightedInvGramDerivOnEuclid · base.weak_partial i · ∂_j ψ
    - ∫ densityDerivOnEuclid · base.u_chart · ψ
    + ∫ densityDerivOnEuclid · base.f_chart · ψ
```
for every smooth test ψ with `tsupport ψ ⊆ chartTargetEuclid α`.
-/
structure DiffChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where

  base : ChartBilinearH1ComplData (I := I) (M := M) g α

  direction : Fin (Module.finrank ℝ E)

  u_chart_deriv : EuclN → ℝ

  f_chart_deriv : EuclN → ℝ

  weak_partial_deriv : Fin (Module.finrank ℝ E) → EuclN → ℝ

  u_chart_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      u_chart_deriv base.u_chart
      (chartTargetEuclid (I := I) (M := M) α)

  f_chart_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      f_chart_deriv base.f_chart
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_deriv_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      (weak_partial_deriv i) (base.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_deriv 2 ((volume : Measure EuclN).restrict K)

  f_chart_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f_chart_deriv 2 ((volume : Measure EuclN).restrict K)

  weak_partial_deriv_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_deriv i) 2
        ((volume : Measure EuclN).restrict K)

  differentiated_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weak_partial_deriv i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * u_chart_deriv y * ψ y
        ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f_chart_deriv y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
              base.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction y *
          base.u_chart y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction y *
          base.f_chart y * ψ y
        ∂(volume : Measure EuclN))

/-- Headline form of the differentiated chart-bilinear identity for a
differentiated `H1Compl` element: given the data `D`, the differentiated
variational identity holds for every smooth test function `ψ` with
`tsupport ψ ⊆ chartTargetEuclid α`. This is a re-export of
`D.differentiated_variational_identity` for ergonomics. -/
theorem differentiated_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.direction y *
            D.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction y *
        D.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction y *
        D.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.differentiated_variational_identity ψ hψ hψ_cs hψ_supp

/-- The base data of a `DiffChartBilinearH1ComplData`. -/
abbrev base
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α) :
    ChartBilinearH1ComplData (I := I) (M := M) g α := D.base

/-- The differentiation direction of a `DiffChartBilinearH1ComplData`. -/
abbrev direction
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α) :
    Fin (Module.finrank ℝ E) := D.direction

/-- A `DiffChartBilinearH1ComplData` carries the *base* variational identity
intact via its `.base` field. This is a convenience re-export for callers that
need both identities side by side. -/
theorem base_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.base.variational_identity ψ hψ hψ_cs hψ_supp

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry
