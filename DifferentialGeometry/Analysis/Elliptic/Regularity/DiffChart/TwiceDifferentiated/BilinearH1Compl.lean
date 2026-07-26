import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

/-!
# Twice-differentiated chart-bilinear identity

This module packages the **twice-differentiated** chart-bilinear variational
identity on `chartTargetEuclid α` obtained by formally differentiating the
variational identity of a `DiffChartBilinearH1ComplData g α` along a second
coordinate direction `l₂ : Fin n`.

Mathematically, starting from the once-differentiated identity carried by
the base data `D₁ : DiffChartBilinearH1ComplData g α` with direction
`l₁ := D₁.direction`:
```
∫ ∑_{i,j} weightedInvGramOnEuclid · weak_partial_deriv i · ∂_j ψ
  + ∫ densityOnEuclid · u_chart_deriv · ψ
  = ∫ densityOnEuclid · f_chart_deriv · ψ
    - ∫ ∑_{i,j} weightedInvGramDerivOnEuclid · base.weak_partial i · ∂_j ψ
    - ∫ densityDerivOnEuclid · base.u_chart · ψ
    + ∫ densityDerivOnEuclid · base.f_chart · ψ,
```
applying `∂_{l₂}` (Leibniz) once more leaves us with the *twice-differentiated*
identity for the weak `l₂`-partial of each integrand factor, with new Leibniz
cross terms involving `∂_{l₂}` of the smooth coefficient fields
`weightedInvGramOnEuclid`, `weightedInvGramDerivOnEuclid (·, ·, l₁)`,
`densityOnEuclid`, and `densityDerivOnEuclid (·, l₁)`. Mixed second
coordinate derivatives of the smooth metric coefficients enter through the
two cross-term layers and are encoded by `weightedInvGramSecondDerivOnEuclid`
and `densitySecondDerivOnEuclid`.

The chart-side smooth coefficients are `C^∞` on `chartTargetEuclid α`, so
their second `(l₁, l₂)`-partial derivatives are also smooth on the same open
set.

The twice-differentiated identity is the input to a per-chart elliptic
regularity step at one order higher than the once-differentiated step.
Applying the chart-local Nirenberg difference-quotient machinery to the
twice-differentiated identity yields fourth weak partials of the chart-pull
of `u_h.coeFn`, completing the `H²` → `H⁴` regularity bootstrap.

## Main definitions

* `DiffTwiceChartBilinearH1ComplData`: packaged data for the
  twice-differentiated chart-bilinear identity, recording the base
  once-differentiated data `base1`, the second-direction `direction2`, the
  weak `direction2`-partials `u_chart_deriv2`, `f_chart_deriv2`,
  `weak_partial_deriv2 i` of the base scalar fields and weak partials, the
  twice-differentiated weak partials `u_chart_second_deriv` and
  `weak_partial_second_deriv`, the smooth twice-Leibniz cross-coefficients,
  and the twice-differentiated variational identity.
* `weightedInvGramSecondDerivOnEuclid`: the mixed `(l₁, l₂)`-partial Frechet
  derivative of `weightedInvGramOnEuclid g α i j`. Smooth on
  `chartTargetEuclid α`.
* `densitySecondDerivOnEuclid`: the mixed `(l₁, l₂)`-partial Frechet
  derivative of `densityOnEuclid g α`. Smooth on `chartTargetEuclid α`.

## Main results

* `twice_differentiated_chart_bilinear_identity`: hypothesis-bearing form of
  the twice-differentiated chart-bilinear identity, expressed via the data
  structure.
* `weightedInvGramSecondDerivOnEuclid_contDiffOn`,
  `densitySecondDerivOnEuclid_contDiffOn`: smoothness of the twice-Leibniz
  cross-coefficient fields on `chartTargetEuclid α`.
* `weightedInvGramSecondDerivOnEuclid_continuousOn`,
  `densitySecondDerivOnEuclid_continuousOn`: continuity wrappers.
* `weightedInvGramSecondDerivOnEuclid_bounded_on_compact`,
  `densitySecondDerivOnEuclid_bounded_on_compact`: uniform bounds on
  compact subsets of `chartTargetEuclid α`.
* `diffTwiceChartBilinearH1ComplData_of_laplacianDomainPow_two` —
  hypothesis-bearing constructor from `u_h ∈ laplacianDomainPow g 2`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffTwiceChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The mixed `(l₁, l₂)`-partial Frechet derivative of
`weightedInvGramOnEuclid g α i j`, evaluated against the `l₂`-th unit
vector of the second derivative. Smooth on `chartTargetEuclid α`. -/
def weightedInvGramSecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ
      (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
    (EuclideanSpace.single l₂ 1)

/-- The mixed `(l₁, l₂)`-partial Frechet derivative of `densityOnEuclid g α`,
evaluated against the `l₂`-th unit vector of the second derivative. Smooth
on `chartTargetEuclid α`. -/
def densitySecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
    (EuclideanSpace.single l₂ 1)

/-- The mixed `(l₁, l₂)`-partial Frechet derivative of
`weightedInvGramOnEuclid g α i j` is smooth on `chartTargetEuclid α`. -/
lemma weightedInvGramSecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- The mixed `(l₁, l₂)`-partial Frechet derivative of `densityOnEuclid g α`
is smooth on `chartTargetEuclid α`. -/
lemma densitySecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (densityDerivOnEuclid (I := I) g α l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) g α l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (densityDerivOnEuclid (I := I) g α l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- Continuity wrapper for `weightedInvGramSecondDerivOnEuclid`. -/
lemma weightedInvGramSecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂).continuousOn

/-- Continuity wrapper for `densitySecondDerivOnEuclid`. -/
lemma densitySecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densitySecondDerivOnEuclid_contDiffOn (I := I) g α l₁ l₂).continuousOn

/-- The twice-Leibniz cross-coefficient `weightedInvGramSecondDerivOnEuclid`
is bounded on every compact subset of `chartTargetEuclid α`. -/
lemma weightedInvGramSecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) K :=
    (weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

/-- The twice-Leibniz cross-coefficient `densitySecondDerivOnEuclid` is
bounded on every compact subset of `chartTargetEuclid α`. -/
lemma densitySecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) K :=
    (densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

/-- Packaged data describing the *twice-differentiated* chart-bilinear
identity on `chartTargetEuclid α` obtained by formally differentiating a
once-differentiated `DiffChartBilinearH1ComplData` in a second direction
`direction2 : Fin n`.

The structure records:

(1) the base once-differentiated data
    `base1 : DiffChartBilinearH1ComplData g α`, with its first
    direction `l₁ := base1.direction`;
(2) the second differentiation direction
    `direction2 : Fin (Module.finrank ℝ E)`;
(3) the weak `direction2`-partials of every chart-side field appearing in
    the once-differentiated identity:
    - `u_chart_deriv2`, `f_chart_deriv2` (weak `l₂`-partials of
      `base1.u_chart_deriv`, `base1.f_chart_deriv`),
    - `u_chart_second_deriv` (weak `l₂`-partial of `base1.u_chart_deriv`
      viewed as a partial of `base1.base.u_chart`),
    - `weak_partial_deriv2 i` (weak `l₂`-partial of `base1.weak_partial_deriv
      i`, i.e. the mixed second partial of `base1.base.u_chart` in
      directions `(i, l₂)` paired with the once-differentiated direction
      `l₁`),
    - `weak_partial_second_deriv i` (weak `l₂`-partial of
      `base1.weak_partial_deriv i`, the canonical second partial used in
      the twice-differentiated principal block);
(4) DeGiorgi-style witnesses that each `_deriv2` / `_second_deriv` field is
    a weak `direction2`-partial of the corresponding base scalar field on
    `chartTargetEuclid α`;
(5) local `L²` regularity of each new field on every compact subset of
    `chartTargetEuclid α`;
(6) the twice-differentiated variational identity, expressing the
    integrated Leibniz expansion as a balance of principal `L²` terms
    (involving `weak_partial_second_deriv` and `u_chart_second_deriv`) and
    lower-order Leibniz cross-terms (involving
    `weightedInvGramDerivOnEuclid`, `densityDerivOnEuclid`,
    `weightedInvGramSecondDerivOnEuclid`, `densitySecondDerivOnEuclid` and
    the once-differentiated / base scalar fields).

The principal integrand uses the EXPLICIT canonical weak second partial
`weak_partial_second_deriv i`, not the classical Fréchet derivative
`fderiv ℝ (base1.weak_partial_deriv i)` (which would vanish a.e. in
non-smooth contexts). The Leibniz cross-terms involve the smooth coefficient
derivatives, contributing lower-order corrections to the variational
identity.

The schematic form of the twice-differentiated identity is
```
∫ ∑_{i,j} weightedInvGramOnEuclid · weak_partial_second_deriv i · ∂_j ψ
  + ∫ densityOnEuclid · u_chart_second_deriv · ψ
  = RHS,
```
where RHS expands the Leibniz cross-products of `∂_{l₂}` acting on
each factor of the once-differentiated RHS, plus the original
`f_chart_deriv2` term. The RHS is recorded explicitly in
`twice_differentiated_variational_identity`. -/
structure DiffTwiceChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where

  base1 : DiffChartBilinearH1ComplData (I := I) (M := M) g α

  direction2 : Fin (Module.finrank ℝ E)

  u_chart_deriv2 : EuclN → ℝ

  f_chart_deriv2 : EuclN → ℝ

  u_chart_second_deriv : EuclN → ℝ

  weak_partial_deriv2 : Fin (Module.finrank ℝ E) → EuclN → ℝ

  weak_partial_second_deriv : Fin (Module.finrank ℝ E) → EuclN → ℝ

  u_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      u_chart_deriv2 base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  f_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      f_chart_deriv2 base1.f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_second_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      u_chart_second_deriv base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_deriv2_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weak_partial_deriv2 i) (base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_second_deriv_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weak_partial_second_deriv i) (base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_deriv2 2 ((volume : Measure EuclN).restrict K)

  f_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f_chart_deriv2 2 ((volume : Measure EuclN).restrict K)

  u_chart_second_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_second_deriv 2 ((volume : Measure EuclN).restrict K)

  weak_partial_deriv2_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_deriv2 i) 2
        ((volume : Measure EuclN).restrict K)

  weak_partial_second_deriv_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_second_deriv i) 2
        ((volume : Measure EuclN).restrict K)

  twice_differentiated_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weak_partial_second_deriv i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * u_chart_second_deriv y * ψ y
        ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j direction2 y *
              weak_partial_deriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          u_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j base1.direction y *
              weak_partial_deriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                base1.direction direction2 y *
              base1.base.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.u_chart y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          base1.base.weak_partial direction2 y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.f_chart y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN))

/-- The base once-differentiated data of a `DiffTwiceChartBilinearH1ComplData`. -/
abbrev base1Data
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α := D.base1

/-- The unbase base-base data of a `DiffTwiceChartBilinearH1ComplData`. -/
abbrev baseData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    ChartBilinearH1ComplData (I := I) (M := M) g α := D.base1.base

/-- The first differentiation direction (inherited from `base1`). -/
abbrev direction1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    Fin (Module.finrank ℝ E) := D.base1.direction

/-- Headline form of the twice-differentiated chart-bilinear identity for
a twice-differentiated `H1Compl` element: given the data `D`, the
twice-differentiated variational identity holds for every smooth test
function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`. This is a re-export
of `D.twice_differentiated_variational_identity` for ergonomics. -/
theorem twice_differentiated_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial_second_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart_second_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.direction2 y *
            D.weak_partial_deriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.u_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.weak_partial_deriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j
              D.base1.direction D.direction2 y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.weak_partial D.direction2 y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.twice_differentiated_variational_identity ψ hψ hψ_cs hψ_supp

/-- A `DiffTwiceChartBilinearH1ComplData` carries the *once-differentiated*
identity intact via its `.base1` field. -/
theorem differentiated_chart_bilinear_identity_via_base1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.weak_partial_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.u_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.f_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.base1.differentiated_variational_identity ψ hψ hψ_cs hψ_supp

/-- A `DiffTwiceChartBilinearH1ComplData` carries the *base* identity
intact via the `.base1.base` field. -/
theorem base_chart_bilinear_identity_via_base1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.base1.base.variational_identity ψ hψ hψ_cs hψ_supp

/-- `u_chart_second_deriv` is a weak `direction2`-partial of
`base1.u_chart_deriv`, which is in turn a weak `direction1`-partial of
`base1.base.u_chart`. Thus, formally, `u_chart_second_deriv` is a "mixed"
weak `(direction1, direction2)`-partial of `base1.base.u_chart`. This wrapper
lemma exposes both ingredients side by side. -/
theorem u_chart_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      D.u_chart_second_deriv D.base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      D.base1.u_chart_deriv D.base1.base.u_chart
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.u_chart_second_deriv_isWeakPartial,
   D.base1.u_chart_deriv_isWeakPartial⟩

/-- For each `i`, `weak_partial_second_deriv i` is a weak `direction2`-partial
of `base1.weak_partial_deriv i`, which is in turn a weak `direction1`-partial
of `base1.base.weak_partial i`. -/
theorem weak_partial_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      (D.weak_partial_second_deriv i) (D.base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      (D.base1.weak_partial_deriv i) (D.base1.base.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.weak_partial_second_deriv_isWeakPartial i,
   D.base1.weak_partial_deriv_isWeakPartial i⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Canonical chosen weak `l₂`-partial of `D₁.u_chart_deriv` on
`chartTargetEuclid α`. -/
noncomputable def chosenSecondPartialUChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ D₁.u_chart_deriv
    (chartTargetEuclid (I := I) (M := M) α)

/-- Canonical chosen weak `l₂`-partial of `D₁.f_chart_deriv` on
`chartTargetEuclid α`. -/
noncomputable def chosenSecondPartialFChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ D₁.f_chart_deriv
    (chartTargetEuclid (I := I) (M := M) α)

/-- Canonical chosen weak `l₂`-partial of `D₁.weak_partial_deriv i` on
`chartTargetEuclid α`. -/
noncomputable def chosenSecondPartialWeakPartialDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (i l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ (D₁.weak_partial_deriv i)
    (chartTargetEuclid (I := I) (M := M) α)

/-- The canonical chosen second partial of `D₁.u_chart_deriv` is a weak
`l₂`-partial of `D₁.u_chart_deriv` on the chart target. -/
private lemma chosenSecondPartialUChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

/-- The canonical chosen second partial of `D₁.f_chart_deriv` is a weak
`l₂`-partial of `D₁.f_chart_deriv` on the chart target. -/
private lemma chosenSecondPartialFChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

/-- The canonical chosen second partial of `D₁.weak_partial_deriv i` is a weak
`l₂`-partial of `D₁.weak_partial_deriv i` on the chart target. -/
private lemma chosenSecondPartialWeakPartialDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂)
      (D₁.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

/-- The canonical chosen second partial of `D₁.u_chart_deriv` is globally
`MemLp 2` on the chart target. -/
private lemma chosenSecondPartialUChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

/-- The canonical chosen second partial of `D₁.f_chart_deriv` is globally
`MemLp 2` on the chart target. -/
private lemma chosenSecondPartialFChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

/-- The canonical chosen second partial of `D₁.weak_partial_deriv i` is
globally `MemLp 2` on the chart target. -/
private lemma chosenSecondPartialWeakPartialDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

/-- Local-`L²` regularity helper: a function in `MemLp 2 (volume.restrict
chartTarget)` is in `MemLp 2 (volume.restrict K)` for every compact
`K ⊆ chartTarget`. -/
private lemma memLp_restrict_of_memLp_chartTarget
    (α : M)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f 2 ((volume : Measure EuclN).restrict K) := by
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact hf.restrict K

/-- **Constructor for `DiffTwiceChartBilinearH1ComplData g α`.**

Given a once-differentiated base data `D₁ : DiffChartBilinearH1ComplData g α`
with first direction `D₁.direction =: l₁`, a second direction `l₂`, and
`MemW1p 2` witnesses for each of the once-differentiated chart-side scalar
fields on `chartTargetEuclid α`, plus the twice-differentiated variational
identity as a hypothesis, package the twice-differentiated data.

The canonical second partials are obtained via `chosenWeakPartial'`. Their
weak-partial witnesses and local `L²` regularity follow unconditionally from
the supplied `MemW1p 2` hypotheses; the variational identity is the only
truly analytic residual hypothesis. -/
noncomputable def diffTwiceChartBilinearH1ComplData_of_diff
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i, DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j D₁.direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  D₁.direction l₂ y *
                D₁.base.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.u_chart y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            D₁.base.weak_partial l₂ y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.f_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α where
  base1 := D₁
  direction2 := l₂
  u_chart_deriv2 := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  f_chart_deriv2 := chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂
  u_chart_second_deriv := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  weak_partial_deriv2 := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  weak_partial_second_deriv := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  u_chart_deriv2_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  f_chart_deriv2_isWeakPartial :=
    chosenSecondPartialFChartDeriv_isWeakPartial
      (I := I) (M := M) h_fDeriv_memW1p l₂
  u_chart_second_deriv_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  weak_partial_deriv2_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  weak_partial_second_deriv_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  u_chart_deriv2_locally_memLp := fun K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  f_chart_deriv2_locally_memLp := fun K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialFChartDeriv_memLp
        (I := I) (M := M) h_fDeriv_memW1p l₂) hK hKin
  u_chart_second_deriv_locally_memLp := fun K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  weak_partial_deriv2_locally_memLp := fun i K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  weak_partial_second_deriv_locally_memLp := fun i K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  twice_differentiated_variational_identity := h_identity

/-- **Hypothesis-bearing constructor from `u_h ∈ laplacianDomainPow g 2`.**

Takes `u_h ∈ laplacianDomainPow g 2`, a first direction `l₁` for the
once-differentiated data, a second direction `l₂` for the twice-differentiated
data, the residual hypotheses for the once-differentiated constructor
(`MemW1p 2 base.f_chart`, plus the once-differentiated variational identity),
and the residual hypotheses for the twice-differentiated constructor
(`MemW1p 2 D₁.u_chart_deriv`, `MemW1p 2 D₁.f_chart_deriv`,
`MemW1p 2 D₁.weak_partial_deriv i`, plus the twice-differentiated variational
identity).

Returns the twice-differentiated chart-bilinear data. -/
noncomputable def diffTwiceChartBilinearH1ComplData_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        ((diffChartBilinearH1ComplData_of_laplacianDomainPow_two
          (I := I) (M := M) g α hu_h l₁
          h_base_f_chart_memW1p h_once_identity).weak_partial_deriv i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction l₂ y *
                (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                  (I := I) (M := M) g α hu_h l₁
                  h_base_f_chart_memW1p h_once_identity).base.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.u_chart y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.weak_partial l₂ y *
            ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.f_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffTwiceChartBilinearH1ComplData_of_diff (I := I) (M := M)
    (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h l₁
      h_base_f_chart_memW1p h_once_identity)
    l₂
    h_uDeriv_memW1p h_fDeriv_memW1p h_wpDeriv_memW1p
    h_twice_identity

end DiffTwiceChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
