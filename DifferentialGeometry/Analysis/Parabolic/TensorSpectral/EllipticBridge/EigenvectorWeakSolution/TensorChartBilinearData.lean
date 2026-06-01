import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr

/-!
# Chart-bilinear divergence-form data for a non-smooth tensor chart component

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the chart-local
elliptic-regularity analysis of the connection Laplacian `Δ_∇` on
`(r, s)`-tensor sections proceeds component by component. After the principal
part of the connection-Laplacian chart Dirichlet form is decoupled per scalar
chart component — by testing against `𝓜⁻¹`-rotated test sections — each chart
component `u` satisfies a **scalar** divergence-form elliptic identity whose
principal symbol is `weightedInvGramOnEuclid g α` (`= √(det g) · gⁱʲ`): the
*same* principal symbol as the scalar Laplace–Beltrami operator. The
component-diagonal principal part of the tensor connection Laplacian is, on each
component, the principal part of the scalar Laplace–Beltrami operator
(`tensorPrincipalForm_eq_scalar_metric_form`).

This module packages, for one chart `P₀`-component of a possibly non-smooth
`(r, s)`-tensor field, exactly that per-component scalar divergence-form data.
The data structure `TensorChartBilinearH1ComplData` records:

* a chart-pulled scalar `u_chart : EuclN → ℝ` (the `P₀`-component, possibly
  non-smooth);
* explicit weak partial derivatives `weak_partial i` of `u_chart` (in the
  DeGiorgi sense, against plain Lebesgue volume on `chartTargetEuclid α`);
* a chart-pulled scalar right-hand side `f_chart : EuclN → ℝ`;
* membership of `u_chart`, `weak_partial i`, and `f_chart` in `L²` of the
  chart-pulled weighted measure `volume.withDensity (densityOnEuclid g α)`;
* the density-weighted variational identity

```
∫_{chartTarget} ∑_{i, j} weightedInvGramOnEuclid · (weak_partial i) · ∂_j ψ
  + ∫_{chartTarget} densityOnEuclid · u_chart · ψ
  = ∫_{chartTarget} densityOnEuclid · f_chart · ψ
```

for every smooth test function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`.

## Relationship to the scalar structure

Because the per-component identity uses the *scalar* principal symbol
`weightedInvGramOnEuclid g α`, the underlying divergence-form data is genuinely
scalar-shaped: a `TensorChartBilinearH1ComplData` *is* a scalar
`ChartBilinearH1ComplData g α` together with the semantic information `(r, s, P₀)`
recording which `(r, s)`-tensor component it describes.

The structure is therefore a **thin wrapper**: it carries a single field
`toChartData : ChartBilinearH1ComplData g α` and exposes the same projection /
ergonomics surface as the scalar structure. The semantic parameters `r`, `s`,
`P₀` fix which chart component this data describes; they carry no extra field,
because the divergence-form data does not depend on the tensor object beyond the
choice of right-hand side, which a downstream producer plugs into
`toChartData.f_chart`. This wrapper exposes a `toChartData` projection so the
scalar interior-regularity engine `h2_chart_loc_of_uniform_bound` (which consumes
a `ChartBilinearH1ComplData`) can be applied to it via a trivial adapter.

The data structure is **non-vacuous** for non-smooth `u_chart`: the principal
integrand uses the explicit weak partial derivative `weak_partial i`, not the
classical Fréchet derivative `fderiv ℝ u_chart` (which would vanish a.e. for
non-smooth `u_chart`).

## Main definitions

* `TensorChartBilinearH1ComplData g r s α P₀` — the chart-bilinear
  divergence-form data for one chart `P₀`-component of a non-smooth
  `(r, s)`-tensor field on a closed Riemannian manifold.

## Main results

* `tensor_chart_bilinear_identity_h1Compl` — hypothesis-bearing form of the
  non-smooth per-component chart-bilinear identity, expressed via the data
  structure (tensor analogue of `chart_bilinear_identity_h1Compl`).
* `TensorChartBilinearH1ComplData.memLp_volume_restrict_u_chart`,
  `…memLp_volume_restrict_f_chart` — weighted `L²` membership of the chart
  component / right-hand side converts to plain `L²` on compact subdomains.
* projection lemmas re-exposing the fields of `toChartData`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Chart-bilinear divergence-form data for one chart `P₀`-component of a
non-smooth `(r, s)`-tensor field.**

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, ranks `(r, s)`, a chart center `α : M`, and a component
multi-index `P₀ : TensorCompIdx r s`, this packages the per-component scalar
divergence-form data of the connection Laplacian.

It is a thin wrapper around the scalar structure `ChartBilinearH1ComplData g α`:
the single field `toChartData` carries the scalar chart component `u_chart`, its
explicit weak partial derivatives `weak_partial i`, the chart-pulled right-hand
side `f_chart`, the weighted / local `L²` integrability of all three, the
genuine weak-partial-derivative data `weak_partial_isWeakPartial`, and the
density-weighted variational identity

```
∫ ∑_{i, j} (√det g · gⁱʲ) · (weak_partial i) · ∂_j ψ
  + ∫ √det g · u_chart · ψ = ∫ √det g · f_chart · ψ
```

on `chartTargetEuclid α` (for every smooth `ψ` with
`tsupport ψ ⊆ chartTargetEuclid α`).

The semantic parameters `r`, `s`, `P₀` fix which chart component of which
tensor field this data describes; they carry no extra field, because — after
the connection-Laplacian principal part is decoupled per component — the
divergence-form data is genuinely scalar-shaped, with principal symbol
`weightedInvGramOnEuclid g α` (the scalar Laplace–Beltrami principal symbol).
The tensor-specificity enters only through which right-hand side `toChartData.f_chart`
a downstream producer plugs in.

The structure is **non-vacuous** for non-smooth `u_chart`: the principal
integrand of `toChartData.variational_identity` uses the EXPLICIT weak partial
`weak_partial i`, not the classical Fréchet derivative `fderiv ℝ u_chart`. -/
structure TensorChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (_P₀ : TensorCompIdx (E := E) r s) where
  /-- The underlying scalar chart-bilinear divergence-form data: the chart
  component `u_chart`, its explicit weak partials, the right-hand side
  `f_chart`, their `L²` integrability, and the density-weighted variational
  identity. The per-component identity has the scalar principal symbol
  `weightedInvGramOnEuclid g α`, so the per-component tensor data is exactly
  this scalar structure. -/
  toChartData : ChartBilinearH1ComplData (I := I) (M := M) g α

namespace TensorChartBilinearH1ComplData

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The chart-pulled scalar `P₀`-component of the non-smooth tensor field. -/
def u_chart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.u_chart

/-- The chart-pulled scalar right-hand side. -/
def f_chart {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.toChartData.f_chart

/-- The explicit weak partial derivatives of the chart component. -/
def weak_partial {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    Fin (Module.finrank ℝ E) → EuclN → ℝ :=
  D.toChartData.weak_partial

@[simp] lemma u_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.u_chart = D.toChartData.u_chart := rfl

@[simp] lemma f_chart_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.f_chart = D.toChartData.f_chart := rfl

@[simp] lemma weak_partial_eq {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    D.weak_partial = D.toChartData.weak_partial := rfl

/-- The chart component `u_chart` is `MemLp 2` with respect to the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/
lemma u_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    MemLp D.u_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.u_chart_memLp_weighted

/-- The right-hand side `f_chart` is `MemLp 2` with respect to the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/
lemma f_chart_memLp_weighted {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    MemLp D.f_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  D.toChartData.f_chart_memLp_weighted

/-- Each weak partial derivative is locally `MemLp 2` (with respect to plain
Lebesgue volume) on every compact subset of `chartTargetEuclid α`. -/
lemma weak_partial_locally_memLp {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weak_partial i) 2 ((volume : Measure EuclN).restrict K) :=
  D.toChartData.weak_partial_locally_memLp i K hK hK_in

/-- Each explicit weak partial derivative is a genuine weak partial derivative of
the chart component `u_chart` on `chartTargetEuclid α` (DeGiorgi sense, against
plain volume). This field is non-vacuous for a non-smooth `u_chart`. -/
lemma weak_partial_isWeakPartial {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (D.weak_partial i) D.u_chart
      (chartTargetEuclid (I := I) (M := M) α) :=
  D.toChartData.weak_partial_isWeakPartial i

/-- The density-weighted per-component variational identity, re-exposed from the
underlying scalar structure. -/
lemma variational_identity {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (ψ : EuclN → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.toChartData.variational_identity ψ hψ hψ_cs hψ_supp

/-- Weighted `MemLp 2` of the chart component on `chartTargetEuclid α` converts
to plain `MemLp 2` on any compact subset `K ⊆ chartTargetEuclid α`. -/
lemma memLp_volume_restrict_u_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.u_chart 2 ((volume : Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted hK_compact hK_meas hK_in

/-- Weighted `MemLp 2` of the right-hand side on `chartTargetEuclid α` converts
to plain `MemLp 2` on any compact subset `K ⊆ chartTargetEuclid α`. -/
lemma memLp_volume_restrict_f_chart {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {α : M} {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.f_chart 2 ((volume : Measure EuclN).restrict K) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.f_chart_memLp_weighted hK_compact hK_meas hK_in

end TensorChartBilinearH1ComplData

/-- **Per-component chart-bilinear identity for a non-smooth tensor chart
component.** Given the chart-bilinear divergence-form data `D` for one chart
`P₀`-component of a non-smooth `(r, s)`-tensor field, the density-weighted
variational identity

```
∫ ∑_{i, j} (√det g · gⁱʲ) · (D.weak_partial i) · ∂_j ψ
  + ∫ √det g · D.u_chart · ψ = ∫ √det g · D.f_chart · ψ
```

on `chartTargetEuclid α` holds for every smooth test function `ψ` with
`tsupport ψ ⊆ chartTargetEuclid α`.

The principal symbol `weightedInvGramOnEuclid g α` (`= √det g · gⁱʲ`) is the
scalar Laplace–Beltrami principal symbol: after the connection-Laplacian
principal part is decoupled per component, each tensor chart component satisfies
this *scalar* divergence-form identity. This is a re-export of
`D.variational_identity` for ergonomics, and the tensor analogue of
`chart_bilinear_identity_h1Compl`. -/
theorem tensor_chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_supp

section ElaborationTests

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    ChartBilinearH1ComplData (I := I) (M := M) g α :=
  D.toChartData

example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀) :
    EuclN → ℝ :=
  D.u_chart

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
