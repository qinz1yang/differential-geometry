import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace
import DifferentialGeometry.Integral.Measure.Family

/-!
# Sub-critical Sobolev embedding `W^{1,p}_chart(M) ↪ L^{p*}(M, μ_g)`,
half-space (with-boundary) variant — per-chart bounds

For a smooth manifold `M` modelled on the canonical Euclidean half-space
`EuclideanHalfSpace n` (`n ≥ 1`), with a smooth Riemannian metric `g`, and
`1 ≤ p < n`, this file provides the per-chart sub-critical Sobolev embedding
on the half-space-relatively-open chart targets, via the boundaryless
sub-critical Sobolev theorem applied to the open interior part of each chart
target.

## Key reduction

The chart-based norm `wkpNormChart` for the with-boundary case is built from
the half-space-Dirichlet norm `wkpNormHalfSpace`, which by definition is the
boundaryless `wkpNorm` evaluated on the open set
`interiorHalfSpace Ω = Ω ∩ openHalfSpace`. Likewise, `MemWkpHalfSpace` is by
definition the boundaryless `MemWkp` on `interiorHalfSpace Ω`. The chart
target `Ω = chartTargetEuclid α = (extChartAt I α).target` is half-space-
relatively-open, so its interior part is open in `EuclideanSpace ℝ (Fin n)`.

Consequently, the boundaryless Euclidean sub-critical Sobolev embedding
`EuclideanSubcritical.eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp` applies
verbatim to functions `f : EuN → ℝ` whose `tsupport` lies in the open interior
part of the half-space-relatively-open chart target. The conclusion is
expressed in terms of `wkpNorm 1 p f (interiorHalfSpace Ω)`, which equals
`wkpNormHalfSpace 1 p f Ω` by definition.

## Main results

### Pure-Euclidean half-space sub-critical Sobolev bounds

* `eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace` — the
  per-chart Euclidean sub-critical Sobolev embedding on a half-space-
  relatively-open carrier, for functions whose `tsupport` lies in the open
  interior part of the carrier (`MemWkpHalfSpace` form).
* `eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace` — same, for smooth
  inputs.

### Per-chart bounds on the chart-target carrier

* `chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace`,
  `chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace`
  — specialisations to the chart target.

### Per-chart bounds on the chart-pushed function

* `chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace`,
  `chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart`
  — specialisations to `chartPushed ρ_α α u`.

### Summed chart-side bound

* `chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart` — the
  sum over chart points `α : M` of the chart-side L^{p*} norms is bounded
  by `wkpNormChart`, for smooth inputs whose chart-pushed functions have
  `tsupport` in the open interior of every chart target.

### Equivalences

* `wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace`,
  `memWkpHalfSpace_iff_memWkp_interiorHalfSpace` — definitional equivalences
  routing the half-space-Dirichlet predicates through the boundaryless ones
  on the open interior part.
* `interiorHalfSpace_chartTargetEuclid_eq`,
  `interiorHalfSpace_chartTargetEuclid_isOpen` — the interior part of a chart
  target is the open set obtained by intersecting with the open half-space.

## Scope note

The full manifold-side headline `eLpNorm u p_star μ_g ≤ C · wkpNormChart g 1 p u`
requires a measure-bridge linking the manifold-side `L^{p*}`-norm to the
chart-side L^{p*}-norms expressed against the volume measure on the chart
target. The boundaryless module provides this bridge under the standard
Mathlib identification `toEuclidean : E ≃L EuclideanSpace ℝ (Fin (finrank E))`,
but that identification does not in general preserve the half-space structure
(see the scope note in `WithBoundary/Chart.lean`). Building the with-boundary
measure-bridge directly on `EuclideanSpace ℝ (Fin n)` (the model space of the
canonical half-space) is delivered in the broader with-boundary measure-bridge
infrastructure module; the present file ships the Euclidean-side per-chart
ingredients and the summed chart-side bound, which together with the bridge
yield the manifold-side headline.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]

local notation "EuN" => EuclideanSpace ℝ (Fin n)

/-- By definition, the half-space-Dirichlet `wkpNormHalfSpace k p u Ω` equals
the boundaryless `wkpNorm k p u (interiorHalfSpace Ω)`. -/
theorem wkpNormHalfSpace_eq_wkpNorm_interiorHalfSpace
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p u Ω =
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := n) k p u
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
  rfl

/-- The half-space-Dirichlet membership `MemWkpHalfSpace k p u Ω` equals
the boundaryless `MemWkp k p u (interiorHalfSpace Ω)`. -/
theorem memWkpHalfSpace_iff_memWkp_interiorHalfSpace
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) k p u Ω ↔
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := n) k p u
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :=
  Iff.rfl

/-- **Per-chart Euclidean sub-critical Sobolev embedding on a half-space-
relatively-open carrier.**

For `f : EuN → ℝ` in `MemWkpHalfSpace 1 p f Ω` (i.e. `MemWkp 1 p f` on the
open interior part `interiorHalfSpace Ω`), with compact support and
`tsupport f ⊆ interiorHalfSpace Ω` (in the open interior part), and for
`1 ≤ p < n`, the L^{p*}-norm of `f` over the open interior part is bounded
by a constant depending on `n` and `p` times the half-space iterated W^{1,p}
norm of `f` over `Ω`.

The theorem reduces to the boundaryless Euclidean sub-critical Sobolev
embedding on the open set `interiorHalfSpace Ω`, with the conclusion
re-packaged in terms of `wkpNormHalfSpace`. -/
theorem eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) {Ω : Set EuN}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen
      (d := n) Ω)
    {f : EuN → ℝ}
    (hf : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) 1 (ENNReal.ofReal p) f Ω)
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :
    eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (d := n) Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen hΩ
  have h_main :=
    DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanSubcritical.eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
      (d := n) hp_one hp_dim hΩ_int_open hf hf_compact hf_supp
  exact h_main

/-- **Per-chart Euclidean sub-critical Sobolev embedding for smooth inputs.**

For smooth, compactly-supported `f : EuN → ℝ` with `tsupport f ⊆
interiorHalfSpace Ω` (the open part of the half-space-relatively-open chart
target), and for `1 ≤ p < n`, we have

  `eLpNorm f p_star (volume.restrict (interiorHalfSpace Ω))
    ≤ ENNReal.ofReal C_gns(n,p) * n * wkpNormHalfSpace 1 p f Ω`,

where `p_star = n p / (n - p)`. -/
theorem eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) {Ω : Set EuN}
    (hΩ : DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen
      (d := n) Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω) :
    eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (d := n) Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen hΩ
  have hp_pos : 0 < p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hf_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) 1 (ENNReal.ofReal p) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := n) hΩ_int_open hf_smooth hf_compact hf_supp hp_enn_one 1
  exact eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) hp_one hp_dim hΩ hf_mem hf_compact hf_supp

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-- The interior part of the chart target equals
`(extChartAt I α).target ∩ openHalfSpace`. -/
theorem interiorHalfSpace_chartTargetEuclid_eq (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α) =
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target ∩
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
  unfold chartTargetEuclid
  rfl

/-- The interior part of every chart target is open in `EuN`. -/
theorem interiorHalfSpace_chartTargetEuclid_isOpen (α : M) :
    IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)

/-- **Per-chart sub-critical Sobolev bound on a half-space chart target,
smooth-input case.**

For smooth, compactly-supported `f : EuN → ℝ` with `tsupport f ⊆
interiorHalfSpace (chartTargetEuclid α)`, and for `1 ≤ p < n`, the
L^{p*}-bound holds with constant depending only on `n` and `p`. -/
theorem chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f
          (chartTargetEuclid (n := n) (M := M) α) :=
  eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    (n := n) hp_one hp_dim
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    hf_smooth hf_compact hf_supp

/-- **Per-chart sub-critical Sobolev bound on a half-space chart target,
`MemWkpHalfSpace` case.**

For `f : EuN → ℝ` in `MemWkpHalfSpace 1 p f (chartTargetEuclid α)`, with
compact support and `tsupport f ⊆ interiorHalfSpace (chartTargetEuclid α)`,
and for `1 ≤ p < n`, the L^{p*}-bound holds with constant depending only on
`n` and `p`. -/
theorem chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {f : EuN → ℝ}
    (hf : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) 1 (ENNReal.ofReal p) f
      (chartTargetEuclid (n := n) (M := M) α))
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    eLpNorm f
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p) f
          (chartTargetEuclid (n := n) (M := M) α) :=
  eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) hp_one hp_dim
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    hf hf_compact hf_supp

/-- **Per-chart bound for the chart-pushed function.**

For smooth, compactly-supported chart-pushed functions whose `tsupport` lies
in the open interior part of the chart target. -/
theorem chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {u : M → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_compact : HasCompactSupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_supp : tsupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    eLpNorm
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := by
  let _ := g
  exact chartTargetEuclid_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
    (n := n) (M := M) hp_one hp_dim α hf_smooth hf_compact hf_supp

/-- **Per-chart bound for the chart-pushed function (`MemWkpHalfSpace` form).** -/
theorem chartPushed_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpChart
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) (α : M)
    {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u)
    (hf_compact : HasCompactSupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u))
    (hf_supp : tsupport
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    eLpNorm
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u)
        (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) :=
  chartTargetEuclid_eLpNorm_p_star_le_const_mul_wkpNormHalfSpace_of_memWkpHalfSpace
    (n := n) (M := M) hp_one hp_dim α (hu α) hf_compact hf_supp

/-- **Summed per-chart bound: smooth-input case.**

For smooth `u : M → ℝ` whose chart-pushed functions all have `tsupport` in
the open interior of each chart target, the sum of L^{p*}-norms on the chart
sides is bounded by the chart-based Sobolev norm `wkpNormChart`, with a
constant depending only on `n`, `p`, and the size of the POU support set. -/
theorem chartPushed_sum_eLpNorm_p_star_smooth_le_const_mul_wkpNormChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ))
    {u : M → ℝ}
    (h_smooth : ∀ α : M,
      ContDiff ℝ (⊤ : ℕ∞)
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u))
    (h_compact : ∀ α : M,
      HasCompactSupport
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u))
    (h_supp : ∀ α : M,
      tsupport
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ∑' α : M,
      eLpNorm
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) *
        wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u := by
  classical
  set C : ℝ≥0∞ := ENNReal.ofReal (DeGiorgi.C_gns n p) * (n : ℝ≥0∞) with hC_def
  have h_per : ∀ α : M,
      eLpNorm
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
        C *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)
            (chartTargetEuclid (n := n) (M := M) α) := fun α =>
    chartPushed_eLpNorm_p_star_smooth_le_const_mul_wkpNormHalfSpace
      (n := n) (M := M) g hp_one hp_dim α (h_smooth α) (h_compact α) (h_supp α)
  have h_sum := ENNReal.tsum_le_tsum h_per
  have h_factor : ∑' α : M, C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) =
      C * wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u := by
    rw [ENNReal.tsum_mul_left]
    rfl
  rw [h_factor] at h_sum
  exact h_sum

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
