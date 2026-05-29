import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffStepWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedScaffold
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSMemW1p
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorArbitraryKRegularity

/-!
# The order-`K` `wkpNorm`-graded bound for the differentiated chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, and a
component multi-index `P₀`, the level-`m` differentiated chart right-hand side
`eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` of the limiting per-component
variational identity is the explicit recursion

* level `0` is the seven-term `eigenvectorChartRHS`;
* level `m + 1` is the indicator, of the compact partition-of-unity kernel, of
  the chart-density-divided differentiated numerator built from the level-`m`
  right-hand side.

This module records the **quantitative** (`wkpNorm`-graded) twin of the
qualitative global iterated-Sobolev regularity headline
`eigenvectorChartRHSDiff_memWkp`. For each `K : ℕ`, given the order-`(m + 1 + K)`
partition-of-unity regularity input `h_pou` on every chart center, there is a
nonnegative constant `C` with

```
wkpNorm K 2 (eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l)
    (chartTargetEuclid α)
  ≤ ENNReal.ofReal (μ⁻¹ * C) * <AGGREGATE m K l>,
```

where `<AGGREGATE m K l>` is the honest finite `ℝ≥0∞`-valued aggregate
`diffRHSAggregate` of primitive regularity data — a recursive sum that, at level
`0`, is the order-`K` seven-term aggregate of the chart right-hand side, and at
level `m + 1`, prepends the order-`(2 + K)` `wkpNorm`s of the iterated weak
partials feeding the differentiated numerator to the level-`m` aggregate at
order `K + 1`.

## Strategy

The headline `eigenvectorChartRHSDiff_wkpNorm_le` is proved by induction on `m`,
with `K` universally quantified so the inductive hypothesis can be invoked at
`K + 1`:

* level `0`: `eigenvectorChartRHSDiff … 0 l = eigenvectorChartRHS …`, whose
  order-`K` `wkpNorm` bound is `eigenvectorChartRHS_wkpNorm_le` — its `h_pou`
  requirement is at order `K + 1 = 0 + 1 + K`, matching this theorem's `h_pou`,
  and its aggregate is, by definition, `diffRHSAggregate … 0 K l`;
* level `m + 1`: writing `l = Fin.snoc (Fin.init l) (l (Fin.last m))`, the
  standalone-step identity `eigenvectorChartIteratedStep_eq_rhsDiff_succ`
  rewrites `eigenvectorChartRHSDiff … (m+1) l` as the level-`(m+1)` standalone
  inductive step over the level-`m` right-hand side. The step `wkpNorm` bound
  `eigenvectorChartIteratedStep_wkpNorm_le` then delivers the order-`K`
  `wkpNorm`, against the differentiated-numerator aggregate
  `diffNumeratorAggregateK`. That aggregate has four pieces: the two iterated
  weak-partial `wkpNorm (2 + K) 2` terms (kept verbatim, forming the level-`(m+1)`
  head `diffRHSHead`), and the order-`(K + 1)` and order-`K` `wkpNorm`s of the
  level-`m` right-hand side. The latter two are bounded by the inductive
  hypothesis at order `K + 1` (the order-`K` term first lifted to order `K + 1`
  by `wkpNorm_mono_order`). Standard `ℝ≥0∞` algebra folds the step constant, the
  inductive constant, and the resolvent eigenvalue's reciprocity into a single
  nonnegative constant.

The three hypotheses of the step `wkpNorm` bound are discharged exactly as in
the qualitative twin, with one improvement: the iterated-weak-partial regularity
`h_iter` — `MemWkp (2 + K) 2` of every `eigenvectorChartIteratedPartial … j idx`
— is supplied **unconditionally** by the arbitrary-order interior regularity
`eigenvector_chartComponent_memWkp_arbitrary` of the eigenvector chart component,
followed by the polymorphic bridge `eigenvectorChartIteratedPartial_memWkp_of_memWkp`;
it needs no partition-of-unity input. The previous-level membership `h_prev` is
the qualitative headline `eigenvectorChartRHSDiff_memWkp` at the previous level
and order `K + 1`; the previous-level ae-vanishing `h_prev_zero` is the
seven-term vanishing at level `0` and the indicator vanishing at positive levels.

The `K = 0` corollary `eigenvectorChartRHSDiff_eLpNorm_le` instantiates the
headline at `K = 0` and rewrites `wkpNorm 0 2` to `eLpNorm` via `wkpNorm_zero`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The order-`K` aggregate for the differentiated chart right-hand side

`diffRHSAggregate` packages the honest finite `ℝ≥0∞`-valued sum of primitive
regularity data controlling the order-`K` `wkpNorm` of the level-`m`
differentiated chart right-hand side. It is a recursion on the level `m`:

* at level `0` it is `rhsZeroAggregate`, the order-`K` seven-term aggregate of
  the source quantities of the chart right-hand side `eigenvectorChartRHS`;
* at level `m + 1` it prepends `diffRHSHead`, the two iterated-weak-partial
  `wkpNorm (2 + K) 2` terms feeding the differentiated numerator, to the
  level-`m` aggregate evaluated at order `K + 1`.

Both `rhsZeroAggregate` and `diffRHSHead` are **data** — `ℝ≥0∞`-valued
quantities, not `Prop`s. -/

/-- The order-`K` seven-term aggregate of the source quantities of the chart
right-hand side `eigenvectorChartRHS`: the canonical eigenvector chart component
`eigenvectorChartComponentFun`; the cross-left and cross-right transport
aggregates of the resolvent-inclusion partition-of-unity chart components; the
chart-partial atoms `partialLpLimit`; the chart-component atoms
`componentLpLimit`; the cutoff cross-right limit objects `crossRightLimitComponent`;
and the cutoff chart-partial atoms `cutoffPartialLpLimit`, all order-`K`
`wkpNorm`s on the chart-`α` target.

This is the level-`0` slice of `diffRHSAggregate`; it is the parenthesised
right-hand side of `eigenvectorChartRHS_wkpNorm_le`. It is **data**. -/
def rhsZeroAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                      g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s h_atlas i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
    + (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))

/-- The level-`(m + 1)` head of `diffRHSAggregate`: the two iterated-weak-partial
`wkpNorm (2 + K) 2` terms feeding the differentiated numerator at level `m`,
along the direction multi-index `l : Fin (m + 1) → Fin n` — the `(m+1)`-fold
mixed partials summed over the first inserted direction, and the `m`-fold mixed
partial along `Fin.init l`.

This collects pieces `A`/`B` and `C` of `diffNumeratorAggregateK`. It is
**data**. -/
def diffRHSHead
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)

/-- The order-`K` aggregate of primitive regularity data controlling the
order-`K` `wkpNorm` of the level-`m` differentiated chart right-hand side.

This is a recursion on the level `m`:

* level `0` is `rhsZeroAggregate`, the order-`K` seven-term aggregate of the
  source quantities of `eigenvectorChartRHS`;
* level `m + 1` is `diffRHSHead` — the two iterated-weak-partial
  `wkpNorm (2 + K) 2` terms — prepended to the level-`m` aggregate evaluated at
  order `K + 1` and direction multi-index `Fin.init l`.

This is **data** — an `ℝ≥0∞`-valued quantity, not a `Prop`. -/
def diffRHSAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  match m, l with
  | 0, _ => rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K
  | m + 1, l =>
      diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K l +
        diffRHSAggregate g r s h_atlas i α P₀ m (K + 1) (Fin.init l)

/-- Definitional unfolding of `diffRHSAggregate` at level `0`. -/
private theorem diffRHSAggregate_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ 0 K l =
      rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K := rfl

/-- Definitional unfolding of `diffRHSAggregate` at level `m + 1`. -/
private theorem diffRHSAggregate_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) K l =
      diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K l +
        diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m (K + 1)
          (Fin.init l) := rfl

/-! ## The level-`m` right-hand side vanishes ae off the partition-of-unity kernel

The step `wkpNorm` bound consumes the ae-vanishing of the level-`m` differentiated
right-hand side off the compact partition-of-unity kernel `chartPouKernel α`. At
level `0` the right-hand side is the seven-term `eigenvectorChartRHS`, whose
ae-vanishing is `eigenvectorChartRHS_ae_zero_off_chartPouKernel`; at every
positive level it is the indicator of the kernel, so vanishes pointwise off it
(`eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel`). -/

omit [CompleteSpace E] in
/-- The level-`m` differentiated chart right-hand side `eigenvectorChartRHSDiff g
r s h_atlas i α P₀ m l` is almost everywhere zero on the open complement of the
compact partition-of-unity kernel `chartPouKernel α` inside the chart target. -/
lemma rhsDiff_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀
  | succ m =>
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ m l hy.2

/-! ## Unconditional iterated-weak-partial regularity

The step `wkpNorm` bound `eigenvectorChartIteratedStep_wkpNorm_le` consumes the
order-`(2 + K)` iterated-Sobolev regularity `h_iter` of every iterated weak
partial `eigenvectorChartIteratedPartial … j idx`. This is supplied
**unconditionally**: the eigenvector chart component lies in `MemWkp k 2` for
every `k` (the arbitrary-order interior regularity
`eigenvector_chartComponent_memWkp_arbitrary`), and the polymorphic bridge
`eigenvectorChartIteratedPartial_memWkp_of_memWkp` transfers chart-`H^{k + j}` of
the component to chart-`H^k` of every `j`-fold mixed weak partial. No
partition-of-unity input is needed. -/

omit [CompleteSpace E] in
/-- **Unconditional order-`(2 + K)` regularity of every iterated weak partial.**
For every direction count `j` and every `j`-direction multi-index `idx`, the
`j`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s h_atlas i α P₀
j idx` lies in `MemWkp (2 + K) 2` on the chart-`α` target.

The eigenvector chart component lies in `MemWkp ((2 + K) + j) 2` on the chart
target for every `j` (`eigenvector_chartComponent_memWkp_arbitrary`); the
polymorphic bridge `eigenvectorChartIteratedPartial_memWkp_of_memWkp` then
delivers `MemWkp (2 + K) 2` of the `j`-fold mixed weak partial. -/
private lemma iteratedPartial_memWkp_two_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) :
    ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro j idx
  -- The eigenvector chart component has interior `W^{(2 + K) + j, 2}` regularity.
  have h_comp : MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s h_atlas i ((2 + K) + j) α P₀
  -- The polymorphic bridge transfers it to the `j`-fold mixed weak partial.
  exact eigenvectorChartIteratedPartial_memWkp_of_memWkp (I := I) (M := M)
    g r s h_atlas i α P₀ j (2 + K) h_comp idx

/-! ## The order-`K` `wkpNorm`-graded bound for the differentiated chart
right-hand side -/

section MainBound

set_option linter.unusedSectionVars false in
/-- The resolvent eigenvalue `μ := i.fst.val` is strictly positive: the
eigenspace at `μ` is non-trivial, so it contains a non-zero eigenvector, and the
resolvent eigenvalues lie in the unit interval `(0, 1]`. -/
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

set_option linter.unusedSectionVars false in
/-- The resolvent eigenvalue `μ := i.fst.val` is at most `1`: the resolvent
eigenvalues lie in the unit interval `(0, 1]`. -/
private lemma eigenIdx_val_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).2

/-- **The order-`K` `wkpNorm`-graded bound for the differentiated chart
right-hand side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, a
component multi-index `P₀`, a level `m`, a regularity order `K`, a direction
multi-index `l : Fin m → Fin n`, and the order-`(m + 1 + K)` partition-of-unity
regularity input `h_pou` on every chart center, there is a nonnegative constant
`C` such that the order-`K` iterated Euclidean Sobolev norm of the level-`m`
differentiated chart right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α
P₀ m l` on the chart-`α` target is bounded by `ENNReal.ofReal (μ⁻¹ * C)` times
the finite order-`K` aggregate `diffRHSAggregate` of primitive regularity data.

This is the quantitative (`wkpNorm`-graded) twin of the qualitative global
iterated-Sobolev regularity headline `eigenvectorChartRHSDiff_memWkp`.

The proof is induction on `m`, with `K` universally quantified so the inductive
hypothesis can be invoked at `K + 1`:

* level `0` is the seven-term `eigenvectorChartRHS`, whose order-`K` `wkpNorm`
  bound is `eigenvectorChartRHS_wkpNorm_le` at order `K + 1 = 0 + 1 + K`, with
  aggregate `diffRHSAggregate … 0 K l = rhsZeroAggregate … K`;
* level `m + 1` rewrites the right-hand side as the standalone inductive step
  (`eigenvectorChartIteratedStep_eq_rhsDiff_succ`) and applies the step `wkpNorm`
  bound `eigenvectorChartIteratedStep_wkpNorm_le`. Its three hypotheses are
  discharged: the iterated-weak-partial regularity `h_iter` unconditionally via
  `iteratedPartial_memWkp_two_add`; the previous-level membership via the
  qualitative headline `eigenvectorChartRHSDiff_memWkp` at order `K + 1`; the
  previous-level ae-vanishing via `rhsDiff_ae_zero_off_chartPouKernel`. The
  differentiated-numerator aggregate splits as `diffRHSHead` plus the
  order-`(K + 1)` and order-`K` `wkpNorm`s of the level-`m` right-hand side,
  the latter two bounded by the inductive hypothesis at order `K + 1`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l := by
  classical
  -- The resolvent eigenvalue lies in `(0, 1]`; its reciprocal is `≥ 1`.
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenIdx_val_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  -- Induction on `m`, with `K` and the direction multi-index `l` generalised so
  -- the inductive hypothesis can be invoked at `K + 1`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is `eigenvectorChartRHS`.
      rw [eigenvectorChartRHSDiff_zero]
      -- `eigenvectorChartRHS_wkpNorm_le` needs `h_pou` at order `K + 1`; this
      -- theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le (I := I) (M := M)
        g r s h_atlas i α P₀ K h_pou'
      refine ⟨C, hC_nn, ?_⟩
      -- The level-`0` aggregate is, by definition, `rhsZeroAggregate`, which is
      -- definitionally the parenthesised right-hand side of
      -- `eigenvectorChartRHS_wkpNorm_le`.
      rw [diffRHSAggregate_zero]
      show wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K
      exact hC_bd
  | succ m ih =>
      -- Level `m + 1`: write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards): the level-`(m+1)`
      -- right-hand side at `Fin.snoc dirs l₀` is the standalone inductive step
      -- over the level-`m` right-hand side.
      rw [← eigenvectorChartIteratedStep_eq_rhsDiff_succ (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Hypothesis (a): the order-`(2 + K)` iterated-weak-partial regularity —
      -- supplied unconditionally.
      have h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        iteratedPartial_memWkp_two_add (I := I) (M := M)
          g r s h_atlas i α P₀ K
      -- Hypothesis (b): the level-`m` right-hand side is `MemWkp (K + 1) 2` —
      -- the qualitative headline at order `K + 1`. Its `h_pou` requirement is at
      -- order `m + 1 + (K + 1) = m + 2 + K`, supplied by this theorem's `h_pou`.
      have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou β Q
      have h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
          g r s h_atlas i α P₀ m (K + 1) (Fin.init l) h_pou_prev
      -- Hypothesis (c): the level-`m` right-hand side is ae-zero off the kernel.
      have h_prev_zero :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) :=
        rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l)
      -- The step `wkpNorm` bound at level `m`.
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le (I := I) (M := M)
          g r s h_atlas i α P₀ m K (Fin.init l)
          (fChartEffPrev := eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (l (Fin.last m)) h_iter h_prev h_prev_zero
      -- The inductive hypothesis at order `K + 1` and direction `Fin.init l`.
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      -- The headline constant: `max Cstep (2 * Cstep * Cih)`.
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn, ?_⟩
      -- Abbreviations for the head and the inductive aggregate.
      set H := diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m (K + 1)
        (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) with hPprev_def
      -- The step bound, in `diffRHSHead`/`wkpNorm` terms: the
      -- differentiated-numerator aggregate `diffNumeratorAggregateK` splits as
      -- `diffRHSHead + wkpNorm (K + 1) Pprev + wkpNorm K Pprev`.
      have h_num_split :
          diffNumeratorAggregateK (I := I) (M := M) g r s h_atlas i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd
      -- The order-`K` `wkpNorm` of `Pprev` is `≤` its order-`(K + 1)` `wkpNorm`.
      have h_prev_mono :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      -- The inductive hypothesis bound on `wkpNorm (K + 1) Pprev`.
      have h_ih_bd :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd
      -- Both `Pprev` `wkpNorm`s are `≤ ENNReal.ofReal (μ⁻¹ * Cih) * D`.
      have h_prev_succ_le :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := h_ih_bd
      have h_prev_K_le :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      -- Bound the differentiated-numerator aggregate:
      -- `H + wkpNorm (K+1) Pprev + wkpNorm K Pprev`
      --   `≤ H + ofReal (μ⁻¹ Cih) D + ofReal (μ⁻¹ Cih) D`.
      have h_aggr_le :
          H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_prev_succ_le) h_prev_K_le
      -- Chain the step bound through the aggregate bound.
      have h_step_chained :
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      -- The level-`(m+1)` aggregate (at the original `l`) is `H + D`.
      have h_target_aggr :
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      -- Set `C' := max Cstep (2 * Cstep * Cih)`.
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      -- Distribute both products over `+`. The left-hand side becomes
      -- `(A + B) + C`, the right-hand side `ofReal(μ⁻¹ C') H + ofReal(μ⁻¹ C') D`.
      rw [mul_add, mul_add, mul_add, add_assoc]
      -- The `H` summand: `ofReal Cstep * H ≤ ofReal (μ⁻¹ C') * H`.
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        -- `Cstep ≤ μ⁻¹ * C'`: since `Cstep ≤ C' ≤ μ⁻¹ * C'` (as `μ⁻¹ ≥ 1`).
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      -- Each `D` summand: `ofReal Cstep * (ofReal(μ⁻¹ Cih) D)`
      --   `≤ ofReal((μ⁻¹ C') / 2) * D`.
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        -- `Cstep * (μ⁻¹ * Cih) ≤ μ⁻¹ * C' / 2`: since `2 Cstep Cih ≤ C'` and
        -- `μ⁻¹ ≥ 1 > 0`.
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      -- The two `D` summands recombine into `ofReal(μ⁻¹ C') * D`.
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      -- Assemble: head summand plus the two tail summands.
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le

/-! ## The eigenbasis-uniform order-`K` `wkpNorm`-graded bound

The per-eigenvector headline `eigenvectorChartRHSDiff_wkpNorm_le` produces, for
each fixed eigenbasis index `i`, a nonnegative constant `C` — quantified *after*
`i`, hence in principle depending on `i`. The downstream bounded-operator
endpoint needs the constant **uniform** across the whole eigenbasis: a single
nonnegative `C` that serves every `i` simultaneously, with only the genuine
resolvent-eigenvalue factor `(i.fst.val)⁻¹` remaining inside the `∀ i`.

`eigenvectorChartRHSDiff_wkpNorm_le_uniform` provides exactly that. It is **not**
derivable from the per-`i` headline — one cannot extract `∃ C, ∀ i` from
`∀ i, ∃ C`. It carries its own proof: the per-`i` induction on `m`, with the
constant produced `i`-freely at every level. At level `0` the base constant is
the eigenbasis-uniform constant of `eigenvectorChartRHS_wkpNorm_le_uniform`; at
level `m + 1` the constant `max Cstep (2 * Cstep * Cih)` is built from the
eigenbasis-uniform step constant `Cstep` of
`eigenvectorChartIteratedStep_wkpNorm_le_uniform` and the inductive constant
`Cih` (uniform by the inductive hypothesis) — an `i`-free arithmetic expression
in `m`, `K`, `l` alone.

The per-`i` regularity input `h_pou` is lifted to a single top-level
`∀ i …`-quantified hypothesis. The `(i.fst.val)⁻¹` factor stays explicit inside
the `∀ i`; only `C` is hoisted out. -/

set_option linter.style.multiGoal false in
/-- **The eigenbasis-uniform order-`K` `wkpNorm`-graded bound for the
differentiated chart right-hand side.**

The constant-uniform twin of `eigenvectorChartRHSDiff_wkpNorm_le`: for a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center `α : M`, a component
multi-index `P₀`, a level `m`, a regularity order `K`, a direction multi-index
`l : Fin m → Fin n`, and the order-`(m + 1 + K)` partition-of-unity regularity
input `h_pou` phrased uniformly over `i`, there is a single nonnegative constant
`C` such that, for *every* eigenbasis index `i` with resolvent eigenvalue
`μ := i.fst.val`, the order-`K` iterated Euclidean Sobolev norm of the level-`m`
differentiated chart right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α
P₀ m l` on the chart-`α` target is bounded by `ENNReal.ofReal (μ⁻¹ * C)` times
the finite order-`K` aggregate `diffRHSAggregate` of primitive regularity data.

A `_uniform` statement cannot be derived from its per-`i` original (one cannot
get `∃ C, ∀ i` from `∀ i, ∃ C`); this carries its own proof — the per-`i`
induction on `m` of `eigenvectorChartRHSDiff_wkpNorm_le`, with the constant
produced `i`-freely at every level. At level `0` the base constant is the
eigenbasis-uniform constant of `eigenvectorChartRHS_wkpNorm_le_uniform`; at level
`m + 1` the constant `max Cstep (2 * Cstep * Cih)` is built from the
eigenbasis-uniform step constant of `eigenvectorChartIteratedStep_wkpNorm_le_uniform`
and the inductive constant — an `i`-free arithmetic expression in `m`, `K`, `l`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l := by
  classical
  -- Induction on `m`, with `K` generalised so the inductive hypothesis can be
  -- invoked at `K + 1`. The direction multi-index `l` and `h_pou` are
  -- generalised automatically, their types depending on `m`. The existential
  -- constant `∃ C` is produced *before* the `∀ i`, with `C` not mentioning `i`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is `eigenvectorChartRHS`.
      -- `eigenvectorChartRHS_wkpNorm_le_uniform` needs `h_pou` at order `K + 1`;
      -- this theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou i β Q
      -- The eigenbasis-uniform level-`0` constant — `i`-free.
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le_uniform
        (I := I) (M := M) g r s h_atlas α P₀ K h_pou'
      refine ⟨C, hC_nn, fun i => ?_⟩
      -- Reduce to `eigenvectorChartRHS` and the level-`0` aggregate.
      rw [eigenvectorChartRHSDiff_zero, diffRHSAggregate_zero]
      -- `rhsZeroAggregate` is definitionally the parenthesised right-hand side
      -- of `eigenvectorChartRHS_wkpNorm_le_uniform`.
      show wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K
      exact hC_bd i
  | succ m ih =>
      -- Level `m + 1`. The previous-level effective right-hand side, as a
      -- function of the eigenbasis index, fed to the uniform step bound.
      set fPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
        fun i => eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l) with hfPrev_def
      -- `h_pou` at order `m + 1 + (K + 1) = m + 2 + K`, phrased uniformly.
      have h_pou_prev : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou i β Q
      -- Hypothesis (a): the order-`(2 + K)` iterated-weak-partial regularity —
      -- supplied unconditionally for every `i`.
      have h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun i => iteratedPartial_memWkp_two_add (I := I) (M := M)
          g r s h_atlas i α P₀ K
      -- Hypothesis (b): the level-`m` right-hand side `fPrev i` is
      -- `MemWkp (K + 1) 2` for every `i` — the qualitative headline at order
      -- `K + 1`.
      have h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fPrev i)
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro i
        rw [hfPrev_def]
        exact eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
          g r s h_atlas i α P₀ m (K + 1) (Fin.init l) (h_pou_prev i)
      -- Hypothesis (c): the level-`m` right-hand side `fPrev i` is ae-zero off
      -- the partition-of-unity kernel for every `i`.
      have h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          (fPrev i) =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        intro i
        rw [hfPrev_def]
        exact rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l)
      -- The eigenbasis-uniform step constant `Cstep` — `i`-free.
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le_uniform (I := I) (M := M)
          g r s h_atlas α P₀ m K (Fin.init l) (l (Fin.last m))
          (fChartEffPrev := fPrev) h_iter h_prev h_prev_zero
      -- The inductive constant `Cih` at order `K + 1` and direction `Fin.init l`
      -- — `i`-free by the inductive hypothesis.
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      -- The headline constant `max Cstep (2 * Cstep * Cih)` — `i`-free.
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn,
        fun i => ?_⟩
      -- The per-`i` argument: the resolvent eigenvalue lies in `(0, 1]`.
      have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
      have hμ_le_one : i.fst.val ≤ 1 :=
        eigenIdx_val_le_one (I := I) (M := M) g r s i
      have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
      -- Write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards).
      rw [← eigenvectorChartIteratedStep_eq_rhsDiff_succ (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Abbreviations for the head and the inductive aggregate.
      set H := diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m (K + 1)
        (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) with hPprev_def
      -- The step bound at the index `i`. `fPrev i` is definitionally `Pprev`.
      have hCstep_bd_i := hCstep_bd i
      have hfPrev_i : fPrev i = Pprev := by rw [hfPrev_def, hPprev_def]
      rw [hfPrev_i] at hCstep_bd_i
      -- The differentiated-numerator aggregate `diffNumeratorAggregateK` splits
      -- as `diffRHSHead + wkpNorm (K + 1) Pprev + wkpNorm K Pprev`.
      have h_num_split :
          diffNumeratorAggregateK (I := I) (M := M) g r s h_atlas i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd_i
      -- The order-`K` `wkpNorm` of `Pprev` is `≤` its order-`(K + 1)` `wkpNorm`.
      have h_prev_mono :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      -- The inductive hypothesis bound on `wkpNorm (K + 1) Pprev`.
      have h_ih_bd :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd i
      have h_prev_K_le :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      -- Bound the differentiated-numerator aggregate.
      have h_aggr_le :
          H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_ih_bd) h_prev_K_le
      -- Chain the step bound through the aggregate bound.
      have h_step_chained :
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd_i (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      -- The level-`(m+1)` aggregate (at the original `l`) is `H + D`.
      have h_target_aggr :
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      -- Set `C' := max Cstep (2 * Cstep * Cih)`.
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      -- Distribute both products over `+`.
      rw [mul_add, mul_add, mul_add, add_assoc]
      -- The `H` summand: `ofReal Cstep * H ≤ ofReal (μ⁻¹ C') * H`.
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      -- Each `D` summand: `ofReal Cstep * (ofReal(μ⁻¹ Cih) D) ≤ ofReal(μ⁻¹ C'/2) D`.
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      -- The two `D` summands recombine into `ofReal(μ⁻¹ C') * D`.
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le

/-! ## The `K = 0` corollary — the weighted-`eLpNorm` bound

At `K = 0` the order-`K` `wkpNorm`-graded bound becomes a weighted-`eLpNorm`
bound: `wkpNorm 0 2 f Ω = eLpNorm f 2 (volume.restrict Ω)` by `wkpNorm_zero`. -/

/-- **The weighted-`eLpNorm` bound for the differentiated chart right-hand
side.**

The `K = 0` instance of `eigenvectorChartRHSDiff_wkpNorm_le`: for a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i` with
resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, a component
multi-index `P₀`, a level `m`, a direction multi-index `l : Fin m → Fin n`, and
the order-`(m + 1)` partition-of-unity regularity input `h_pou`, there is a
nonnegative constant `C` such that the `L²`-norm of the level-`m` differentiated
chart right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` against
the plain Lebesgue volume restricted to the chart-`α` target is bounded by
`ENNReal.ofReal (μ⁻¹ * C)` times the order-`0` aggregate `diffRHSAggregate … m 0
l`.

At `K = 0` the headline `eigenvectorChartRHSDiff_wkpNorm_le` produces an order-`0`
`wkpNorm` bound; `wkpNorm_zero` restates the order-`0` `wkpNorm` as the weighted
`eLpNorm`. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
          2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, ?_⟩
  -- `wkpNorm 0 2 f Ω = eLpNorm f 2 (volume.restrict Ω)`.
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd

/-- **The eigenbasis-uniform weighted-`eLpNorm` bound for the differentiated
chart right-hand side.**

The constant-uniform twin of `eigenvectorChartRHSDiff_eLpNorm_le`, and the
`K = 0` instance of `eigenvectorChartRHSDiff_wkpNorm_le_uniform`: for a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center `α : M`, a component
multi-index `P₀`, a level `m`, a direction multi-index `l : Fin m → Fin n`, and
the order-`(m + 1)` partition-of-unity regularity input `h_pou` phrased uniformly
over `i`, there is a single nonnegative constant `C` such that, for *every*
eigenbasis index `i` with resolvent eigenvalue `μ := i.fst.val`, the `L²`-norm of
the level-`m` differentiated chart right-hand side `eigenvectorChartRHSDiff g r s
h_atlas i α P₀ m l` against the plain Lebesgue volume restricted to the chart-`α`
target is bounded by `ENNReal.ofReal (μ⁻¹ * C)` times the order-`0` aggregate
`diffRHSAggregate … m 0 l`.

A `_uniform` statement cannot be derived from its per-`i` original (one cannot
get `∃ C, ∀ i` from `∀ i, ∃ C`); this carries its own proof — the eigenbasis-
uniform headline `eigenvectorChartRHSDiff_wkpNorm_le_uniform` at `K = 0`, with
the order-`0` `wkpNorm` restated as the weighted `eLpNorm` via `wkpNorm_zero`. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m l)
            2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- `wkpNorm 0 2 f Ω = eLpNorm f 2 (volume.restrict Ω)`.
  have hC_bd_i := hC_bd i
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd_i

end MainBound

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The headline produces, from the order-`(m + 1 + K)` partition-of-unity
regularity input, the order-`K` `wkpNorm`-graded bound for the differentiated
chart right-hand side. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l :=
  eigenvectorChartRHSDiff_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m K l h_pou

/-- The `K = 0` corollary produces the weighted-`eLpNorm` bound for the
differentiated chart right-hand side. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
          2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m 0 l :=
  eigenvectorChartRHSDiff_eLpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m l h_pou

/-- The eigenbasis-uniform headline produces, from the uniformly-phrased
order-`(m + 1 + K)` partition-of-unity regularity input, a single nonnegative
constant serving the order-`K` `wkpNorm`-graded bound for *every* eigenbasis
index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l :=
  eigenvectorChartRHSDiff_wkpNorm_le_uniform (I := I) (M := M)
    g r s h_atlas α P₀ m K l h_pou

/-- The eigenbasis-uniform `K = 0` corollary produces a single nonnegative
constant serving the weighted-`eLpNorm` bound for *every* eigenbasis index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m l)
            2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m 0 l :=
  eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
    g r s h_atlas α P₀ m l h_pou

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations below are the chart-locality-free twins of the
partition-of-unity-keyed declarations above. Each proves the same statement
without the chart-selection hypothesis `h_atlas`, re-keyed onto the intrinsic
compact-operator eigenbasis (`tensorResolventEigenbasisVec_ofCompact` at the
intrinsic compactness witness `tensorResolventL2_isCompactOperator_intrinsic`).
The aggregate twins are **data**; the bound twins carry their own proofs,
structurally identical to the originals with the chart-locality-free siblings
substituted throughout. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `rhsZeroAggregate`. -/
def rhsZeroAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                      g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent_unconditional (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
    + (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))

/-- Chart-locality-free twin of `diffRHSHead`. -/
def diffRHSHead_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `diffRHSAggregate`. -/
def diffRHSAggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  match m, l with
  | 0, _ => rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K
  | m + 1, l =>
      diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K l +
        diffRHSAggregate_unconditional g r s i α P₀ m (K + 1) (Fin.init l)

/-- Chart-locality-free twin of `diffRHSAggregate_zero`. -/
private theorem diffRHSAggregate_zero_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ 0 K l =
      rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K := rfl

/-- Chart-locality-free twin of `diffRHSAggregate_succ`. -/
private theorem diffRHSAggregate_succ_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ (m + 1) K l =
      diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K l +
        diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ m (K + 1)
          (Fin.init l) := rfl

/-- Chart-locality-free twin of `rhsDiff_ae_zero_off_chartPouKernel`. -/
lemma rhsDiff_ae_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      rw [eigenvectorChartRHSDiff_unconditional_zero]
      exact eigenvectorChartRHS_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀
  | succ m =>
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_unconditional_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m l hy.2

/-- Chart-locality-free twin of `iteratedPartial_memWkp_two_add`. -/
private lemma iteratedPartial_memWkp_two_add_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) :
    ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro j idx
  -- The eigenvector chart component has interior `W^{(2 + K) + j, 2}` regularity.
  have h_comp : MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary_unconditional (I := I) (M := M)
      g r s i ((2 + K) + j) α P₀
  -- The polymorphic bridge transfers it to the `j`-fold mixed weak partial.
  exact eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp (I := I)
    (M := M) g r s i α P₀ j (2 + K) h_comp idx

/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_wkpNorm_le`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m K l := by
  classical
  -- The resolvent eigenvalue lies in `(0, 1]`; its reciprocal is `≥ 1`.
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenIdx_val_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  -- Induction on `m`, with `K` and the direction multi-index `l` generalised so
  -- the inductive hypothesis can be invoked at `K + 1`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is
      -- `eigenvectorChartRHS_unconditional`.
      rw [eigenvectorChartRHSDiff_unconditional_zero]
      -- `eigenvectorChartRHS_wkpNorm_le_unconditional` needs `h_pou` at order
      -- `K + 1`; this theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le_unconditional
        (I := I) (M := M) g r s i α P₀ K h_pou'
      refine ⟨C, hC_nn, ?_⟩
      -- The level-`0` aggregate is, by definition, `rhsZeroAggregate_unconditional`,
      -- which is definitionally the parenthesised right-hand side of
      -- `eigenvectorChartRHS_wkpNorm_le_unconditional`.
      rw [diffRHSAggregate_zero_unconditional]
      show wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K
      exact hC_bd
  | succ m ih =>
      -- Level `m + 1`: write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards).
      rw [← eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ (I := I)
        (M := M) g r s i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Hypothesis (a): the order-`(2 + K)` iterated-weak-partial regularity —
      -- supplied unconditionally.
      have h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        iteratedPartial_memWkp_two_add_unconditional (I := I) (M := M)
          g r s i α P₀ K
      -- Hypothesis (b): the level-`m` right-hand side is `MemWkp (K + 1) 2` —
      -- the qualitative headline at order `K + 1`.
      have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou β Q
      have h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartRHSDiff_memWkp_unconditional (I := I) (M := M)
          g r s i α P₀ m (K + 1) (Fin.init l) h_pou_prev
      -- Hypothesis (c): the level-`m` right-hand side is ae-zero off the kernel.
      have h_prev_zero :
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) :=
        rhsDiff_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)
      -- The step `wkpNorm` bound at level `m`.
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le_unconditional (I := I) (M := M)
          g r s i α P₀ m K (Fin.init l)
          (fChartEffPrev := eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (l (Fin.last m)) h_iter h_prev h_prev_zero
      -- The inductive hypothesis at order `K + 1` and direction `Fin.init l`.
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      -- The headline constant: `max Cstep (2 * Cstep * Cih)`.
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn, ?_⟩
      -- Abbreviations for the head and the inductive aggregate.
      set H := diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate_unconditional (I := I) (M := M)
        g r s i α P₀ m (K + 1) (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) with hPprev_def
      -- The differentiated-numerator aggregate `diffNumeratorAggregateK_unconditional`
      -- splits as `diffRHSHead_unconditional + wkpNorm (K + 1) Pprev + wkpNorm K Pprev`.
      have h_num_split :
          diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd
      -- The order-`K` `wkpNorm` of `Pprev` is `≤` its order-`(K + 1)` `wkpNorm`.
      have h_prev_mono :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      -- The inductive hypothesis bound on `wkpNorm (K + 1) Pprev`.
      have h_ih_bd :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd
      have h_prev_succ_le :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := h_ih_bd
      have h_prev_K_le :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      -- Bound the differentiated-numerator aggregate.
      have h_aggr_le :
          H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_prev_succ_le) h_prev_K_le
      -- Chain the step bound through the aggregate bound.
      have h_step_chained :
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      -- The level-`(m+1)` aggregate (at the original `l`) is `H + D`.
      have h_target_aggr :
          diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ_unconditional, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      -- Set `C' := max Cstep (2 * Cstep * Cih)`.
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      -- Distribute both products over `+`.
      rw [mul_add, mul_add, mul_add, add_assoc]
      -- The `H` summand: `ofReal Cstep * H ≤ ofReal (μ⁻¹ C') * H`.
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      -- Each `D` summand.
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      -- The two `D` summands recombine into `ofReal(μ⁻¹ C') * D`.
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le

set_option linter.style.multiGoal false in
/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_wkpNorm_le_uniform`. -/
theorem eigenvectorChartRHSDiff_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m K l := by
  classical
  -- Induction on `m`, with `K` generalised so the inductive hypothesis can be
  -- invoked at `K + 1`. The existential constant `∃ C` is produced *before* the
  -- `∀ i`, with `C` not mentioning `i`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is
      -- `eigenvectorChartRHS_unconditional`.
      have h_pou' : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou i β Q
      -- The eigenbasis-uniform level-`0` constant — `i`-free.
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le_uniform_unconditional
        (I := I) (M := M) g r s α P₀ K h_pou'
      refine ⟨C, hC_nn, fun i => ?_⟩
      -- Reduce to `eigenvectorChartRHS_unconditional` and the level-`0` aggregate.
      rw [eigenvectorChartRHSDiff_unconditional_zero,
        diffRHSAggregate_zero_unconditional]
      -- `rhsZeroAggregate_unconditional` is definitionally the parenthesised
      -- right-hand side of `eigenvectorChartRHS_wkpNorm_le_uniform_unconditional`.
      show wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K
      exact hC_bd i
  | succ m ih =>
      -- Level `m + 1`. The previous-level effective right-hand side, as a
      -- function of the eigenbasis index, fed to the uniform step bound.
      set fPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
        fun i => eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) with hfPrev_def
      -- `h_pou` at order `m + 1 + (K + 1) = m + 2 + K`, phrased uniformly.
      have h_pou_prev : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou i β Q
      -- Hypothesis (a): the order-`(2 + K)` iterated-weak-partial regularity —
      -- supplied unconditionally for every `i`.
      have h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun i => iteratedPartial_memWkp_two_add_unconditional (I := I) (M := M)
          g r s i α P₀ K
      -- Hypothesis (b): the level-`m` right-hand side `fPrev i` is
      -- `MemWkp (K + 1) 2` for every `i`.
      have h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fPrev i)
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro i
        rw [hfPrev_def]
        exact eigenvectorChartRHSDiff_memWkp_unconditional (I := I) (M := M)
          g r s i α P₀ m (K + 1) (Fin.init l) (h_pou_prev i)
      -- Hypothesis (c): the level-`m` right-hand side `fPrev i` is ae-zero off
      -- the partition-of-unity kernel for every `i`.
      have h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          (fPrev i) =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        intro i
        rw [hfPrev_def]
        exact rhsDiff_ae_zero_off_chartPouKernel_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)
      -- The eigenbasis-uniform step constant `Cstep` — `i`-free.
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le_uniform_unconditional (I := I)
          (M := M) g r s α P₀ m K (Fin.init l) (l (Fin.last m))
          (fChartEffPrev := fPrev) h_iter h_prev h_prev_zero
      -- The inductive constant `Cih` at order `K + 1` and direction `Fin.init l`
      -- — `i`-free by the inductive hypothesis.
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      -- The headline constant `max Cstep (2 * Cstep * Cih)` — `i`-free.
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn,
        fun i => ?_⟩
      -- The per-`i` argument: the resolvent eigenvalue lies in `(0, 1]`.
      have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
      have hμ_le_one : i.fst.val ≤ 1 :=
        eigenIdx_val_le_one (I := I) (M := M) g r s i
      have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
      -- Write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards).
      rw [← eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ (I := I)
        (M := M) g r s i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Abbreviations for the head and the inductive aggregate.
      set H := diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate_unconditional (I := I) (M := M)
        g r s i α P₀ m (K + 1) (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) with hPprev_def
      -- The step bound at the index `i`. `fPrev i` is definitionally `Pprev`.
      have hCstep_bd_i := hCstep_bd i
      have hfPrev_i : fPrev i = Pprev := by rw [hfPrev_def, hPprev_def]
      rw [hfPrev_i] at hCstep_bd_i
      -- The differentiated-numerator aggregate splits as
      -- `diffRHSHead_unconditional + wkpNorm (K + 1) Pprev + wkpNorm K Pprev`.
      have h_num_split :
          diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd_i
      -- The order-`K` `wkpNorm` of `Pprev` is `≤` its order-`(K + 1)` `wkpNorm`.
      have h_prev_mono :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      -- The inductive hypothesis bound on `wkpNorm (K + 1) Pprev`.
      have h_ih_bd :
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd i
      have h_prev_K_le :
          wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      -- Bound the differentiated-numerator aggregate.
      have h_aggr_le :
          H
              + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + wkpNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_ih_bd) h_prev_K_le
      -- Chain the step bound through the aggregate bound.
      have h_step_chained :
          wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd_i (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      -- The level-`(m+1)` aggregate (at the original `l`) is `H + D`.
      have h_target_aggr :
          diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ_unconditional, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      -- Set `C' := max Cstep (2 * Cstep * Cih)`.
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      -- Distribute both products over `+`.
      rw [mul_add, mul_add, mul_add, add_assoc]
      -- The `H` summand: `ofReal Cstep * H ≤ ofReal (μ⁻¹ C') * H`.
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      -- Each `D` summand.
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      -- The two `D` summands recombine into `ofReal(μ⁻¹ C') * D`.
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le

/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_eLpNorm_le`. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m l)
          2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le_unconditional
    (I := I) (M := M) g r s i α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, ?_⟩
  -- `wkpNorm 0 2 f Ω = eLpNorm f 2 (volume.restrict Ω)`.
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd

/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_eLpNorm_le_uniform`. -/
theorem eigenvectorChartRHSDiff_eLpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m l)
            2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le_uniform_unconditional
    (I := I) (M := M) g r s α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- `wkpNorm 0 2 f Ω = eLpNorm f 2 (volume.restrict Ω)`.
  have hC_bd_i := hC_bd i
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd_i

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
