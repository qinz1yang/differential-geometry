import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorPouWkpNormTwins
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightLimit

/-!
# Order-`K` iterated-Sobolev norm bounds for two eigenvector chart limit objects

The chart-Euclidean right-hand side of the connection-Laplacian eigenvector's
weak-solution assembly is built from limit objects that are cutoff Euclidean
chart components of fixed abstract `L²` elements. Two of them — the cross-Leibniz
limits — are treated here at the order-`K` iterated-Sobolev (`wkpNorm`) level:

* `crossLeftLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the completion-extended covariant gradient
  `tensorCovGradL2Compl g r s` applied to the eigenvector resolvent;
* `crossRightLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the `L²`-coercion `TensorH1ComplToTensorL2 g r s`
  of the eigenvector resolvent.

For each, this file records an explicit-constant order-`K` `wkpNorm` bound for
the Euclidean chart target `chartTargetEuclid α`.

## Strategy

Both limit objects are, by definition, single cutoff Euclidean chart components
of abstract `L²` elements; the foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces the order-`K` `wkpNorm`
of any such cutoff component to an explicit constant times a finite double sum,
over the transport chart centres and the component multi-indices, of the
order-`K` `wkpNorm` of the underlying abstract element's partition-of-unity
Euclidean chart components.

* For the cross-right limit the underlying abstract element is the resolvent
  inclusion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)` itself, so
  that finite double sum is already the faithful aggregate of order-`K`
  `wkpNorm` of the resolvent-inclusion partition-of-unity chart components — the
  regularity hypothesis `h_pou` is exactly the `MemWkp` membership of those same
  components, and the bound assembles in one step.
* For the cross-left limit the underlying abstract element is the
  covariant gradient `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`; each
  resulting covariant-gradient chart-component norm is in turn controlled — in
  `MemWkp` (`eigenvectorCovGrad_pou_memWkp`, needed to feed the cutoff lemma) and
  in `wkpNorm` (`eigenvectorCovGrad_pou_wkpNorm_le`) — by an explicit constant
  times an order-`(K+1)` aggregate of the resolvent-inclusion partition-of-unity
  chart components. Composing the two reductions and folding every summation
  multiplicity and per-summand constant into a single headline constant yields
  the order-`K` `wkpNorm` bound, with the regularity hypothesis again phrased on
  the resolvent-inclusion chart components.

## Main results

* `wkpNorm_crossLeftLimitComponent_le`
* `wkpNorm_crossRightLimitComponent_le`

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section CrossRotationWkpNormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

/-! ## Abbreviation for the resolvent-inclusion chart-component norm

The faithful aggregate of both headlines is built from the order-`(K+1)` (for the
cross-left limit) or order-`K` (for the cross-right limit) iterated-Sobolev norm
of the resolvent-inclusion partition-of-unity Euclidean chart components. The
following abbreviation names that per-`(β, Q)` norm at a generic order `N`. -/

/-- The order-`N` iterated-Sobolev norm of the resolvent-inclusion
partition-of-unity Euclidean chart `Q`-component at a chart centre `β`. The
resolvent inclusion is the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i)`. -/
private def resInclChartNorm (N : ℕ) (β : M)
    (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) N 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β)

/-! ## Headline 1 — the cross-left limit object

`crossLeftLimitComponent g r s h_atlas i α P` is, by definition, the cutoff
Euclidean chart component of the abstract `L²` element
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s h_atlas i)` at rank
`(r, s + 1)`. The foundational `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`
reduces its order-`K` `wkpNorm` to a finite double sum of the order-`K` `wkpNorm`
of the covariant-gradient partition-of-unity chart components; each of those is
in turn controlled, in `MemWkp` and in `wkpNorm`, by the order-`(K+1)` aggregate
of the resolvent-inclusion partition-of-unity chart components. -/

/-! ### The per-transport-centre covariant-gradient aggregate

For a transport chart centre `β`, every covariant-gradient chart-component norm
at `β` is `MemWkp` and `wkpNorm`-bounded by an explicit constant times the
two-part order-`(K+1)` aggregate `covGradResAggregate β`: the sum of the
order-`(K+1)` resolvent-inclusion chart-component norms at `β` itself plus the
double sum of those norms over the transport chart centres of `β`. -/

/-- The two-part order-`(K+1)` resolvent-inclusion aggregate at a chart centre
`β` — the sum over component multi-indices of the order-`(K+1)`
resolvent-inclusion chart-component norms at `β` itself, plus the double sum of
those norms over the transport chart centres of `β`. This is exactly the
aggregate produced by `eigenvectorCovGrad_pou_wkpNorm_le`. -/
private def covGradResAggregate (β : M) : ℝ≥0∞ :=
  (∑ Q : TensorCompIdx (E := E) r s,
      resInclChartNorm (I := I) (M := M) g r s h_atlas i (K + 1) β Q)
    + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          resInclChartNorm (I := I) (M := M) g r s h_atlas i (K + 1) β' Q

/-- Each covariant-gradient partition-of-unity chart-component norm at a chart
centre `β` is `MemWkp K 2`, given the order-`(K+1)` `MemWkp` regularity of the
resolvent-inclusion chart components. This is the membership needed to feed the
foundational cutoff bound. -/
private lemma covGradChartComponent_memWkp
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) :=
  eigenvectorCovGrad_pou_memWkp (I := I) (M := M) g r s h_atlas i K h_pou β Q'

/-- Each covariant-gradient partition-of-unity chart-component norm at a chart
centre `β` is `wkpNorm K 2`-bounded by an explicit nonnegative constant times the
order-`(K+1)` resolvent-inclusion aggregate `covGradResAggregate β`. -/
private lemma wkpNorm_covGradChartComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2Compl (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal C *
          covGradResAggregate (I := I) (M := M) g r s h_atlas i K β := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eigenvectorCovGrad_pou_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K h_pou β Q'
  exact ⟨C, hC_nn, hC_bd⟩

/-! ### The double-sum collection lemma

The cutoff bound delivers a finite double sum, over the transport chart centres
`β ∈ S` and the component multi-indices `Q'`, of the order-`K` `wkpNorm` of the
covariant-gradient chart components. Bounding each summand by an explicit
constant times the per-centre aggregate and folding the `Q'`-summation
multiplicity into the constant collapses the double sum to a constant times the
single sum, over `β ∈ S`, of the per-centre aggregates. -/

-- The collection step is established purely from `Finset` subadditivity and
-- arithmetic of `ℝ≥0∞`; the manifold-completeness and closed-manifold instances
-- enter only through the types of the chart objects.
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- A finite double-indexed family of order-`K` `wkpNorm`s, each bounded by
`ENNReal.ofReal` of a per-summand constant times a per-centre aggregate selected
by the outer index, has its double sum bounded by `ENNReal.ofReal` of an explicit
constant times the single sum, over the outer index, of the per-centre
aggregates. -/
private lemma wkpNorm_doubleSum_le_const_mul_aggregateSum
    {ι κ : Type*} [Fintype κ]
    (S : Finset ι) (W : ι → κ → ℝ≥0∞) (aggr : ι → ℝ≥0∞)
    (Cf : ι → κ → ℝ) (hCf_nn : ∀ j ∈ S, ∀ q : κ, 0 ≤ Cf j q)
    (h_bd : ∀ j ∈ S, ∀ q : κ,
      W j q ≤ ENNReal.ofReal (Cf j q) * aggr j) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ j ∈ S, ∑ q : κ, W j q)
        ≤ ENNReal.ofReal C * ∑ j ∈ S, aggr j := by
  classical
  -- A single nonnegative constant dominating every per-summand constant: the
  -- sum of all of them, floored at `1`.
  set Csup : ℝ := 1 + ∑ j ∈ S, ∑ q : κ, Cf j q with hCsup_def
  have hCsup_nn : 0 ≤ Csup := by
    rw [hCsup_def]
    have h_sum_nn : 0 ≤ ∑ j ∈ S, ∑ q : κ, Cf j q :=
      Finset.sum_nonneg (fun j hj =>
        Finset.sum_nonneg (fun q _ => hCf_nn j hj q))
    linarith
  have hCf_le_Csup : ∀ j ∈ S, ∀ q : κ, Cf j q ≤ Csup := by
    intro j hj q
    rw [hCsup_def]
    have h_inner : Cf j q ≤ ∑ q' : κ, Cf j q' :=
      Finset.single_le_sum (f := fun q' => Cf j q')
        (fun q' _ => hCf_nn j hj q') (Finset.mem_univ q)
    have h_outer : (∑ q' : κ, Cf j q') ≤ ∑ j' ∈ S, ∑ q' : κ, Cf j' q' :=
      Finset.single_le_sum (f := fun j' => ∑ q' : κ, Cf j' q')
        (fun j' hj' => Finset.sum_nonneg (fun q' _ => hCf_nn j' hj' q')) hj
    linarith [h_inner.trans h_outer]
  -- The headline constant: the uniform per-summand bound times the
  -- `κ`-cardinality.
  refine ⟨Csup * (Fintype.card κ), by positivity, ?_⟩
  -- Bound each summand by the uniform constant times the per-centre aggregate.
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W j q ≤ ENNReal.ofReal Csup * aggr j := by
    intro j hj q
    refine (h_bd j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  -- Sum the per-summand bounds; the inner sum over `κ` of a constant is the
  -- cardinality times the constant.
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Reassemble: pull the cardinality and the constant out of the outer sum.
  -- `ENNReal.ofReal Csup * Fintype.card κ = ENNReal.ofReal (Csup * card)`.
  have h_const_eq : (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup
      = ENNReal.ofReal (Csup * (Fintype.card κ)) := by
    rw [mul_comm Csup, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
      ENNReal.ofReal_natCast]
  calc
    (∑ j ∈ S, ∑ q : κ, W j q)
        ≤ ∑ j ∈ S, (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr j) :=
          Finset.sum_le_sum h_inner_const
    _ = (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup * ∑ j ∈ S, aggr j := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    _ = ENNReal.ofReal (Csup * (Fintype.card κ)) * ∑ j ∈ S, aggr j := by
          rw [h_const_eq]

/-- **Explicit-constant order-`K` `wkpNorm` bound for the cross-left limit
object.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i`, a chart center `α : M`, a component multi-index
`P : TensorCompIdx r (s + 1)`, and an order `K`, there is a nonnegative constant
`C` with

```
wkpNorm K 2 (crossLeftLimitComponent g r s h_atlas i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')),
```

given the order-`(K+1)` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossLeftLimitComponent` is the cutoff Euclidean chart component
of the abstract `L²` element `tensorCovGradL2Compl g r s (eigenvectorResolvent
…)`; the foundational `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its
order-`K` `wkpNorm` to a finite double sum of the order-`K` `wkpNorm` of the
covariant-gradient partition-of-unity chart components, each of which is in turn
`wkpNorm K 2`-bounded by an explicit constant times the order-`(K+1)`
resolvent-inclusion aggregate. The summation multiplicity and every per-summand
constant are folded into the single constant `C`. -/
theorem wkpNorm_crossLeftLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossLeftLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s h_atlas i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  -- Step 1: the cutoff bound reduces the order-`K` `wkpNorm` of the limit object
  -- to a finite double sum of covariant-gradient chart-component norms.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
      g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
      α P K
      (fun β Q' => covGradChartComponent_memWkp (I := I) (M := M)
        g r s h_atlas i K h_pou β Q')
  -- Step 2: each covariant-gradient chart-component norm is bounded by an
  -- explicit constant times the per-centre order-`(K+1)` aggregate.
  have h_per : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2Compl (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradResAggregate (I := I) (M := M) g r s h_atlas i K β :=
    fun β Q' => wkpNorm_covGradChartComponent_le (I := I) (M := M)
      g r s h_atlas i K h_pou β Q'
  -- Step 3: collect the double sum into a constant times the single sum, over
  -- the transport chart centres, of the per-centre aggregates.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum
      (transportChartCenters (I := I) (M := M) α)
      (fun β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun β => covGradResAggregate (I := I) (M := M) g r s h_atlas i K β)
      (fun β Q' => (h_per β Q').choose)
      (fun β _ Q' => (h_per β Q').choose_spec.1)
      (fun β _ Q' => (h_per β Q').choose_spec.2)
  -- Assemble: the headline constant is `C₀ * C₁`.
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  -- The `covGradResAggregate` unfolds to the explicit double-sum aggregate.
  have h_aggr_eq : (∑ β ∈ transportChartCenters (I := I) (M := M) α,
      covGradResAggregate (I := I) (M := M) g r s h_atlas i K β)
      = ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s h_atlas i))
                        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')) := by
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [covGradResAggregate]
    rfl
  -- Chain the two reductions and pull the constant `C₀ * C₁` together.
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            covGradResAggregate (I := I) (M := M) g r s h_atlas i K β) := by
    -- Rewrite the limit object as the cutoff component, then chain.
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
    rw [h_unfold]
    refine hC₀_bd.trans ?_
    exact mul_le_mul_of_nonneg_left hC₁_bd (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, h_aggr_eq]

end CrossRotationWkpNormBounds

section CrossRightWkpNormBound

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

/-! ## Headline 2 — the cross-right limit object

`crossRightLimitComponent g r s h_atlas i α P` is, by definition, the cutoff
Euclidean chart component of the abstract `L²` element
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i)` — the
resolvent inclusion itself. The foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`, applied to that abstract
element, reduces its order-`K` `wkpNorm` directly to a finite double sum of the
order-`K` `wkpNorm` of the resolvent-inclusion partition-of-unity chart
components — already the faithful aggregate — so the bound assembles in one
step. -/

/-- **Explicit-constant order-`K` `wkpNorm` bound for the cross-right limit
object.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i`, a chart center `α : M`, a component multi-index
`P : TensorCompIdx r s`, and an order `K`, there is a nonnegative constant `C`
with

```
wkpNorm K 2 (crossRightLimitComponent g r s h_atlas i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β),
```

given the order-`K` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossRightLimitComponent` is the cutoff Euclidean chart component
of the abstract `L²` element `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent
…)`; the foundational `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its
order-`K` `wkpNorm` directly to a finite double sum of the order-`K` `wkpNorm` of
the resolvent-inclusion partition-of-unity chart components. -/
theorem wkpNorm_crossRightLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s h_atlas i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  -- Rewrite the limit object as the cutoff component of the resolvent
  -- inclusion, then apply the foundational cutoff bound directly: its `h_pou`
  -- hypothesis is exactly the order-`K` `MemWkp` regularity supplied here.
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
    g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
    α P K h_pou

end CrossRightWkpNormBound

/-! ## Eigenbasis-uniform companions

The two headlines above each `∃`-bind their explicit constant `C` *after* the
eigenbasis index `i`, so `C` is allowed to vary with `i`. The downstream
bounded-operator endpoint instead needs a *single* constant working for every
`i` simultaneously — the `∀ i` quantifier moved *inside* the `∃ C`.

Such an eigenbasis-uniform restatement is not derivable from its per-`i`
original — it carries its own proof, which is the per-`i` proof with the
constant witness hoisted before the `∀ i`. The hoist succeeds because every
per-`i` ingredient already has an eigenbasis-uniform companion:

* the cutoff-component bound `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`
  is *input-uniform* — its constant is chart-transition geometric data,
  independent of the abstract `L²` element, hence of `i`;
* the covariant-gradient chart-component bound
  `eigenvectorCovGrad_pou_wkpNorm_le` has the eigenbasis-uniform companion
  `eigenvectorCovGrad_pou_wkpNorm_le_uniform`, whose constant is *purely
  geometric* — the `‖μ‖ · μ⁻¹` cancellation removes the eigenvalue factor — so
  no residual `(i.fst.val)⁻¹` appears.

Consequently both eigenbasis-uniform headlines take the plain
`∃ C, 0 ≤ C ∧ ∀ i, … ≤ ENNReal.ofReal C * …` shape, with no exposed eigenvalue
factor. -/

section CrossRotationWkpNormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (K : ℕ)

/-! ### The eigenbasis-uniform double-sum collection lemma

`wkpNorm_doubleSum_le_const_mul_aggregateSum` collapses, for one fixed `i`, a
finite double sum to a constant times the single sum of per-centre aggregates;
its per-summand constants come from `eigenvectorCovGrad_pou_wkpNorm_le`. The
eigenbasis-uniform companion `eigenvectorCovGrad_pou_wkpNorm_le_uniform`
delivers a *single* geometric per-summand constant, independent of `i`, so the
collapsed headline constant is itself `i`-independent. The following lemma is
the eigenbasis-indexed restatement: the per-summand constant family `Cf` is
`i`-independent, and the collapsed constant is hoisted before the `∀ i`. -/

-- The collection step is established purely from `Finset` subadditivity and
-- arithmetic of `ℝ≥0∞`; the manifold-completeness and closed-manifold instances
-- enter only through the types of the chart objects.
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- Eigenbasis-uniform double-sum collection. A finite double-indexed family of
order-`K` `wkpNorm`s, indexed additionally by an eigenbasis index `δ` and each
bounded by `ENNReal.ofReal` of a `δ`-independent per-summand constant `Cf j q`
times a per-centre aggregate `aggr δ j` selected by the outer index, has — with
a *single* constant `C`, hoisted before the `∀ δ` — its double sum bounded, for
every `δ`, by `ENNReal.ofReal C` times the single sum, over the outer index, of
the per-centre aggregates. -/
private lemma wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
    {δ ι κ : Type*} [Fintype κ]
    (S : Finset ι) (W : δ → ι → κ → ℝ≥0∞) (aggr : δ → ι → ℝ≥0∞)
    (Cf : ι → κ → ℝ) (hCf_nn : ∀ j ∈ S, ∀ q : κ, 0 ≤ Cf j q)
    (h_bd : ∀ (d : δ), ∀ j ∈ S, ∀ q : κ,
      W d j q ≤ ENNReal.ofReal (Cf j q) * aggr d j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : δ,
        (∑ j ∈ S, ∑ q : κ, W d j q)
          ≤ ENNReal.ofReal C * ∑ j ∈ S, aggr d j := by
  classical
  -- A single nonnegative constant dominating every per-summand constant: the
  -- sum of all of them, floored at `1`. It is `δ`-independent.
  set Csup : ℝ := 1 + ∑ j ∈ S, ∑ q : κ, Cf j q with hCsup_def
  have hCsup_nn : 0 ≤ Csup := by
    rw [hCsup_def]
    have h_sum_nn : 0 ≤ ∑ j ∈ S, ∑ q : κ, Cf j q :=
      Finset.sum_nonneg (fun j hj =>
        Finset.sum_nonneg (fun q _ => hCf_nn j hj q))
    linarith
  have hCf_le_Csup : ∀ j ∈ S, ∀ q : κ, Cf j q ≤ Csup := by
    intro j hj q
    rw [hCsup_def]
    have h_inner : Cf j q ≤ ∑ q' : κ, Cf j q' :=
      Finset.single_le_sum (f := fun q' => Cf j q')
        (fun q' _ => hCf_nn j hj q') (Finset.mem_univ q)
    have h_outer : (∑ q' : κ, Cf j q') ≤ ∑ j' ∈ S, ∑ q' : κ, Cf j' q' :=
      Finset.single_le_sum (f := fun j' => ∑ q' : κ, Cf j' q')
        (fun j' hj' => Finset.sum_nonneg (fun q' _ => hCf_nn j' hj' q')) hj
    linarith [h_inner.trans h_outer]
  -- The headline constant: the uniform per-summand bound times the
  -- `κ`-cardinality. It does not depend on `δ`, so it is hoisted here.
  refine ⟨Csup * (Fintype.card κ), by positivity, fun d => ?_⟩
  -- Bound each summand by the uniform constant times the per-centre aggregate.
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W d j q ≤ ENNReal.ofReal Csup * aggr d j := by
    intro j hj q
    refine (h_bd d j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  -- Sum the per-summand bounds; the inner sum over `κ` of a constant is the
  -- cardinality times the constant.
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W d j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr d j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Reassemble: pull the cardinality and the constant out of the outer sum.
  -- `ENNReal.ofReal Csup * Fintype.card κ = ENNReal.ofReal (Csup * card)`.
  have h_const_eq : (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup
      = ENNReal.ofReal (Csup * (Fintype.card κ)) := by
    rw [mul_comm Csup, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ _),
      ENNReal.ofReal_natCast]
  calc
    (∑ j ∈ S, ∑ q : κ, W d j q)
        ≤ ∑ j ∈ S, (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr d j) :=
          Finset.sum_le_sum h_inner_const
    _ = (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal Csup * ∑ j ∈ S, aggr d j := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    _ = ENNReal.ofReal (Csup * (Fintype.card κ)) * ∑ j ∈ S, aggr d j := by
          rw [h_const_eq]

/-- **Eigenbasis-uniform explicit-constant order-`K` `wkpNorm` bound for the
cross-left limit object.** The eigenbasis-uniform companion of
`wkpNorm_crossLeftLimitComponent_le`: a *single* nonnegative constant `C`,
independent of the eigenbasis index `i`, serves every `i` simultaneously — the
`∀ i` quantifier moved inside the `∃ C`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P : TensorCompIdx r (s + 1)`, and an order
`K`, given the order-`(K+1)` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components — phrased uniformly over
`i` — there is a nonnegative constant `C` with, for every `i`,

```
wkpNorm K 2 (crossLeftLimitComponent g r s h_atlas i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')).
```

No exposed eigenvalue factor appears: the cutoff-component reduction is
input-uniform, and the covariant-gradient chart-component bound's
eigenbasis-uniform companion `eigenvectorCovGrad_pou_wkpNorm_le_uniform` is
purely geometric (the `‖μ‖ · μ⁻¹` cancellation removes the eigenvalue
dependence). The constant `C` is the product of the input-uniform cutoff
constant and the eigenbasis-uniform double-sum collection constant, both
`i`-independent and hence hoisted before the `∀ i`. -/
theorem wkpNorm_crossLeftLimitComponent_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                        (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  -- Step 1: the input-uniform cutoff bound — its constant `C₀` is
  -- chart-transition geometric data, independent of the abstract `L²` element
  -- and hence of `i`; it is hoisted here, before the `∀ i`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r (s + 1) α P K
  -- Step 2: the eigenbasis-uniform covariant-gradient chart-component bound,
  -- invoked at each `(β, Q')`. Because its `h_pou` hypothesis is itself
  -- uniform over `i`, the resulting per-summand constant — extracted as the
  -- `Classical.choice` witness — depends only on `(β, Q')`, not on `i`. Its
  -- per-`i` specification is the bound against the per-centre aggregate.
  set Cf : M → TensorCompIdx (E := E) r (s + 1) → ℝ :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s h_atlas K h_pou β Q').choose
    with hCf_def
  have hCf_spec : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      0 ≤ Cf β Q' ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (Cf β Q') *
              covGradResAggregate (I := I) (M := M) g r s h_atlas i K β :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s h_atlas K h_pou β Q').choose_spec
  -- Step 3: collect the cutoff bound's double sum into a constant times the
  -- single sum, over the transport chart centres, of the per-centre
  -- aggregates. The per-summand constant family `Cf` is `i`-independent, so the
  -- eigenbasis-uniform collection lemma hoists the collapsed constant `C₁`.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
      (δ := TensorEigenIdx (I := I) (M := M) g r s)
      (transportChartCenters (I := I) (M := M) α)
      (fun i β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun i β => covGradResAggregate (I := I) (M := M) g r s h_atlas i K β)
      (fun β Q' => Cf β Q')
      (fun β _ Q' => (hCf_spec β Q').1)
      (fun i β _ Q' => (hCf_spec β Q').2 i)
  -- Assemble: the headline constant is `C₀ * C₁`, hoisted before the `∀ i`.
  refine ⟨C₀ * C₁, by positivity, fun i => ?_⟩
  -- The `covGradResAggregate` unfolds to the explicit double-sum aggregate.
  have h_aggr_eq : (∑ β ∈ transportChartCenters (I := I) (M := M) α,
      covGradResAggregate (I := I) (M := M) g r s h_atlas i K β)
      = ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s h_atlas i))
                        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')) := by
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [covGradResAggregate]
    rfl
  -- Chain the two reductions and pull the constant `C₀ * C₁` together.
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            covGradResAggregate (I := I) (M := M) g r s h_atlas i K β) := by
    -- Rewrite the limit object as the cutoff component, then chain.
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
    rw [h_unfold]
    -- The cutoff bound applied to the covariant-gradient `L²` element, whose
    -- partition-of-unity chart components are `MemWkp` by
    -- `covGradChartComponent_memWkp`.
    refine (hC₀_bd
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
      (fun β Q' => covGradChartComponent_memWkp (I := I) (M := M)
        g r s h_atlas i K (h_pou i) β Q')).trans ?_
    exact mul_le_mul_of_nonneg_left (hC₁_bd i) (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn, h_aggr_eq]

/-- **Eigenbasis-uniform explicit-constant order-`K` `wkpNorm` bound for the
cross-right limit object.** The eigenbasis-uniform companion of
`wkpNorm_crossRightLimitComponent_le`: a *single* nonnegative constant `C`,
independent of the eigenbasis index `i`, serves every `i` simultaneously — the
`∀ i` quantifier moved inside the `∃ C`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P : TensorCompIdx r s`, and an order `K`,
given the order-`K` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components — phrased uniformly over
`i` — there is a nonnegative constant `C` with, for every `i`,

```
wkpNorm K 2 (crossRightLimitComponent g r s h_atlas i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β).
```

No exposed eigenvalue factor appears: `crossRightLimitComponent` is by
definition the cutoff Euclidean chart component of the resolvent inclusion
itself, and the foundational cutoff bound
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` is *input-uniform* — its
constant is chart-transition geometric data, independent of the abstract `L²`
element and hence of `i`. That single constant is hoisted before the `∀ i`. -/
theorem wkpNorm_crossRightLimitComponent_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s h_atlas i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  -- The input-uniform cutoff bound: a single constant `C`, chart-transition
  -- geometric data independent of the abstract `L²` element — hence of `i` —
  -- is hoisted before the `∀ i`.
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r s α P K
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- Rewrite the limit object as the cutoff component of the resolvent
  -- inclusion, then apply the input-uniform cutoff bound at that abstract `L²`
  -- element: its `h_pou` hypothesis is exactly the order-`K` `MemWkp`
  -- regularity supplied here for the index `i`.
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact hC_bd
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
    (h_pou i)

end CrossRotationWkpNormBoundsUniform

/-! ## Chart-locality-free restatements

The cross-right `wkpNorm` bounds above carry the chart-selection hypothesis
`h_atlas` only through the limit object `crossRightLimitComponent`, which is built
from the eigenvector resolvent `eigenvectorResolvent`. The limit object has a
chart-locality-free twin `crossRightLimitComponent_unconditional` — keyed on the
eigenvector resolvent `eigenvectorResolvent_unconditional`, itself built from the
eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`
selected at the unconditional compactness witness. By definition this twin is the
cutoff Euclidean chart component, at `(α, P)`, of the abstract `L²` element
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent_unconditional g r s i)` — the
resolvent inclusion itself. The foundational cutoff `wkpNorm` bound
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` (and its eigenbasis-uniform,
input-uniform companion `…_uniform`) quantifies over an arbitrary abstract `L²`
element, so it applies verbatim to the chart-locality-free limit object, with no
chart-selection hypothesis. The cross-right proof bodies transfer verbatim, with
the resolvent inclusion of `eigenvectorResolvent` replaced by that of
`eigenvectorResolvent_unconditional`. -/

section CrossRightWkpNormBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

/-- **Chart-locality-free explicit-constant order-`K` `wkpNorm` bound for the
cross-right limit object.** Chart-locality-free twin of
`wkpNorm_crossRightLimitComponent_le`. For a closed Riemannian manifold
`(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a chart center `α : M`, a
component multi-index `P : TensorCompIdx r s`, and an order `K`, there is a
nonnegative constant `C` with

```
wkpNorm K 2 (crossRightLimitComponent_unconditional g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β),
```

given the order-`K` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossRightLimitComponent_unconditional` is the cutoff Euclidean
chart component of the abstract `L²` element `TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent_unconditional …)`; the foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its order-`K` `wkpNorm`
directly to a finite double sum of the order-`K` `wkpNorm` of the
resolvent-inclusion partition-of-unity chart components. -/
theorem wkpNorm_crossRightLimitComponent_le_unconditional
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  -- Rewrite the limit object as the cutoff component of the resolvent
  -- inclusion, then apply the foundational cutoff bound directly: its `h_pou`
  -- hypothesis is exactly the order-`K` `MemWkp` regularity supplied here.
  have h_unfold : (fun y => ((crossRightLimitComponent_unconditional (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent_unconditional]
  rw [h_unfold]
  exact wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
    g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
    α P K h_pou

end CrossRightWkpNormBoundUnconditional

section CrossRightWkpNormBoundUniformUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)

/-- **Chart-locality-free eigenbasis-uniform explicit-constant order-`K`
`wkpNorm` bound for the cross-right limit object.** Chart-locality-free twin of
`wkpNorm_crossRightLimitComponent_le_uniform`: a *single* nonnegative constant
`C`, independent of the eigenbasis index `i`, serves every `i` simultaneously,
with no chart-selection hypothesis.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P : TensorCompIdx r s`, and an order `K`,
given the order-`K` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components — phrased uniformly over
`i` — there is a nonnegative constant `C` with, for every `i`,

```
wkpNorm K 2 (crossRightLimitComponent_unconditional g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β).
```

No exposed eigenvalue factor appears: `crossRightLimitComponent_unconditional` is
by definition the cutoff Euclidean chart component of the resolvent inclusion
itself, and the foundational cutoff bound
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` is *input-uniform* — its
constant is chart-transition geometric data, independent of the abstract `L²`
element and hence of `i`. That single constant is hoisted before the `∀ i`. -/
theorem wkpNorm_crossRightLimitComponent_le_uniform_unconditional
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent_unconditional (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  -- The input-uniform cutoff bound: a single constant `C`, chart-transition
  -- geometric data independent of the abstract `L²` element — hence of `i` —
  -- is hoisted before the `∀ i`.
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r s α P K
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- Rewrite the limit object as the cutoff component of the resolvent
  -- inclusion, then apply the input-uniform cutoff bound at that abstract `L²`
  -- element: its `h_pou` hypothesis is exactly the order-`K` `MemWkp`
  -- regularity supplied here for the index `i`.
  have h_unfold : (fun y => ((crossRightLimitComponent_unconditional (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent_unconditional]
  rw [h_unfold]
  exact hC_bd
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
    (h_pou i)

end CrossRightWkpNormBoundUniformUnconditional

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

example
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossLeftLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s h_atlas i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) :=
  wkpNorm_crossLeftLimitComponent_le (I := I) (M := M)
    g r s h_atlas i K h_pou α P

example
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s h_atlas i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) :=
  wkpNorm_crossRightLimitComponent_le (I := I) (M := M)
    g r s h_atlas i K h_pou α P

end ElaborationTests

/-! ## Chart-locality-free restatements — the cross-left limit object

The cross-left `wkpNorm` bounds carry the chart-selection hypothesis `h_atlas`
only through the limit object `crossLeftLimitComponent`, which is built from the
eigenvector resolvent `eigenvectorResolvent`. The limit object has a
chart-locality-free twin `crossLeftLimitComponent_unconditional` — keyed on the
eigenvector resolvent `eigenvectorResolvent_unconditional`, itself built from the
eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`
selected at the unconditional compactness witness. By definition this twin is the
cutoff Euclidean chart component, at `(α, P)`, of the abstract `L²` element
`tensorCovGradL2Compl g r s (eigenvectorResolvent_unconditional g r s i)`. The
foundational cutoff `wkpNorm` bound `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`
(and its eigenbasis-uniform, input-uniform companion `…_uniform`) quantifies over
an arbitrary abstract `L²` element, so it applies verbatim to the
chart-locality-free limit object; the covariant-gradient chart-component
reduction enters through the chart-locality-free covariant-gradient twins
`eigenvectorCovGrad_pou_memWkp_unconditional`,
`eigenvectorCovGrad_pou_wkpNorm_le_unconditional`, and (for the uniform headline)
`eigenvectorCovGrad_pou_wkpNorm_le_uniform_unconditional`. The cross-left proof
bodies transfer verbatim, with the resolvent inclusion of `eigenvectorResolvent`
replaced by that of `eigenvectorResolvent_unconditional` and every per-centre
aggregate written out explicitly. -/

section CrossRotationWkpNormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

/-- **Chart-locality-free explicit-constant order-`K` `wkpNorm` bound for the
cross-left limit object.** Chart-locality-free twin of
`wkpNorm_crossLeftLimitComponent_le`. For a closed Riemannian manifold `(M, g)`,
ranks `(r, s)`, an eigenbasis index `i`, a chart center `α : M`, a component
multi-index `P : TensorCompIdx r (s + 1)`, and an order `K`, there is a
nonnegative constant `C` with

```
wkpNorm K 2 (crossLeftLimitComponent_unconditional g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')),
```

given the order-`(K+1)` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossLeftLimitComponent_unconditional` is the cutoff Euclidean
chart component of the abstract `L²` element `tensorCovGradL2Compl g r s
(eigenvectorResolvent_unconditional …)`; the foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its order-`K` `wkpNorm`
to a finite double sum of the order-`K` `wkpNorm` of the covariant-gradient
partition-of-unity chart components, each of which is in turn `wkpNorm K 2`-bounded
by an explicit constant times the order-`(K+1)` resolvent-inclusion aggregate. The
summation multiplicity and every per-summand constant are folded into the single
constant `C`. -/
theorem wkpNorm_crossLeftLimitComponent_le_unconditional
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent_unconditional (I := I) (M := M)
                              g r s i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  -- The per-centre order-`(K+1)` resolvent-inclusion aggregate, written out
  -- explicitly (the chart-locality-free analogue of `covGradResAggregate`).
  set aggr : M → ℝ≥0∞ := fun β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  -- Step 1: the cutoff bound reduces the order-`K` `wkpNorm` of the limit object
  -- to a finite double sum of covariant-gradient chart-component norms; the
  -- `MemWkp` premises are the chart-locality-free covariant-gradient memberships.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
      g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
      α P K
      (fun β Q' => eigenvectorCovGrad_pou_memWkp_unconditional (I := I) (M := M)
        g r s i K h_pou β Q')
  -- Step 2: each covariant-gradient chart-component norm is bounded by an
  -- explicit constant times the per-centre order-`(K+1)` aggregate.
  have h_per : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2Compl (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C * aggr β :=
    fun β Q' => eigenvectorCovGrad_pou_wkpNorm_le_unconditional (I := I) (M := M)
      g r s i K h_pou β Q'
  -- Step 3: collect the double sum into a constant times the single sum, over
  -- the transport chart centres, of the per-centre aggregates.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum
      (transportChartCenters (I := I) (M := M) α)
      (fun β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun β => aggr β)
      (fun β Q' => (h_per β Q').choose)
      (fun β _ Q' => (h_per β Q').choose_spec.1)
      (fun β _ Q' => (h_per β Q').choose_spec.2)
  -- Assemble: the headline constant is `C₀ * C₁`.
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  -- Chain the two reductions and pull the constant `C₀ * C₁` together.
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr β) := by
    -- Rewrite the limit object as the cutoff component, then chain.
    have h_unfold : (fun y => ((crossLeftLimitComponent_unconditional (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent_unconditional]
    rw [h_unfold]
    refine hC₀_bd.trans ?_
    exact mul_le_mul_of_nonneg_left hC₁_bd (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn]

end CrossRotationWkpNormBoundsUnconditional

section CrossRotationWkpNormBoundsUniformUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)

/-- **Chart-locality-free eigenbasis-uniform explicit-constant order-`K`
`wkpNorm` bound for the cross-left limit object.** Chart-locality-free twin of
`wkpNorm_crossLeftLimitComponent_le_uniform`: a *single* nonnegative constant `C`,
independent of the eigenbasis index `i`, serves every `i` simultaneously, with no
chart-selection hypothesis.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P : TensorCompIdx r (s + 1)`, and an order
`K`, given the order-`(K+1)` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components — phrased uniformly over
`i` — there is a nonnegative constant `C` with, for every `i`,

```
wkpNorm K 2 (crossLeftLimitComponent_unconditional g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')).
```

No exposed eigenvalue factor appears: the cutoff-component reduction is
input-uniform, and the covariant-gradient chart-component bound's
eigenbasis-uniform companion `eigenvectorCovGrad_pou_wkpNorm_le_uniform_unconditional`
is purely geometric (the `‖μ‖ · μ⁻¹` cancellation removes the eigenvalue
dependence). The constant `C` is the product of the input-uniform cutoff constant
and the eigenbasis-uniform double-sum collection constant, both `i`-independent
and hence hoisted before the `∀ i`. -/
theorem wkpNorm_crossLeftLimitComponent_le_uniform_unconditional
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                              (eigenvectorResolvent_unconditional (I := I)
                                (M := M) g r s i))
                            β' Q :
                            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                            EuclN → ℝ) y)
                        (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  -- The per-centre order-`(K+1)` resolvent-inclusion aggregate, written out
  -- explicitly (the chart-locality-free analogue of `covGradResAggregate`),
  -- parametrised by the eigenbasis index `i`.
  set aggr : TensorEigenIdx (I := I) (M := M) g r s → M → ℝ≥0∞ := fun i β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  -- Step 1: the input-uniform cutoff bound — its constant `C₀` is
  -- chart-transition geometric data, independent of the abstract `L²` element
  -- and hence of `i`; it is hoisted here, before the `∀ i`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r (s + 1) α P K
  -- Step 2: the eigenbasis-uniform covariant-gradient chart-component bound,
  -- invoked at each `(β, Q')`. Because its `h_pou` hypothesis is itself uniform
  -- over `i`, the resulting per-summand constant — extracted as the
  -- `Classical.choice` witness — depends only on `(β, Q')`, not on `i`.
  set Cf : M → TensorCompIdx (E := E) r (s + 1) → ℝ :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform_unconditional (I := I) (M := M)
        g r s K h_pou β Q').choose
    with hCf_def
  have hCf_spec : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      0 ≤ Cf β Q' ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M)
                      g r s i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (Cf β Q') * aggr i β :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform_unconditional (I := I) (M := M)
        g r s K h_pou β Q').choose_spec
  -- Step 3: collect the cutoff bound's double sum into a constant times the
  -- single sum, over the transport chart centres, of the per-centre aggregates.
  -- The per-summand constant family `Cf` is `i`-independent, so the
  -- eigenbasis-uniform collection lemma hoists the collapsed constant `C₁`.
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
      (δ := TensorEigenIdx (I := I) (M := M) g r s)
      (transportChartCenters (I := I) (M := M) α)
      (fun i β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun i β => aggr i β)
      (fun β Q' => Cf β Q')
      (fun β _ Q' => (hCf_spec β Q').1)
      (fun i β _ Q' => (hCf_spec β Q').2 i)
  -- Assemble: the headline constant is `C₀ * C₁`, hoisted before the `∀ i`.
  refine ⟨C₀ * C₁, by positivity, fun i => ?_⟩
  -- Chain the two reductions and pull the constant `C₀ * C₁` together.
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr i β) := by
    -- Rewrite the limit object as the cutoff component, then chain.
    have h_unfold : (fun y => ((crossLeftLimitComponent_unconditional (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent_unconditional]
    rw [h_unfold]
    -- The cutoff bound applied to the covariant-gradient `L²` element, whose
    -- partition-of-unity chart components are `MemWkp` by
    -- `eigenvectorCovGrad_pou_memWkp_unconditional`.
    refine (hC₀_bd
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
      (fun β Q' => eigenvectorCovGrad_pou_memWkp_unconditional (I := I) (M := M)
        g r s i K (h_pou i) β Q')).trans ?_
    exact mul_le_mul_of_nonneg_left (hC₁_bd i) (zero_le _)
  refine h_chain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀_nn]

end CrossRotationWkpNormBoundsUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
