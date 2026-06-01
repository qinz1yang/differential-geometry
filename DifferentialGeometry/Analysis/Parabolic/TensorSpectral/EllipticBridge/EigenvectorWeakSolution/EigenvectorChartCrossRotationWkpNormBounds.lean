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
* `wkpNorm_crossLeftLimitComponent_le_uniform`
* `wkpNorm_crossRightLimitComponent_le_uniform`

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section CrossRotationWkpNormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

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
  refine ⟨Csup * (Fintype.card κ), by positivity, ?_⟩
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W j q ≤ ENNReal.ofReal Csup * aggr j := by
    intro j hj q
    refine (h_bd j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
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

end CrossRotationWkpNormBounds

section CrossRotationWkpNormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (K : ℕ)

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
  refine ⟨Csup * (Fintype.card κ), by positivity, fun d => ?_⟩
  have h_each : ∀ j ∈ S, ∀ q : κ,
      W d j q ≤ ENNReal.ofReal Csup * aggr d j := by
    intro j hj q
    refine (h_bd d j hj q).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCf_le_Csup j hj q)) (zero_le _)
  have h_inner_const : ∀ j ∈ S,
      (∑ q : κ, W d j q)
        ≤ (Fintype.card κ : ℝ≥0∞) * (ENNReal.ofReal Csup * aggr d j) := by
    intro j hj
    refine (Finset.sum_le_sum (fun q _ => h_each j hj q)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
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

end CrossRotationWkpNormBoundsUniform

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
wkpNorm K 2 (crossRightLimitComponent g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β),
```

given the order-`K` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossRightLimitComponent` is the cutoff Euclidean
chart component of the abstract `L²` element `TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent …)`; the foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its order-`K` `wkpNorm`
directly to a finite double sum of the order-`K` `wkpNorm` of the
resolvent-inclusion partition-of-unity chart components. -/
theorem wkpNorm_crossRightLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
    g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
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
wkpNorm K 2 (crossRightLimitComponent g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α, ∑ Q,
          wkpNorm K 2 (resolvent-inclusion chart Q-component at β).
```

No exposed eigenvalue factor appears: `crossRightLimitComponent` is
by definition the cutoff Euclidean chart component of the resolvent inclusion
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
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r s α P K
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_unfold : (fun y => ((crossRightLimitComponent (I := I)
        (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) y) := by
    rw [crossRightLimitComponent]
  rw [h_unfold]
  exact hC_bd
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    (h_pou i)

end CrossRightWkpNormBoundUniformUnconditional

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
wkpNorm K 2 (crossLeftLimitComponent g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')),
```

given the order-`(K+1)` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components.

By definition `crossLeftLimitComponent` is the cutoff Euclidean
chart component of the abstract `L²` element `tensorCovGradL2Compl g r s
(eigenvectorResolvent …)`; the foundational
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou` reduces its order-`K` `wkpNorm`
to a finite double sum of the order-`K` `wkpNorm` of the covariant-gradient
partition-of-unity chart components, each of which is in turn `wkpNorm K 2`-bounded
by an explicit constant times the order-`(K+1)` resolvent-inclusion aggregate. The
summation multiplicity and every per-summand constant are folded into the single
constant `C`. -/
theorem wkpNorm_crossLeftLimitComponent_le
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set aggr : M → ℝ≥0∞ := fun β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M)
      g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))
      α P K
      (fun β Q' => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
        g r s i K h_pou β Q')
  have h_per : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2Compl (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C * aggr β :=
    fun β Q' => eigenvectorCovGrad_pou_wkpNorm_le (I := I) (M := M)
      g r s i K h_pou β Q'
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum
      (transportChartCenters (I := I) (M := M) α)
      (fun β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun β => aggr β)
      (fun β Q' => (h_per β Q').choose)
      (fun β _ Q' => (h_per β Q').choose_spec.1)
      (fun β _ Q' => (h_per β Q').choose_spec.2)
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr β) := by
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
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
wkpNorm K 2 (crossLeftLimitComponent g r s i α P) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C
      * ∑ β ∈ transportChartCenters α,
          ((∑ Q, wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β))
            + ∑ β' ∈ transportChartCenters β, ∑ Q,
                wkpNorm (K+1) 2 (resolvent-inclusion chart Q-component at β')).
```

No exposed eigenvalue factor appears: the cutoff-component reduction is
input-uniform, and the covariant-gradient chart-component bound's
eigenbasis-uniform companion `eigenvectorCovGrad_pou_wkpNorm_le_uniform`
is purely geometric (the `‖μ‖ · μ⁻¹` cancellation removes the eigenvalue
dependence). The constant `C` is the product of the input-uniform cutoff constant
and the eigenbasis-uniform double-sum collection constant, both `i`-independent
and hence hoisted before the `∀ i`. -/
theorem wkpNorm_crossLeftLimitComponent_le_uniform
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ((∑ Q : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
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
                              (eigenvectorResolvent (I := I)
                                (M := M) g r s i))
                            β' Q :
                            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                            EuclN → ℝ) y)
                        (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set aggr : TensorEigenIdx (I := I) (M := M) g r s → M → ℝ≥0∞ := fun i β =>
    (∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β')
    with haggr_def
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform (I := I) (M := M)
      g r (s + 1) α P K
  set Cf : M → TensorCompIdx (E := E) r (s + 1) → ℝ :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s K h_pou β Q').choose
    with hCf_def
  have hCf_spec : ∀ (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)),
      0 ≤ Cf β Q' ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (Cf β Q') * aggr i β :=
    fun β Q' =>
      (eigenvectorCovGrad_pou_wkpNorm_le_uniform (I := I) (M := M)
        g r s K h_pou β Q').choose_spec
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ :=
    wkpNorm_doubleSum_le_const_mul_aggregateSum_uniform
      (δ := TensorEigenIdx (I := I) (M := M) g r s)
      (transportChartCenters (I := I) (M := M) α)
      (fun i β Q' => wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
      (fun i β => aggr i β)
      (fun β Q' => Cf β Q')
      (fun β _ Q' => (hCf_spec β Q').1)
      (fun i β _ Q' => (hCf_spec β Q').2 i)
  refine ⟨C₀ * C₁, by positivity, fun i => ?_⟩
  have h_chain : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal C₁ *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α, aggr i β) := by
    have h_unfold : (fun y => ((crossLeftLimitComponent (I := I)
          (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        = (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            α P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) := by
      rw [crossLeftLimitComponent]
    rw [h_unfold]
    refine (hC₀_bd
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))
      (fun β Q' => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
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
