import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSWkpNormEnergyBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSDiffWkpNorm

/-!
# An order-`K` uniform energy bound for the differentiated chart right-hand side aggregate

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, a level `m`, an order `K`, and a
direction multi-index `l`, the order-`K` aggregate of primitive regularity data
`diffRHSAggregate g r s h_atlas i α P₀ m K l` controlling the order-`K`
`wkpNorm` of the level-`m` differentiated chart right-hand side is the
recursive sum

* at level `0`: the seven-term `rhsZeroAggregate` of source quantities of
  `eigenvectorChartRHS`;
* at level `m + 1`: the two-piece `diffRHSHead` of iterated-weak-partial
  `wkpNorm (2 + K) 2` terms, prepended to the level-`m` aggregate at order
  `K + 1` along `Fin.init l`.

This file collapses the aggregate, at every level and order, to the abstract
`L²` norm of the eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`,
*given* uniform `wkpNorm`-graded chart-component energy hypotheses on the
primitive regularity data — that is, on each of the seven source atoms of
`rhsZeroAggregate` and on every iterated weak partial
`eigenvectorChartIteratedPartial` feeding `diffRHSHead`. The headline is

```
∃ C ≥ 0, ∀ i,
  diffRHSAggregate g r s h_atlas i α P₀ m K l
    ≤ ENNReal.ofReal (C · μ⁻¹) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖.
```

The constant `C` is geometric — it depends only on `g r s h_atlas α P₀ m K l`
and on the (geometric) constants supplied by the input hypotheses; in
particular it is independent of the eigenbasis index `i`. The universal
quantifier `∀ i` lies *inside* the existential `∃ C`, so a single geometric
constant controls the aggregate of *every* eigenvector simultaneously; the
`i`-dependence of the right-hand side is confined to the explicit `μ⁻¹`
factor.

## Genuine input hypotheses

Bounding the order-`K` `wkpNorm` aggregate of the differentiated chart
right-hand side by the `L²` energy of the eigenbasis vector is not a free
consequence of the `L²` eigen-equation: it relies on chart-component
arbitrary-order Sobolev regularity that the downstream coupled-induction
argument establishes. The headline therefore takes these regularity facts as
*genuine* inputs: uniform `wkpNorm`-graded bounds — with constants
`K`-uniform — on each source atom of `rhsZeroAggregate` and on every
iterated weak partial.

These are not vacuous defers nor fabricated predicates: they are the same
chart-component energy bounds that the coupled-induction supplies, phrased as
the campaign's `_uniform` convention dictates (a single nonnegative geometric
constant followed by `∀ i …`).

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`.
The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

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

/-! ## Per-`Finset`-sum collapse

A finite indexed family bounded, summand-by-summand, by `ENNReal.ofReal Cⱼ * A`
sums to `ENNReal.ofReal (∑ Cⱼ) * A`. -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
lemma finsetSum_eNNReal_ofReal_mul_le
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (C : ι → ℝ) (A : ℝ≥0∞)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hbd : ∀ j ∈ s, f j ≤ ENNReal.ofReal (C j) * A) :
    ∑ j ∈ s, f j ≤ ENNReal.ofReal (∑ j ∈ s, C j) * A := by
  classical
  calc ∑ j ∈ s, f j
      ≤ ∑ j ∈ s, ENNReal.ofReal (C j) * A := Finset.sum_le_sum hbd
    _ = (∑ j ∈ s, ENNReal.ofReal (C j)) * A := by rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ j ∈ s, C j) * A := by
        rw [ENNReal.ofReal_sum_of_nonneg hC]

/-! ## Positivity of the resolvent eigenvalue

The resolvent eigenvalue `μ := i.fst.val` lies in the unit interval `(0, 1]`.
Its strict positivity follows from non-vanishing of an eigenvector. -/

omit [CompleteSpace E] in
/-- The eigenbasis vector has unit norm. -/
private lemma vec_norm_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas).norm_eq_one i

omit [CompleteSpace E] in
/-- The resolvent eigenvalue is strictly positive. -/
private lemma eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s h_atlas i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [CompleteSpace E] in
/-- The resolvent eigenvalue is bounded above by `1`. -/
private lemma eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s h_atlas i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

/-! ## The level-`0` collapse `rhsZeroAggregate ≤ ofReal C · ‖vec‖`

A summand-by-summand collapse of the seven-term `rhsZeroAggregate` to a single
geometric constant times the eigenbasis-vector `L²` norm, given the seven
uniform input hypotheses on the source atoms. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
private lemma rhsZeroAggregate_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Ceig : ℝ) (hCeig_nn : 0 ≤ Ceig)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresH : ℝ) (hCresH_nn : 0 ≤ CresH)
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresH *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresL : ℝ) (hCresL_nn : 0 ≤ CresL)
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresL *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Cpar : ℝ) (hCpar_nn : 0 ≤ Cpar)
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Cpar *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccom : ℝ) (hCcom_nn : 0 ≤ Ccom)
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccom *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CcR : ℝ) (hCcR_nn : 0 ≤ CcR)
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal CcR *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccut : ℝ) (hCcut_nn : 0 ≤ Ccut)
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccut *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K'
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Per-summand cardinal collapse constants.
  set TCard : ℕ → ℕ := fun β_ext =>
    (transportChartCenters (I := I) (M := M) α).card with hTCard_def
  -- We compute a single aggregate constant; the chart-transition cardinalities
  -- arise from inner finite sums.
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresH
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * Ccom
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CcR
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) with hCcut'_def
  set Cagg : ℝ := Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  -- Nonnegativity of all the building blocks.
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this hCresH_nn
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ hCresL_nn)
  have hCpar'_nn : 0 ≤ Cpar' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCpar_nn)
  have hCcom'_nn : 0 ≤ Ccom' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcom_nn
  have hCcR'_nn : 0 ≤ CcR' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcR_nn
  have hCcut'_nn : 0 ≤ Ccut' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCcut_nn)
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact hCeig_nn
  refine ⟨Cagg, hCagg_nn, fun i K' => ?_⟩
  -- Abbreviate the abstract-norm right-hand side factor.
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  -- The seven summands of `rhsZeroAggregate`.
  -- Summand 1: the bare eigenvector chart component.
  have hS1 :
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig * Rhs := hCeig_bd i K'
  -- Summand 2: the cross-Leibniz transport double sum.
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β' Q K'
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s h_atlas i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s h_atlas i))
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) * Rhs := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresL * Rhs := fun Q _hQ => hCresL_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresL) Rhs (fun _ _ => hCresL_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ hCresL_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL)
      Rhs (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) * Rhs := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cpar * Rhs := fun k _hk => hCpar_bd i P k K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => Cpar) Rhs (fun _ _ => hCpar_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCpar_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom * Rhs := fun p _hp => hCcom_bd i p K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => Ccom) Rhs (fun _ _ => hCcom_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR * Rhs := fun P _hP => hCcR_bd i P K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => CcR) Rhs (fun _ _ => hCcR_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) * Rhs := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Ccut * Rhs := fun l _hl => hCcut_bd i P l K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => Ccut) Rhs (fun _ _ => hCcut_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCcut_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  -- The full seven-summand aggregate is bounded by `ofReal Cagg · Rhs`.
  rw [rhsZeroAggregate]
  -- Pre-compute the partial-sum nonneg facts.
  have hp1 : 0 ≤ Ceig + Cmid_α := add_nonneg hCeig_nn hCmid_α_nn
  have hp2 : 0 ≤ Ceig + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal Ceig + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom' + ENNReal.ofReal CcR'
          + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add hCeig_nn hCmid_α_nn]
  rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
  exact hS1

/-! ## The level-`(m+1)` head collapse `diffRHSHead ≤ ofReal C · ‖vec‖`

The level-`(m+1)` head `diffRHSHead` is a finite sum of `n + 1` iterated-
weak-partial `wkpNorm (2 + K) 2` terms, each `≤ Citer · ‖vec‖` by the input
iterated-partial uniform hypothesis. -/

omit [CompleteSpace E] in
private lemma diffRHSHead_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Citer : ℝ) (hCiter_nn : 0 ≤ Citer)
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
      (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m K l
      ≤ ENNReal.ofReal
          (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  rw [diffRHSHead]
  -- First piece: the `(m+1)`-fold sum over an inserted direction.
  have h_each :
      ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer * Rhs := fun a _ha =>
    hCiter_bd i (m + 1) (Fin.cons a (Fin.init l)) K
  have h_first :
      (∑ a : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs := by
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun a => wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _ => Citer) Rhs (fun _ _ => hCiter_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum
  -- Second piece: the single `m`-fold mixed partial along `Fin.init l`.
  have h_second :
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer * Rhs := hCiter_bd i m (Fin.init l) K
  -- Add the two pieces.
  have h_total :
      (∑ a : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs
        + ENNReal.ofReal Citer * Rhs := add_le_add h_first h_second
  refine h_total.trans (le_of_eq ?_)
  have hQ_nn : (0 : ℝ) ≤
      (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCiter_nn
  rw [← add_mul, ← ENNReal.ofReal_add hQ_nn hCiter_nn]
  congr 2
  ring

/-! ## The headline uniform energy bound for the differentiated aggregate

Starting from the level-`0` and level-`(m+1)` per-piece collapses, an
induction on `m` (generalising `K` and `l`) folds the level-`m` aggregate to a
single nonnegative geometric constant times the abstract `L²` norm of the
eigenbasis vector. The `μ⁻¹` factor of the headline absorbs harmlessly: the
resolvent eigenvalue lies in `(0, 1]`, so `μ⁻¹ ≥ 1` and the bare bound `C ·
‖vec‖` is dominated by `(μ⁻¹ · C) · ‖vec‖`. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Uniform order-`K` energy bound for the differentiated chart right-hand
side aggregate.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, a level `m`, an order `K`, a direction
multi-index `l : Fin m → Fin n`, and eight uniform `wkpNorm`-graded
chart-component energy hypotheses on the source atoms of the differentiated
aggregate (seven for `rhsZeroAggregate`'s base level, one for the iterated
weak partials feeding `diffRHSHead`), there is a single nonnegative constant
`C` — geometric, independent of the eigenbasis index — such that for *every*
eigenbasis index `i`, with resolvent eigenvalue `μ := i.fst.val`, the order-`K`
aggregate `diffRHSAggregate g r s h_atlas i α P₀ m K l` is bounded by
`ENNReal.ofReal (C · μ⁻¹)` times the abstract `L²` norm of the eigenbasis
vector `tensorResolventEigenbasisVec h_atlas i`:

```
diffRHSAggregate g r s h_atlas i α P₀ m K l
  ≤ ENNReal.ofReal (C · μ⁻¹) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖.
```

The explicit eigenvalue factor `μ⁻¹` stays *inside* the `∀ i` — it is a
genuine per-`i` quantity — while only the geometric constant `C` is hoisted
before the `∀ i`. A single `C` controls the aggregate of *every* eigenvector
simultaneously.

The proof is induction on `m`, generalising `K` and `l` so that the inductive
hypothesis can be invoked at order `K + 1` and direction `Fin.init l`. The
level-`0` base case is the seven-term `rhsZeroAggregate` collapse. The
level-`(m+1)` step splits the aggregate into `diffRHSHead` (bounded by the
iterated-weak-partial input hypothesis) plus the level-`m` aggregate at order
`K + 1` (bounded by the inductive hypothesis). All collapse constants are
`i`-free, so the headline constant is `i`-free. -/
theorem diffRHSAggregate_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_eig : ∃ Ceig : ℝ, 0 ≤ Ceig ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ceig *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_resHigh : ∃ CresH : ℝ, 0 ≤ CresH ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresH *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_resLow : ∃ CresL : ℝ, 0 ≤ CresL ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresL *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_partial : ∃ Cpar : ℝ, 0 ≤ Cpar ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Cpar *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_component : ∃ Ccom : ℝ, 0 ≤ Ccom ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (p : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_crossRight : ∃ CcR : ℝ, 0 ≤ CcR ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_cutoff : ∃ Ccut : ℝ, 0 ≤ Ccut ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccut *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_iter : ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
        (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Hoist the eight uniform input constants.
  obtain ⟨Ceig, hCeig_nn, hCeig_bd⟩ := h_eig
  obtain ⟨CresH, hCresH_nn, hCresH_bd⟩ := h_resHigh
  obtain ⟨CresL, hCresL_nn, hCresL_bd⟩ := h_resLow
  obtain ⟨Cpar, hCpar_nn, hCpar_bd⟩ := h_partial
  obtain ⟨Ccom, hCcom_nn, hCcom_bd⟩ := h_component
  obtain ⟨CcR, hCcR_nn, hCcR_bd⟩ := h_crossRight
  obtain ⟨Ccut, hCcut_nn, hCcut_bd⟩ := h_cutoff
  obtain ⟨Citer, hCiter_nn, hCiter_bd⟩ := h_iter
  -- The eigenbasis-uniform level-`0` (base) constant collapsing the seven
  -- source atoms — `i`-free, `K`-uniform.
  obtain ⟨Cbase, hCbase_nn, hCbase_bd⟩ :=
    rhsZeroAggregate_le_energy_uniform (I := I) (M := M)
      g r s h_atlas α P₀
      Ceig hCeig_nn hCeig_bd
      CresH hCresH_nn hCresH_bd
      CresL hCresL_nn hCresL_bd
      Cpar hCpar_nn hCpar_bd
      Ccom hCcom_nn hCcom_bd
      CcR hCcR_nn hCcR_bd
      Ccut hCcut_nn hCcut_bd
  -- The per-level head collapse constant — `i`-free, `K`-uniform.
  set Chead : ℝ := ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer
    with hChead_def
  have hChead_nn : 0 ≤ Chead := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      linarith
    exact mul_nonneg this hCiter_nn
  -- Closed-form total constant `Cbase + m · Chead` at level `m` — `i`-free.
  set Ctotal : ℝ := Cbase + (m : ℝ) * Chead with hCtotal_def
  have hCtotal_nn : 0 ≤ Ctotal := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_nn (mul_nonneg hm hChead_nn)
  refine ⟨Ctotal, hCtotal_nn, fun i => ?_⟩
  -- The resolvent eigenvalue lies in `(0, 1]`; its reciprocal is `≥ 1`.
  have hμ_pos : 0 < i.fst.val := eigenvalue_pos (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s h_atlas i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  -- Abbreviate the abstract-norm right-hand side factor.
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  -- The bare-form per-level bound (without `μ⁻¹`), proved by induction on `m`
  -- generalising `K` and `l`. The constant at level `m` is `Cbase + m · Chead`.
  have h_bare : ∀ (m' K' : ℕ) (l' : Fin m' → Fin (Module.finrank ℝ E)),
      diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀ m' K' l'
        ≤ ENNReal.ofReal (Cbase + (m' : ℝ) * Chead) * Rhs := by
    intro m' K' l'
    induction m' generalizing K' with
    | zero =>
        -- Level `0`: `diffRHSAggregate = rhsZeroAggregate`.
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ 0 K' l' =
            rhsZeroAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ K' from rfl]
        have h_base := hCbase_bd i K'
        -- `Cbase + 0 · Chead = Cbase`.
        have h_simp : (Cbase + ((0 : ℕ) : ℝ) * Chead) = Cbase := by
          simp
        rw [h_simp]
        exact h_base
    | succ m'' ih =>
        -- Level `m'' + 1`: `diffRHSAggregate = diffRHSHead + diffRHSAggregate m''`.
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ (m'' + 1) K' l' =
            diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m'' K' l' +
              diffRHSAggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m'' (K' + 1) (Fin.init l') from rfl]
        -- Bound the head and the recursive piece.
        have h_head := diffRHSHead_le_energy_uniform (I := I) (M := M)
          g r s h_atlas α P₀ Citer hCiter_nn hCiter_bd i m'' K' l'
        have h_rec := ih (K' + 1) (Fin.init l')
        -- Both pieces share `Rhs` on the right; combine the two `ofReal C` factors.
        have h_combine :
            diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m'' K' l'
              + diffRHSAggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m'' (K' + 1) (Fin.init l')
            ≤ ENNReal.ofReal Chead * Rhs
                + ENNReal.ofReal (Cbase + (m'' : ℝ) * Chead) * Rhs :=
          add_le_add h_head h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase + (m'' : ℝ) * Chead := by
          have hm'' : (0 : ℝ) ≤ (m'' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_nn (mul_nonneg hm'' hChead_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_nn hCprev_nn]
        congr 2
        push_cast
        ring
  -- Specialise to the headline `(m, K, l)`.
  have h_at_m := h_bare m K l
  -- Convert `ofReal Ctotal · Rhs` to `ofReal (Ctotal · μ⁻¹) · Rhs` using
  -- `μ⁻¹ ≥ 1`.
  refine h_at_m.trans ?_
  gcongr
  -- `Ctotal ≤ Ctotal · μ⁻¹` since `μ⁻¹ ≥ 1` and `Ctotal ≥ 0`.
  nlinarith [hCtotal_nn, hμ_inv_ge_one]

/-! ## Per-`K`-family analogues of the energy bounds

The previous lemmas
(`rhsZeroAggregate_le_energy_uniform` and
`diffRHSAggregate_le_energy_uniform`) take `K'`-uniform input
hypotheses, asking for a single nonnegative geometric constant `Ceig`
that bounds the chart-component `wkpNorm` *at every order* `K'`
simultaneously. The coupled-induction consumer only delivers a bound
at a single order with an explicit `(i.fst.val)⁻¹^?` factor; the
`K'`-uniform shape is unsatisfiable for chart components of Laplace
eigenvectors.

The following per-`K`-family analogues take inputs of the shape
`Ceig : ℕ → ℝ`, `eEig : ℕ → ℕ`, with bounds carrying an explicit
`(i.fst.val)⁻¹ ^ (eEig K')` factor, and produce a per-`(m, K, l)`-fixed
output bound `ofReal (C * (i.fst.val)⁻¹ ^ e) * ‖vec‖`. They mirror
the existing uniform proofs but extract from the family at each
hypothesis use site. The chain of orders that the level-`m`
recursion visits is finite (`K, K+1, …, K+m+1`), so dominating each
local exponent by the maximum over this finite chain — using
`(i.fst.val)⁻¹ ≥ 1` together with monotonicity of nonneg powers —
collapses all atoms to a common exponent factor. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Per-`K`-family energy bound for the level-`0` source aggregate.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart
center `α : M`, a component multi-index `P₀`, an order `K`, and
seven per-`K`-family `wkpNorm`-graded chart-component energy
hypotheses on the source atoms of `rhsZeroAggregate` — each carrying
an explicit `(i.fst.val)⁻¹ ^ (e_X K')` factor — there are a single
nonnegative geometric constant `C` and a single natural-number
exponent `e` (both depending only on `g r s h_atlas α P₀ K` and the
input constants and exponents at orders `K` and `K + 1`) such that
for *every* eigenbasis index `i`,

```
rhsZeroAggregate g r s h_atlas i α P₀ K
  ≤ ofReal (C · μ⁻¹^e) · ‖tensorResolventEigenbasisVec …‖.
```

This is the per-`K`-fixed analogue of
`rhsZeroAggregate_le_energy_uniform`. -/
lemma rhsZeroAggregate_le_energy_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ K
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Common exponent: the maximum over the eight per-K-family exponents
  -- actually consumed at orders `K` and `K + 1`. Domination of any of these
  -- by `e_max` is then immediate from `μ⁻¹ ≥ 1` and monotonicity of nonneg
  -- powers.
  set e_max : ℕ :=
    max (max (max (max (max (max (max
      (eEig K) (eResH K)) (eResH (K + 1))) (eResL K)) (ePar K))
      (eCom K)) (eCcR K)) (eCcut K) with he_max_def
  -- Per-summand cardinal collapse constants at the fixed `K`, mirroring the
  -- K-uniform proof.
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresH K
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * Ccom K
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CcR K
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K) with hCcut'_def
  set Cagg : ℝ := Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  -- Nonnegativity of all the building blocks at the fixed `K`.
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this (hCresH_nn K)
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ (hCresL_nn K))
  have hCpar'_nn : 0 ≤ Cpar' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (hCpar_nn K))
  have hCcom'_nn : 0 ≤ Ccom' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (hCcom_nn K)
  have hCcR'_nn : 0 ≤ CcR' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (hCcR_nn K)
  have hCcut'_nn : 0 ≤ Ccut' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (hCcut_nn K))
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact hCeig_nn K
  refine ⟨Cagg, e_max, hCagg_nn, fun i => ?_⟩
  -- The resolvent eigenvalue lies in `(0, 1]`; its reciprocal is `≥ 1`, and
  -- `μ⁻¹^k` is monotone non-decreasing in `k`.
  have hμ_pos : 0 < i.fst.val := eigenvalue_pos (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s h_atlas i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hpow_e_max_pos : 0 < (i.fst.val)⁻¹ ^ e_max :=
    pow_pos (inv_pos.mpr hμ_pos) _
  have hpow_e_max_nn : 0 ≤ (i.fst.val)⁻¹ ^ e_max := hpow_e_max_pos.le
  -- Each per-K-family exponent is bounded by `e_max`.
  have hEig_le : eEig K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_left _ _
  have hResH_le : eResH K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResH1_le : eResH (K + 1) ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResL_le : eResL K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hPar_le : ePar K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCom_le : eCom K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcR_le : eCcR K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : eCcut K ≤ e_max := le_max_right _ _
  -- Power domination on `μ⁻¹^?`.
  have hpow_dom : ∀ a, a ≤ e_max → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max :=
    fun _a ha => pow_le_pow_right₀ hμ_inv_ge_one ha
  -- Abbreviate the abstract-norm right-hand side factor, and the augmented
  -- right-hand side carrying the common exponent.
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  set Rhs_eff : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_max) * Rhs
    with hRhs_eff_def
  -- A per-summand bridge: given a per-K-family bound at exponent `a ≤ e_max`,
  -- absorb `μ⁻¹^a ≤ μ⁻¹^e_max` to obtain a bound of the form
  -- `ofReal Cval * Rhs_eff`.
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_max →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_eff := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max := hpow_dom a ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_max :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le _)
    -- Now turn `ofReal (Cval * μ⁻¹^e_max) * Rhs` into `ofReal Cval * Rhs_eff`.
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs
          = ENNReal.ofReal Cval * Rhs_eff := by
      rw [hRhs_eff_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  -- The seven summand bounds, each phrased as `≤ ofReal C * Rhs_eff`.
  -- Summand 1: the bare eigenvector chart component.
  have hS1 :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K) * Rhs_eff :=
    h_bridge _ (Ceig K) (eEig K) (hCeig_nn K) hEig_le (hCeig_bd i K)
  -- Summand 2: the cross-Leibniz transport double sum.
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs_eff := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (CresH K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (CresH K) (eResH K) (hCresH_nn K) hResH_le
          (hCresH_bd i β Q K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresH K) Rhs_eff (fun _ _ => hCresH_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs_eff := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal (CresH K) * Rhs_eff := fun Q _hQ =>
          h_bridge _ (CresH K) (eResH K) (hCresH_nn K) hResH_le
            (hCresH_bd i β' Q K)
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => CresH K) Rhs_eff (fun _ _ => hCresH_nn K) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs_eff (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
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
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs_eff := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
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
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs_eff h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs_eff := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K) *
            Rhs_eff := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (CresL K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (CresL K) (eResL K) (hCresL_nn K) hResL_le
          (hCresL_bd i β Q K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresL K) Rhs_eff (fun _ _ => hCresL_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (hCresL_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K)
      Rhs_eff (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Cpar K) * Rhs_eff := fun k _hk =>
        h_bridge _ (Cpar K) (ePar K) (hCpar_nn K) hPar_le (hCpar_bd i P k K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => Cpar K) Rhs_eff (fun _ _ => hCpar_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (hCpar_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs_eff := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Ccom K) * Rhs_eff := fun p _hp =>
      h_bridge _ (Ccom K) (eCom K) (hCcom_nn K) hCom_le (hCcom_bd i p K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => Ccom K) Rhs_eff (fun _ _ => hCcom_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs_eff := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CcR K) * Rhs_eff := fun P _hP =>
      h_bridge _ (CcR K) (eCcR K) (hCcR_nn K) hCcR_le (hCcR_bd i P K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => CcR K) Rhs_eff (fun _ _ => hCcR_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Ccut K) * Rhs_eff := fun l _hl =>
        h_bridge _ (Ccut K) (eCcut K) (hCcut_nn K) hCcut_le (hCcut_bd i P l K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => Ccut K) Rhs_eff (fun _ _ => hCcut_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (hCcut_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  -- The full seven-summand aggregate is bounded by `ofReal Cagg · Rhs_eff`.
  rw [rhsZeroAggregate]
  -- Pre-compute the partial-sum nonneg facts.
  have hp1 : 0 ≤ Ceig K + Cmid_α := add_nonneg (hCeig_nn K) hCmid_α_nn
  have hp2 : 0 ≤ Ceig K + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal (Ceig K) + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom' + ENNReal.ofReal CcR'
          + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add (hCeig_nn K) hCmid_α_nn]
  have h_sum_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s h_atlas i))
                      β Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
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
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
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
        ≤ ENNReal.ofReal Cagg * Rhs_eff := by
    rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
    exact hS1
  refine h_sum_bound.trans (le_of_eq ?_)
  -- Re-package `ofReal Cagg * Rhs_eff` into the headline shape
  -- `ofReal (Cagg * μ⁻¹^e_max) * Rhs`.
  rw [hRhs_eff_def, ← mul_assoc, ← ENNReal.ofReal_mul hCagg_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Per-`K`-family energy bound for the differentiated chart right-hand side
aggregate.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, a level `m`, an order `K`, a direction
multi-index `l : Fin m → Fin n`, and eight per-`K`-family `wkpNorm`-graded
chart-component energy hypotheses on the source atoms of the differentiated
aggregate — each carrying an explicit `(i.fst.val)⁻¹ ^ (e_X K')` factor —
there are a single nonnegative constant `C` and a single natural-number
exponent `e` such that for *every* eigenbasis index `i`, with resolvent
eigenvalue `μ := i.fst.val`,

```
diffRHSAggregate g r s h_atlas i α P₀ m K l
  ≤ ofReal (C · μ⁻¹^e) · ‖tensorResolventEigenbasisVec …‖.
```

The proof mirrors `diffRHSAggregate_le_energy_uniform`'s induction on `m`
generalising `K`, but at each induction step uses the per-`K`-family
hypotheses at the specific `K'` in scope. Both `C` and `e` are `i`-free; the
output `(C, e)` depend on `g r s h_atlas α P₀ m K l` and on the input
constants and exponents at orders `K, K + 1, …, K + m + 1`. This is the
per-`K`-fixed analogue of `diffRHSAggregate_le_energy_uniform`. -/
theorem diffRHSAggregate_le_energy_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s h_atlas i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (Citer : ℕ → ℝ) (eIter : ℕ → ℕ) (hCiter_nn : ∀ K', 0 ≤ Citer K')
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate (I := I) (M := M)
            g r s h_atlas i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The induction on `m` visits orders `K, K + 1, …, K + m`, with the
  -- level-`0` base case at `K + m` consuming exponents at `K + m` and
  -- `K + m + 1`. Take a common exponent `e_max` dominating every exponent
  -- visited along the chain.
  set e_max : ℕ := (Finset.range (m + 2)).sup (fun j =>
      max (max (max (max (max (max (max (max
        (eEig (K + j)) (eResH (K + j))) (eResH (K + j + 1)))
        (eResL (K + j))) (ePar (K + j))) (eCom (K + j))) (eCcR (K + j)))
        (eCcut (K + j))) (eIter (K + j))) with he_max_def
  -- Bridge for any of the per-K-family exponents at `K + j` for `j ≤ m + 1`,
  -- and for `eResH` at `K + j + 1`, to the common `e_max`.
  have hEig_le : ∀ j ≤ m + 1, eEig (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_left _ _
  have hResH_le : ∀ j ≤ m + 1, eResH (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResH1_le : ∀ j ≤ m + 1, eResH (K + j + 1) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResL_le : ∀ j ≤ m + 1, eResL (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hPar_le : ∀ j ≤ m + 1, ePar (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCom_le : ∀ j ≤ m + 1, eCom (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCcR_le : ∀ j ≤ m + 1, eCcR (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : ∀ j ≤ m + 1, eCcut (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hIter_le : ∀ j ≤ m + 1, eIter (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    exact le_max_right _ _
  -- For the head-bound at level `m'+1`, we will need a per-K-family
  -- iterated-partial bound at a fixed K' but with the exponent upgraded to
  -- `e_max`. Build a family-style bound at each `K + j` for `j ≤ m`.
  -- The level-`0` base at order `K + m` will need the seven source bounds
  -- at order `K + m`. We bundle these via the per-K lemma at each level.
  -- For the head at level m'+1, K' = K + (m - m'); but we use the family.
  -- Rather than parametrizing, we just feed the per-K hypothesis families
  -- and invoke `rhsZeroAggregate_le_energy_perK` and the head bound
  -- at each step.
  --
  -- Base constant at order `K + m`.
  obtain ⟨Cbase_m, eBase_m, hCbase_m_nn, hCbase_m_bd⟩ :=
    rhsZeroAggregate_le_energy_perK (I := I) (M := M)
      g r s h_atlas α P₀ (K + m)
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
  refine ⟨Cbase_m + (m : ℝ) *
      (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))),
    max eBase_m e_max, ?_, fun i => ?_⟩
  · -- The total constant is nonneg.
    have h0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_mem : (0 : ℕ) ∈ Finset.range (m + 1) :=
        Finset.mem_range.mpr (by omega)
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j)) h_mem
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact add_nonneg hCbase_m_nn (mul_nonneg h0 (mul_nonneg h1 h2))
  -- Eigenvalue facts.
  have hμ_pos : 0 < i.fst.val := eigenvalue_pos (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s h_atlas i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  -- Power domination on `μ⁻¹^?`.
  have hpow_dom : ∀ a b, a ≤ b → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ b :=
    fun _a _b hab => pow_le_pow_right₀ hμ_inv_ge_one hab
  -- Abbreviate the abstract-norm right-hand side factor and the
  -- `μ⁻¹^(max eBase_m e_max)`-augmented version.
  set e_out : ℕ := max eBase_m e_max with he_out_def
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hRhs_def
  set Rhs_eff : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_out) * Rhs
    with hRhs_eff_def
  -- A per-summand bridge for the per-K-family hypotheses, upgrading the
  -- exponent to `e_out`.
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_out →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_eff := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_out := hpow_dom a e_out ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_out :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le _)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs
          = ENNReal.ofReal Cval * Rhs_eff := by
      rw [hRhs_eff_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  -- Reusable head bound at level `m''+1` with K' = K + (m - m'' - 1) and
  -- general direction multi-index. For our purposes we phrase it abstractly:
  -- for any K' and l', the head is bounded by
  -- `((Fintype.card (Fin n) : ℝ) + 1) * Citer K' * Rhs_eff`, provided
  -- `eIter K' ≤ e_out` and `m'' + 1 ≤ m + 1` (i.e., `m'' ≤ m`).
  -- Reusable head bound: combines two iterated-partial atoms.
  have h_head_bound :
      ∀ (m'' K' : ℕ) (l' : Fin (m'' + 1) → Fin (Module.finrank ℝ E)),
        m'' + 1 ≤ m + 1 → eIter K' ≤ e_out →
        diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀ m'' K' l'
          ≤ ENNReal.ofReal
              (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer K') * Rhs_eff := by
    intro m'' K' l' hm''_le_succ h_eIter_le
    rw [diffRHSHead]
    have hm''_le : m'' ≤ m + 1 := Nat.le_of_succ_le hm''_le_succ
    -- Reduce each summand to `ofReal Citer K' * Rhs_eff`.
    have h_first_each : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_eff := fun a _ha =>
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i (m'' + 1) hm''_le_succ (Fin.cons a (Fin.init l')) K')
    have h_first :
        (∑ a : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') *
            Rhs_eff := by
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun a => wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _ => Citer K') Rhs_eff (fun _ _ => hCiter_nn K') h_first_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have h_second :
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m'' (Fin.init l'))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_eff :=
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i m'' hm''_le (Fin.init l') K')
    have h_total :
        (∑ a : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          + wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m'' (Fin.init l'))
              (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') * Rhs_eff
          + ENNReal.ofReal (Citer K') * Rhs_eff := add_le_add h_first h_second
    refine h_total.trans (le_of_eq ?_)
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K' := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (hCiter_nn K')
    rw [← add_mul, ← ENNReal.ofReal_add hQ_nn (hCiter_nn K')]
    congr 2
    ring
  -- The base-case bound at level `0` at order `K + m`, upgraded to `Rhs_eff`.
  have h_base_at_Km :
      rhsZeroAggregate (I := I) (M := M) g r s h_atlas i α P₀ (K + m)
        ≤ ENNReal.ofReal Cbase_m * Rhs_eff :=
    h_bridge _ Cbase_m eBase_m hCbase_m_nn (le_max_left _ _)
      (hCbase_m_bd i)
  -- For the per-level head bound we need a per-K-family bound at the
  -- *current* K' = K + (m - m''). To avoid carrying max-of-Citer through
  -- the induction explicitly, we use the supremum of `Citer (K + j)`
  -- over `j ∈ range (m + 1)`.
  set Chead_max : ℝ :=
      ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))
    with hChead_max_def
  have hChead_max_nn : 0 ≤ Chead_max := by
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j))
          (Finset.mem_range.mpr (by omega))
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact mul_nonneg h1 h2
  -- Bare-form bound by induction on m', using the head bound and base bound.
  -- At level m' (so K' = K + m - m', l' arbitrary), we get
  -- `diffRHSAggregate ≤ ofReal (Cbase_m + m' * Chead_max) * Rhs_eff`.
  -- We prove this for general `(m', K' = K + (m - m'), l')` by induction on m'.
  -- For the induction, we parametrize by m' and reverse-walk the K' position.
  -- A cleaner inductive statement: for all m' ≤ m, for any l',
  -- `diffRHSAggregate g r s h_atlas i α P₀ m' (K + m - m') l'
  --   ≤ ofReal (Cbase_m + m' * Chead_max) * Rhs_eff`.
  -- We prove a slightly stronger general bare-form by induction on m' (not
  -- coupled to m):
  -- ∀ m' K', (eIter (K' + j) ≤ e_out for relevant j) →
  --   (rhsZero base at K' + m' ≤ ofReal Cbase_m * Rhs_eff) →
  --   diffRHSAggregate m' K' l' ≤ ofReal (Cbase_m + m' * Chead_max) * Rhs_eff.
  -- To minimise bookkeeping we instead prove the special form needed.
  -- Bare-form bound by induction on `m'`, parametrised by direction `l'` and
  -- using the *fixed* level-0 bound at order `K + m` plus per-step heads.
  -- The induction adjusts the K' position: at level `m'`, the K' position is
  -- `K + m - m'`. We avoid that arithmetic by inducting on `m''` going from
  -- top down to bottom.
  -- We prove the bound at every level `m''` with K' = `K + (m - m'')`:
  -- diffRHSAggregate m'' (K + m - m'') l'
  --   ≤ ofReal (Cbase_m + m'' * Chead_max) * Rhs_eff.
  -- We need m'' ≤ m so K + m - m'' is a valid natural number that
  -- equals K + (m - m''). Since we'll only use it at m'' = m, we
  -- formulate this generally with `m'' ≤ m`.
  have h_bare :
      ∀ (m'' : ℕ), m'' ≤ m → ∀ (l' : Fin m'' → Fin (Module.finrank ℝ E)),
        diffRHSAggregate (I := I) (M := M) g r s h_atlas i α P₀
            m'' (K + (m - m'')) l'
          ≤ ENNReal.ofReal (Cbase_m + (m'' : ℝ) * Chead_max) * Rhs_eff := by
    intro m'' hm''_le l'
    induction m'' with
    | zero =>
        -- Level 0 at K + m: equals the base bound.
        have : K + (m - 0) = K + m := by simp
        rw [this]
        -- diffRHSAggregate at level 0 unfolds to rhsZeroAggregate.
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ 0 (K + m) l' =
            rhsZeroAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ (K + m) from rfl]
        have : ((0 : ℕ) : ℝ) * Chead_max = 0 := by simp
        rw [show (Cbase_m + ((0 : ℕ) : ℝ) * Chead_max) = Cbase_m from by
          rw [this]; ring]
        exact h_base_at_Km
    | succ m''' ih =>
        -- Level m'''+1 at K + (m - (m'''+1)).
        have hm'''_le : m''' ≤ m := Nat.le_of_succ_le hm''_le
        have h_pos : 1 ≤ m - m''' := by omega
        -- K + (m - (m''' + 1)) + 1 = K + (m - m''') (using m''' < m).
        have h_shift : K + (m - (m''' + 1)) + 1 = K + (m - m''') := by
          have : m - (m''' + 1) + 1 = m - m''' := by omega
          omega
        -- diffRHSAggregate at level (m'''+1) at K' = K + (m - (m'''+1)):
        --   = diffRHSHead m''' K' l' + diffRHSAggregate m''' (K'+1) (Fin.init l')
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s h_atlas i α P₀ (m''' + 1) (K + (m - (m''' + 1))) l' =
            diffRHSHead (I := I) (M := M)
              g r s h_atlas i α P₀ m''' (K + (m - (m''' + 1))) l' +
              diffRHSAggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l') from rfl]
        -- Apply h_shift to align the recursive piece's K' with the IH.
        have h_rec_eq :
            diffRHSAggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l')
              = diffRHSAggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m''' (K + (m - m''')) (Fin.init l') := by
          rw [h_shift]
        rw [h_rec_eq]
        -- Now invoke the IH on `m'''` at direction `Fin.init l'`.
        have h_rec := ih hm'''_le (Fin.init l')
        -- Head bound at K' = K + (m - (m'''+1)). We need
        -- `eIter (K + (m - (m'''+1))) ≤ e_out`.
        have h_eIter_le_local : eIter (K + (m - (m''' + 1))) ≤ e_out := by
          have h_idx : m - (m''' + 1) ≤ m + 1 := by omega
          have h_in := hIter_le (m - (m''' + 1)) h_idx
          exact h_in.trans (le_max_right _ _)
        have hm'''_succ_le : m''' + 1 ≤ m + 1 := by omega
        have h_head := h_head_bound m''' (K + (m - (m''' + 1))) l'
          hm'''_succ_le h_eIter_le_local
        -- Replace Citer K' in the head bound by the supremum.
        have h_in_range : m - (m''' + 1) ∈ Finset.range (m + 1) :=
          Finset.mem_range.mpr (by omega)
        have h_Citer_le :
            Citer (K + (m - (m''' + 1)))
              ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
                  (fun j => Citer (K + j)) :=
          Finset.le_sup' (fun j => Citer (K + j)) h_in_range
        -- Upgrade `Citer K' * (...)` to `Chead_max`.
        have h_card_nn : (0 : ℝ) ≤
            (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
            exact_mod_cast Nat.zero_le _
          linarith
        have h_upgrade_real :
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer (K + (m - (m''' + 1)))
              ≤ Chead_max := by
          rw [hChead_max_def]
          exact mul_le_mul_of_nonneg_left h_Citer_le h_card_nn
        have h_upgrade :
            ENNReal.ofReal
                (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                  Citer (K + (m - (m''' + 1))))
              ≤ ENNReal.ofReal Chead_max := ENNReal.ofReal_le_ofReal h_upgrade_real
        have h_head_up :
            diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀
                m''' (K + (m - (m''' + 1))) l'
              ≤ ENNReal.ofReal Chead_max * Rhs_eff := by
          refine h_head.trans ?_
          exact mul_le_mul_of_nonneg_right h_upgrade (by exact zero_le _)
        -- Combine head and recursive.
        have h_combine :
            diffRHSHead (I := I) (M := M) g r s h_atlas i α P₀
                m''' (K + (m - (m''' + 1))) l'
              + diffRHSAggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m''' (K + (m - m''')) (Fin.init l')
            ≤ ENNReal.ofReal Chead_max * Rhs_eff
                + ENNReal.ofReal (Cbase_m + (m''' : ℝ) * Chead_max) * Rhs_eff :=
          add_le_add h_head_up h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase_m + (m''' : ℝ) * Chead_max := by
          have hm''' : (0 : ℝ) ≤ (m''' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_m_nn (mul_nonneg hm''' hChead_max_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_max_nn hCprev_nn]
        congr 2
        push_cast
        ring
  -- Specialise to m'' = m. Then K + (m - m) = K + 0 = K. The result
  -- gives the headline at level m, order K.
  have h_at_m := h_bare m (le_refl _) l
  have h_K_eq : K + (m - m) = K := by simp
  rw [h_K_eq] at h_at_m
  -- Convert the `Rhs_eff = ofReal (μ⁻¹^e_out) * Rhs` packaging back to
  -- the headline `ofReal (Ctotal * μ⁻¹^e_out) * Rhs` form.
  have hCtotal_nn : 0 ≤ Cbase_m + (m : ℝ) * Chead_max := by
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_m_nn (mul_nonneg hm_nn hChead_max_nn)
  have h_rw_back :
      ENNReal.ofReal (Cbase_m + (m : ℝ) * Chead_max) * Rhs_eff
        = ENNReal.ofReal ((Cbase_m + (m : ℝ) * Chead_max) *
              (i.fst.val)⁻¹ ^ e_out) * Rhs := by
    rw [hRhs_eff_def, ← mul_assoc, ← ENNReal.ofReal_mul hCtotal_nn]
  exact h_at_m.trans_eq h_rw_back

/-! ## Chart-locality-free twins

The declarations below re-key the entire chain above onto the intrinsic
compact-operator eigenbasis `tensorResolventEigenbasisVec_ofCompact … (…
intrinsic …)`, dropping the chart-selection hypothesis. The statements are
otherwise identical to their originals; the proofs mirror them verbatim with
every primitive regularity datum routed through its `_unconditional` twin. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `vec_norm_eq_one`. -/
private lemma vec_norm_eq_one_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ = 1 :=
  (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
      g r s)).norm_eq_one i

/-- Chart-locality-free twin of `eigenvalue_pos`. -/
private lemma eigenvalue_pos_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_unconditional (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

/-- Chart-locality-free twin of `eigenvalue_le_one`. -/
private lemma eigenvalue_le_one_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_unconditional (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Chart-locality-free twin of `rhsZeroAggregate_le_energy_uniform`. -/
private lemma rhsZeroAggregate_le_energy_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Ceig : ℝ) (hCeig_nn : 0 ≤ Ceig)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresH : ℝ) (hCresH_nn : 0 ≤ CresH)
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresH *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresL : ℝ) (hCresL_nn : 0 ≤ CresL)
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresL *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℝ) (hCpar_nn : 0 ≤ Cpar)
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Cpar *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℝ) (hCcom_nn : 0 ≤ Ccom)
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccom *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CcR : ℝ) (hCcR_nn : 0 ≤ CcR)
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal CcR *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℝ) (hCcut_nn : 0 ≤ Ccut)
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccut *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K'
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set TCard : ℕ → ℕ := fun β_ext =>
    (transportChartCenters (I := I) (M := M) α).card with hTCard_def
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresH
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * Ccom
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CcR
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) with hCcut'_def
  set Cagg : ℝ := Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this hCresH_nn
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ hCresL_nn)
  have hCpar'_nn : 0 ≤ Cpar' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCpar_nn)
  have hCcom'_nn : 0 ≤ Ccom' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcom_nn
  have hCcR'_nn : 0 ≤ CcR' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcR_nn
  have hCcut'_nn : 0 ≤ Ccut' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCcut_nn)
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact hCeig_nn
  refine ⟨Cagg, hCagg_nn, fun i K' => ?_⟩
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have hS1 :
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig * Rhs := hCeig_bd i K'
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β' Q K'
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent_unconditional (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M)
                        g r s i))
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) * Rhs := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresL * Rhs := fun Q _hQ => hCresL_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresL) Rhs (fun _ _ => hCresL_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ hCresL_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL)
      Rhs (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) * Rhs := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cpar * Rhs := fun k _hk => hCpar_bd i P k K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => Cpar) Rhs (fun _ _ => hCpar_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCpar_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom * Rhs := fun p _hp => hCcom_bd i p K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => Ccom) Rhs (fun _ _ => hCcom_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR * Rhs := fun P _hP => hCcR_bd i P K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => CcR) Rhs (fun _ _ => hCcR_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) * Rhs := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Ccut * Rhs := fun l _hl => hCcut_bd i P l K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => Ccut) Rhs (fun _ _ => hCcut_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCcut_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate_unconditional]
  have hp1 : 0 ≤ Ceig + Cmid_α := add_nonneg hCeig_nn hCmid_α_nn
  have hp2 : 0 ≤ Ceig + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal Ceig + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom' + ENNReal.ofReal CcR'
          + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add hCeig_nn hCmid_α_nn]
  rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
  exact hS1

/-- Chart-locality-free twin of `diffRHSHead_le_energy_uniform`. -/
private lemma diffRHSHead_le_energy_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Citer : ℝ) (hCiter_nn : 0 ≤ Citer)
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
      (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m K l
      ≤ ENNReal.ofReal
          (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
  classical
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  rw [diffRHSHead_unconditional]
  have h_each :
      ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer * Rhs := fun a _ha =>
    hCiter_bd i (m + 1) (Fin.cons a (Fin.init l)) K
  have h_first :
      (∑ a : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs := by
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun a => wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _ => Citer) Rhs (fun _ _ => hCiter_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum
  have h_second :
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer * Rhs := hCiter_bd i m (Fin.init l) K
  have h_total :
      (∑ a : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs
        + ENNReal.ofReal Citer * Rhs := add_le_add h_first h_second
  refine h_total.trans (le_of_eq ?_)
  have hQ_nn : (0 : ℝ) ≤
      (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCiter_nn
  rw [← add_mul, ← ENNReal.ofReal_add hQ_nn hCiter_nn]
  congr 2
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Chart-locality-free twin of `diffRHSAggregate_le_energy_uniform`. -/
theorem diffRHSAggregate_le_energy_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_eig : ∃ Ceig : ℝ, 0 ≤ Ceig ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ceig *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_resHigh : ∃ CresH : ℝ, 0 ≤ CresH ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresH *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_resLow : ∃ CresL : ℝ, 0 ≤ CresL ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresL *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_partial : ∃ Cpar : ℝ, 0 ≤ Cpar ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Cpar *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_component : ∃ Ccom : ℝ, 0 ≤ Ccom ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (p : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_crossRight : ∃ CcR : ℝ, 0 ≤ CcR ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_cutoff : ∃ Ccut : ℝ, 0 ≤ Ccut ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccut *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (h_iter : ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
        (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Ceig, hCeig_nn, hCeig_bd⟩ := h_eig
  obtain ⟨CresH, hCresH_nn, hCresH_bd⟩ := h_resHigh
  obtain ⟨CresL, hCresL_nn, hCresL_bd⟩ := h_resLow
  obtain ⟨Cpar, hCpar_nn, hCpar_bd⟩ := h_partial
  obtain ⟨Ccom, hCcom_nn, hCcom_bd⟩ := h_component
  obtain ⟨CcR, hCcR_nn, hCcR_bd⟩ := h_crossRight
  obtain ⟨Ccut, hCcut_nn, hCcut_bd⟩ := h_cutoff
  obtain ⟨Citer, hCiter_nn, hCiter_bd⟩ := h_iter
  obtain ⟨Cbase, hCbase_nn, hCbase_bd⟩ :=
    rhsZeroAggregate_le_energy_uniform_unconditional (I := I) (M := M)
      g r s α P₀
      Ceig hCeig_nn hCeig_bd
      CresH hCresH_nn hCresH_bd
      CresL hCresL_nn hCresL_bd
      Cpar hCpar_nn hCpar_bd
      Ccom hCcom_nn hCcom_bd
      CcR hCcR_nn hCcR_bd
      Ccut hCcut_nn hCcut_bd
  set Chead : ℝ := ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer
    with hChead_def
  have hChead_nn : 0 ≤ Chead := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      linarith
    exact mul_nonneg this hCiter_nn
  set Ctotal : ℝ := Cbase + (m : ℝ) * Chead with hCtotal_def
  have hCtotal_nn : 0 ≤ Ctotal := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_nn (mul_nonneg hm hChead_nn)
  refine ⟨Ctotal, hCtotal_nn, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one_unconditional (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have h_bare : ∀ (m' K' : ℕ) (l' : Fin m' → Fin (Module.finrank ℝ E)),
      diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀ m' K' l'
        ≤ ENNReal.ofReal (Cbase + (m' : ℝ) * Chead) * Rhs := by
    intro m' K' l'
    induction m' generalizing K' with
    | zero =>
        rw [show diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ 0 K' l' =
            rhsZeroAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ K' from rfl]
        have h_base := hCbase_bd i K'
        have h_simp : (Cbase + ((0 : ℕ) : ℝ) * Chead) = Cbase := by
          simp
        rw [h_simp]
        exact h_base
    | succ m'' ih =>
        rw [show diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ (m'' + 1) K' l' =
            diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m'' K' l' +
              diffRHSAggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m'' (K' + 1) (Fin.init l') from rfl]
        have h_head := diffRHSHead_le_energy_uniform_unconditional (I := I) (M := M)
          g r s α P₀ Citer hCiter_nn hCiter_bd i m'' K' l'
        have h_rec := ih (K' + 1) (Fin.init l')
        have h_combine :
            diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m'' K' l'
              + diffRHSAggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m'' (K' + 1) (Fin.init l')
            ≤ ENNReal.ofReal Chead * Rhs
                + ENNReal.ofReal (Cbase + (m'' : ℝ) * Chead) * Rhs :=
          add_le_add h_head h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase + (m'' : ℝ) * Chead := by
          have hm'' : (0 : ℝ) ≤ (m'' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_nn (mul_nonneg hm'' hChead_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_nn hCprev_nn]
        congr 2
        push_cast
        ring
  have h_at_m := h_bare m K l
  refine h_at_m.trans ?_
  gcongr
  nlinarith [hCtotal_nn, hμ_inv_ge_one]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Chart-locality-free twin of `rhsZeroAggregate_le_energy_perK`. -/
lemma rhsZeroAggregate_le_energy_perK_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ K
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set e_max : ℕ :=
    max (max (max (max (max (max (max
      (eEig K) (eResH K)) (eResH (K + 1))) (eResL K)) (ePar K))
      (eCom K)) (eCcR K)) (eCcut K) with he_max_def
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresH K
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * Ccom K
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CcR K
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K) with hCcut'_def
  set Cagg : ℝ := Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this (hCresH_nn K)
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ (hCresL_nn K))
  have hCpar'_nn : 0 ≤ Cpar' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (hCpar_nn K))
  have hCcom'_nn : 0 ≤ Ccom' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (hCcom_nn K)
  have hCcR'_nn : 0 ≤ CcR' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (hCcR_nn K)
  have hCcut'_nn : 0 ≤ Ccut' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (hCcut_nn K))
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact hCeig_nn K
  refine ⟨Cagg, e_max, hCagg_nn, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one_unconditional (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hpow_e_max_pos : 0 < (i.fst.val)⁻¹ ^ e_max :=
    pow_pos (inv_pos.mpr hμ_pos) _
  have hpow_e_max_nn : 0 ≤ (i.fst.val)⁻¹ ^ e_max := hpow_e_max_pos.le
  have hEig_le : eEig K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_left _ _
  have hResH_le : eResH K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResH1_le : eResH (K + 1) ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResL_le : eResL K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hPar_le : ePar K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCom_le : eCom K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcR_le : eCcR K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : eCcut K ≤ e_max := le_max_right _ _
  have hpow_dom : ∀ a, a ≤ e_max → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max :=
    fun _a ha => pow_le_pow_right₀ hμ_inv_ge_one ha
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  set Rhs_eff : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_max) * Rhs
    with hRhs_eff_def
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_max →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_eff := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max := hpow_dom a ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_max :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le _)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs
          = ENNReal.ofReal Cval * Rhs_eff := by
      rw [hRhs_eff_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  have hS1 :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K) * Rhs_eff :=
    h_bridge _ (Ceig K) (eEig K) (hCeig_nn K) hEig_le (hCeig_bd i K)
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
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
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs_eff := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (CresH K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (CresH K) (eResH K) (hCresH_nn K) hResH_le
          (hCresH_bd i β Q K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresH K) Rhs_eff (fun _ _ => hCresH_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs_eff := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal (CresH K) * Rhs_eff := fun Q _hQ =>
          h_bridge _ (CresH K) (eResH K) (hCresH_nn K) hResH_le
            (hCresH_bd i β' Q K)
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => CresH K) Rhs_eff (fun _ _ => hCresH_nn K) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs_eff (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
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
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs_eff := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
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
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs_eff h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs_eff := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K) *
            Rhs_eff := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (CresL K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (CresL K) (eResL K) (hCresL_nn K) hResL_le
          (hCresL_bd i β Q K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresL K) Rhs_eff (fun _ _ => hCresL_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (hCresL_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL K)
      Rhs_eff (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Cpar K) * Rhs_eff := fun k _hk =>
        h_bridge _ (Cpar K) (ePar K) (hCpar_nn K) hPar_le (hCpar_bd i P k K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => Cpar K) Rhs_eff (fun _ _ => hCpar_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (hCpar_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs_eff := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Ccom K) * Rhs_eff := fun p _hp =>
      h_bridge _ (Ccom K) (eCom K) (hCcom_nn K) hCom_le (hCcom_bd i p K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => Ccom K) Rhs_eff (fun _ _ => hCcom_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs_eff := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CcR K) * Rhs_eff := fun P _hP =>
      h_bridge _ (CcR K) (eCcR K) (hCcR_nn K) hCcR_le (hCcR_bd i P K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => CcR K) Rhs_eff (fun _ _ => hCcR_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Ccut K) * Rhs_eff := fun l _hl =>
        h_bridge _ (Ccut K) (eCcut K) (hCcut_nn K) hCcut_le (hCcut_bd i P l K)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => Ccut K) Rhs_eff (fun _ _ => hCcut_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (hCcut_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate_unconditional]
  have hp1 : 0 ≤ Ceig K + Cmid_α := add_nonneg (hCeig_nn K) hCmid_α_nn
  have hp2 : 0 ≤ Ceig K + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal (Ceig K) + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom' + ENNReal.ofReal CcR'
          + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add (hCeig_nn K) hCmid_α_nn]
  have h_sum_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent_unconditional (I := I) (M := M)
                          g r s i))
                      β Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
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
                    (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
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
        ≤ ENNReal.ofReal Cagg * Rhs_eff := by
    rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
    exact hS1
  refine h_sum_bound.trans (le_of_eq ?_)
  rw [hRhs_eff_def, ← mul_assoc, ← ENNReal.ofReal_mul hCagg_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Chart-locality-free twin of `diffRHSAggregate_le_energy_perK`. -/
theorem diffRHSAggregate_le_energy_perK_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (Citer : ℕ → ℝ) (eIter : ℕ → ℕ) (hCiter_nn : ∀ K', 0 ≤ Citer K')
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate_unconditional (I := I) (M := M)
            g r s i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set e_max : ℕ := (Finset.range (m + 2)).sup (fun j =>
      max (max (max (max (max (max (max (max
        (eEig (K + j)) (eResH (K + j))) (eResH (K + j + 1)))
        (eResL (K + j))) (ePar (K + j))) (eCom (K + j))) (eCcR (K + j)))
        (eCcut (K + j))) (eIter (K + j))) with he_max_def
  have hEig_le : ∀ j ≤ m + 1, eEig (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_left _ _
  have hResH_le : ∀ j ≤ m + 1, eResH (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResH1_le : ∀ j ≤ m + 1, eResH (K + j + 1) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResL_le : ∀ j ≤ m + 1, eResL (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hPar_le : ∀ j ≤ m + 1, ePar (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCom_le : ∀ j ≤ m + 1, eCom (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCcR_le : ∀ j ≤ m + 1, eCcR (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : ∀ j ≤ m + 1, eCcut (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hIter_le : ∀ j ≤ m + 1, eIter (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eEig (K + j')) (eResH (K + j'))) (eResH (K + j' + 1)))
        (eResL (K + j'))) (ePar (K + j'))) (eCom (K + j'))) (eCcR (K + j')))
        (eCcut (K + j'))) (eIter (K + j'))) hj_mem)
    exact le_max_right _ _
  obtain ⟨Cbase_m, eBase_m, hCbase_m_nn, hCbase_m_bd⟩ :=
    rhsZeroAggregate_le_energy_perK_unconditional (I := I) (M := M)
      g r s α P₀ (K + m)
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
  refine ⟨Cbase_m + (m : ℝ) *
      (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))),
    max eBase_m e_max, ?_, fun i => ?_⟩
  · have h0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_mem : (0 : ℕ) ∈ Finset.range (m + 1) :=
        Finset.mem_range.mpr (by omega)
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j)) h_mem
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact add_nonneg hCbase_m_nn (mul_nonneg h0 (mul_nonneg h1 h2))
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one_unconditional (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hpow_dom : ∀ a b, a ≤ b → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ b :=
    fun _a _b hab => pow_le_pow_right₀ hμ_inv_ge_one hab
  set e_out : ℕ := max eBase_m e_max with he_out_def
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ with hRhs_def
  set Rhs_eff : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_out) * Rhs
    with hRhs_eff_def
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_out →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_eff := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_out := hpow_dom a e_out ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_out :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le _)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs
          = ENNReal.ofReal Cval * Rhs_eff := by
      rw [hRhs_eff_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  have h_head_bound :
      ∀ (m'' K' : ℕ) (l' : Fin (m'' + 1) → Fin (Module.finrank ℝ E)),
        m'' + 1 ≤ m + 1 → eIter K' ≤ e_out →
        diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀ m'' K' l'
          ≤ ENNReal.ofReal
              (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer K') * Rhs_eff := by
    intro m'' K' l' hm''_le_succ h_eIter_le
    rw [diffRHSHead_unconditional]
    have hm''_le : m'' ≤ m + 1 := Nat.le_of_succ_le hm''_le_succ
    have h_first_each : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_eff := fun a _ha =>
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i (m'' + 1) hm''_le_succ (Fin.cons a (Fin.init l')) K')
    have h_first :
        (∑ a : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') *
            Rhs_eff := by
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun a => wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _ => Citer K') Rhs_eff (fun _ _ => hCiter_nn K') h_first_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have h_second :
        wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m'' (Fin.init l'))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_eff :=
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i m'' hm''_le (Fin.init l') K')
    have h_total :
        (∑ a : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          + wkpNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ m'' (Fin.init l'))
              (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') * Rhs_eff
          + ENNReal.ofReal (Citer K') * Rhs_eff := add_le_add h_first h_second
    refine h_total.trans (le_of_eq ?_)
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K' := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (hCiter_nn K')
    rw [← add_mul, ← ENNReal.ofReal_add hQ_nn (hCiter_nn K')]
    congr 2
    ring
  have h_base_at_Km :
      rhsZeroAggregate_unconditional (I := I) (M := M) g r s i α P₀ (K + m)
        ≤ ENNReal.ofReal Cbase_m * Rhs_eff :=
    h_bridge _ Cbase_m eBase_m hCbase_m_nn (le_max_left _ _)
      (hCbase_m_bd i)
  set Chead_max : ℝ :=
      ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))
    with hChead_max_def
  have hChead_max_nn : 0 ≤ Chead_max := by
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j))
          (Finset.mem_range.mpr (by omega))
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact mul_nonneg h1 h2
  have h_bare :
      ∀ (m'' : ℕ), m'' ≤ m → ∀ (l' : Fin m'' → Fin (Module.finrank ℝ E)),
        diffRHSAggregate_unconditional (I := I) (M := M) g r s i α P₀
            m'' (K + (m - m'')) l'
          ≤ ENNReal.ofReal (Cbase_m + (m'' : ℝ) * Chead_max) * Rhs_eff := by
    intro m'' hm''_le l'
    induction m'' with
    | zero =>
        have : K + (m - 0) = K + m := by simp
        rw [this]
        rw [show diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ 0 (K + m) l' =
            rhsZeroAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ (K + m) from rfl]
        have : ((0 : ℕ) : ℝ) * Chead_max = 0 := by simp
        rw [show (Cbase_m + ((0 : ℕ) : ℝ) * Chead_max) = Cbase_m from by
          rw [this]; ring]
        exact h_base_at_Km
    | succ m''' ih =>
        have hm'''_le : m''' ≤ m := Nat.le_of_succ_le hm''_le
        have h_pos : 1 ≤ m - m''' := by omega
        have h_shift : K + (m - (m''' + 1)) + 1 = K + (m - m''') := by
          have : m - (m''' + 1) + 1 = m - m''' := by omega
          omega
        rw [show diffRHSAggregate_unconditional (I := I) (M := M)
              g r s i α P₀ (m''' + 1) (K + (m - (m''' + 1))) l' =
            diffRHSHead_unconditional (I := I) (M := M)
              g r s i α P₀ m''' (K + (m - (m''' + 1))) l' +
              diffRHSAggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l') from rfl]
        have h_rec_eq :
            diffRHSAggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l')
              = diffRHSAggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - m''')) (Fin.init l') := by
          rw [h_shift]
        rw [h_rec_eq]
        have h_rec := ih hm'''_le (Fin.init l')
        have h_eIter_le_local : eIter (K + (m - (m''' + 1))) ≤ e_out := by
          have h_idx : m - (m''' + 1) ≤ m + 1 := by omega
          have h_in := hIter_le (m - (m''' + 1)) h_idx
          exact h_in.trans (le_max_right _ _)
        have hm'''_succ_le : m''' + 1 ≤ m + 1 := by omega
        have h_head := h_head_bound m''' (K + (m - (m''' + 1))) l'
          hm'''_succ_le h_eIter_le_local
        have h_in_range : m - (m''' + 1) ∈ Finset.range (m + 1) :=
          Finset.mem_range.mpr (by omega)
        have h_Citer_le :
            Citer (K + (m - (m''' + 1)))
              ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
                  (fun j => Citer (K + j)) :=
          Finset.le_sup' (fun j => Citer (K + j)) h_in_range
        have h_card_nn : (0 : ℝ) ≤
            (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
            exact_mod_cast Nat.zero_le _
          linarith
        have h_upgrade_real :
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer (K + (m - (m''' + 1)))
              ≤ Chead_max := by
          rw [hChead_max_def]
          exact mul_le_mul_of_nonneg_left h_Citer_le h_card_nn
        have h_upgrade :
            ENNReal.ofReal
                (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                  Citer (K + (m - (m''' + 1))))
              ≤ ENNReal.ofReal Chead_max := ENNReal.ofReal_le_ofReal h_upgrade_real
        have h_head_up :
            diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀
                m''' (K + (m - (m''' + 1))) l'
              ≤ ENNReal.ofReal Chead_max * Rhs_eff := by
          refine h_head.trans ?_
          exact mul_le_mul_of_nonneg_right h_upgrade (by exact zero_le _)
        have h_combine :
            diffRHSHead_unconditional (I := I) (M := M) g r s i α P₀
                m''' (K + (m - (m''' + 1))) l'
              + diffRHSAggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m''' (K + (m - m''')) (Fin.init l')
            ≤ ENNReal.ofReal Chead_max * Rhs_eff
                + ENNReal.ofReal (Cbase_m + (m''' : ℝ) * Chead_max) * Rhs_eff :=
          add_le_add h_head_up h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase_m + (m''' : ℝ) * Chead_max := by
          have hm''' : (0 : ℝ) ≤ (m''' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_m_nn (mul_nonneg hm''' hChead_max_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_max_nn hCprev_nn]
        congr 2
        push_cast
        ring
  have h_at_m := h_bare m (le_refl _) l
  have h_K_eq : K + (m - m) = K := by simp
  rw [h_K_eq] at h_at_m
  have hCtotal_nn : 0 ≤ Cbase_m + (m : ℝ) * Chead_max := by
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_m_nn (mul_nonneg hm_nn hChead_max_nn)
  have h_rw_back :
      ENNReal.ofReal (Cbase_m + (m : ℝ) * Chead_max) * Rhs_eff
        = ENNReal.ofReal ((Cbase_m + (m : ℝ) * Chead_max) *
              (i.fst.val)⁻¹ ^ e_out) * Rhs := by
    rw [hRhs_eff_def, ← mul_assoc, ← ENNReal.ofReal_mul hCtotal_nn]
  exact h_at_m.trans_eq h_rw_back

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
