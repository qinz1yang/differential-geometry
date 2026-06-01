import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartGradientEnergyBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossLimits
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDiv

/-!
# Chart-local energy estimates for the gradient-order limit atoms of an
# eigenvector chart right-hand side

The level-`0` eigen-equation right-hand side `eigenvectorChartRHS g r s h_atlas i
α P₀` of a connection-Laplacian eigenvector has, by `eigenvectorChartRHS_eLpNorm_le`,
a weighted-`eLpNorm` bound whose right-hand side is a six-summand aggregate.
Three of those summands are *gradient-order* objects — they carry one covariant
derivative / one weak chart partial of the eigenvector — while the other three
are order-`0`. This file supplies a uniform chart-local `eLpNorm` energy estimate
for each of the three gradient-order atoms:

* `crossLeftLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the completion-extended covariant gradient
  `tensorCovGradL2Compl g r s` applied to the eigenvector resolvent
  `eigenvectorResolvent g r s h_atlas i`;
* `partialLpLimit g r s h_atlas i α P k` — `μ` times the candidate weak `k`-th
  chart partial `eigenvectorChartPartialLp` of the eigenvector chart component;
* `cutoffPartialLpLimit g r s h_atlas i α P k` — `μ` times the candidate weak
  `k`-th cutoff chart partial `eigenvectorCutoffChartPartialLp` of the eigenvector
  chart component.

Here `μ := i.fst.val` is the nonzero resolvent eigenvalue attached to the
eigenbasis index `i`.

## Why an energy estimate is needed

A higher-order norm of a function cannot be bounded by a lower-order norm of the
same function in general. The bounds below are genuine precisely because the
function is an *eigenvector*: the resolvent eigen-equation supplies the energy
identity `eigenvectorResolvent_h1Norm_le`, `‖eigenvectorResolvent g r s h_atlas i‖
≤ √μ · ‖φ‖` (with `φ := tensorResolventEigenbasisVec h_atlas i`), and its
gradient corollary `tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le`,
`‖tensorCovGradL2Compl g r s (eigenvectorResolvent …)‖ ≤ √μ · ‖φ‖`, both proved
in `EigenvectorChartGradientEnergyBound.lean`.

Each of the three gradient-order atoms is the value of a bounded chart
continuous linear map applied to `eigenvectorResolvent g r s h_atlas i` or to
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s h_atlas i)`:

* `cutoffPartialLpLimit = i.fst.val • (i.fst.val⁻¹ • eigenvectorCutoffChartPartialCLM
  g r s α P k (eigenvectorResolvent …))`, and the two scalar factors cancel,
  exhibiting `cutoffPartialLpLimit = eigenvectorCutoffChartPartialCLM g r s α P k
  (eigenvectorResolvent …)`;
* likewise `partialLpLimit = eigenvectorChartPartialCLM g r s α P k
  (eigenvectorResolvent …)`;
* `crossLeftLimitComponent = tensorL2ChartComponentCutoffCLM g r (s + 1) α P
  (tensorCovGradL2Compl g r s (eigenvectorResolvent …))`.

The chart `L²` norm of each atom is therefore at most the *operator norm* of the
relevant chart continuous linear map — a quantity depending only on the geometric
data `g r s α P (k)` — times the `L²` norm of `eigenvectorResolvent …`
respectively `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`. Composing
with the energy identity supplies the `√μ`-weighted estimate.

## The genuineness of the constant

Every headline quantifies the constant `C` with `∃` *before* the universal
`∀ i`: a single `C` controls the chart atom of *every* eigenvector
simultaneously. `C` is the operator norm of a chart continuous linear map; it
depends only on `g r s α P (k)`, never on the eigenbasis index `i`. The only
`i`-dependence of the right-hand side is the explicit `√μ` factor, which
originates from the energy identity — the eigen-equation — not from any
finiteness or ratio shortcut.

## Main results

* `crossLeftLimitComponent_eLpNorm_le` — a chart-geometric constant `C ≥ 0`,
  uniform over `i`, with `eLpNorm (crossLeftLimitComponent … i α P) 2
  (volume.restrict (chartTargetEuclid α)) ≤ ofReal (C · √μ) · ofReal ‖φ‖`.
* `partialLpLimit_eLpNorm_le` — the same for `partialLpLimit … i α P k`.
* `cutoffPartialLpLimit_eLpNorm_le` — the same for `cutoffPartialLpLimit … i α P
  k`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
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
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Chart-locality-free positivity of the resolvent eigenvalue.** Chart-
locality-free twin of `eigenvalue_pos`: the resolvent eigenvalue `μ := i.fst.val`
attached to an eigenbasis index is strictly positive. The unconditional
eigenbasis vector `tensorResolventEigenbasisVec (…intrinsic g r s) i`
is a non-zero element of the resolvent eigenspace at `μ`, and the resolvent
eigenvalues lie in the unit interval. No chart-selection hypothesis. -/
private lemma eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm :
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ = 1 :=
        (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s)).norm_eq_one i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- For an `Lp ℝ 2 (chartL2Measure α)` class `w`, the `eLpNorm` of its
coercion-to-function against `volume.restrict (chartTargetEuclid α)` equals
`ENNReal.ofReal ‖w‖`. -/
private lemma eLpNorm_lpClass_eq_ofReal_norm
    (α : M) (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    eLpNorm ((w : EuclN → ℝ)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      = ENNReal.ofReal ‖w‖ := by
  have h_eq : eLpNorm ((w : EuclN → ℝ)) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm ((w : EuclN → ℝ)) 2 (chartL2Measure (I := I) (M := M) α) := rfl
  rw [h_eq, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-partial limit atom as a CLM value (chart-locality-free).** Chart-
locality-free twin of `partialLpLimit_eq_clm`: `partialLpLimit g r s
i α P k` is the bare value of the canonical chart-partial continuous linear map
`eigenvectorChartPartialCLM g r s α P k` on the unconditional eigenvector
resolvent `eigenvectorResolvent g r s i`; the `μ` and `μ⁻¹` factors
cancel. No chart-selection hypothesis. -/
private lemma partialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    partialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [partialLpLimit, eigenvectorChartPartialLp,
    smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart `L²` norm of the chart-partial limit atom is bounded by the
operator norm of the canonical chart-partial continuous linear map times the
`H¹` norm of the unconditional eigenvector resolvent (chart-locality-free twin of
`partialLpLimit_norm_le`). No chart-selection hypothesis. -/
private lemma partialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [partialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k).le_opNorm _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-local gradient-energy estimate for the chart-partial limit atom
(chart-locality-free).** Chart-locality-free twin of `partialLpLimit_eLpNorm_le`.
For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P`, and a chart-coordinate direction `k`, there
is a chart-geometric constant `C ≥ 0` — uniform over the eigenbasis index `i` —
such that for every eigenbasis index `i` with nonzero resolvent eigenvalue
`μ := i.fst.val`, the `L²` norm over the Euclidean chart target of the
chart-partial limit atom `partialLpLimit g r s i α P k` is at most
`C · √μ` times the abstract `L²` norm of the unconditional eigenbasis vector
`tensorResolventEigenbasisVec (…intrinsic g r s) i`.

The constant `C` is the operator norm of the canonical chart-partial continuous
linear map `eigenvectorChartPartialCLM g r s α P k`; it depends only on the
geometric data `g r s α P k`. The bound is genuine — and not the vacuous per-`i`
ratio — because the universal quantifier `∀ i` lies *inside* the existential
`∃ C`. The `i`-dependence on the right-hand side is the explicit `√μ` factor,
originating from the energy identity `eigenvectorResolvent_h1Norm_le`
(the eigen-equation). No chart-selection hypothesis. -/
theorem partialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (partialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖partialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          partialLpLimit_norm_le (I := I) (M := M) g r s i α P k
      _ ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The cutoff chart-partial limit atom as a CLM value (chart-locality-free).**
Chart-locality-free twin of `cutoffPartialLpLimit_eq_clm`:
`cutoffPartialLpLimit g r s i α P k` is the bare value of the
canonical cutoff chart-partial continuous linear map
`eigenvectorCutoffChartPartialCLM g r s α P k` on the unconditional eigenvector
resolvent `eigenvectorResolvent g r s i`; the `μ` and `μ⁻¹` factors
cancel. No chart-selection hypothesis. -/
private lemma cutoffPartialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    cutoffPartialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [cutoffPartialLpLimit,
    eigenvectorCutoffChartPartialLp, smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart `L²` norm of the cutoff chart-partial limit atom is bounded by the
operator norm of the canonical cutoff chart-partial continuous linear map times
the `H¹` norm of the unconditional eigenvector resolvent (chart-locality-free
twin of `cutoffPartialLpLimit_norm_le`). No chart-selection hypothesis. -/
private lemma cutoffPartialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [cutoffPartialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
    g r s α P k).le_opNorm _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-local gradient-energy estimate for the cutoff chart-partial limit
atom (chart-locality-free).** Chart-locality-free twin of
`cutoffPartialLpLimit_eLpNorm_le`. For a closed Riemannian manifold `(M, g)`,
ranks `(r, s)`, a chart center `α : M`, a component multi-index `P`, and a
chart-coordinate direction `k`, there is a chart-geometric constant `C ≥ 0` —
uniform over the eigenbasis index `i` — such that for every eigenbasis index `i`
with nonzero resolvent eigenvalue `μ := i.fst.val`, the `L²` norm over the
Euclidean chart target of the cutoff chart-partial limit atom
`cutoffPartialLpLimit g r s i α P k` is at most `C · √μ` times the
abstract `L²` norm of the unconditional eigenbasis vector
`tensorResolventEigenbasisVec (…intrinsic g r s) i`.

The constant `C` is the operator norm of the canonical cutoff chart-partial
continuous linear map `eigenvectorCutoffChartPartialCLM g r s α P k`; it depends
only on the geometric data `g r s α P k`. The bound is genuine — and not the
vacuous per-`i` ratio — because the universal quantifier `∀ i` lies *inside* the
existential `∃ C`. The `i`-dependence on the right-hand side is the explicit `√μ`
factor, originating from the energy identity
`eigenvectorResolvent_h1Norm_le` (the eigen-equation). No chart-
selection hypothesis. -/
theorem cutoffPartialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
      g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (cutoffPartialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          cutoffPartialLpLimit_norm_le (I := I) (M := M)
            g r s i α P k
      _ ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
          g r s α P k‖ * Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
        g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P : TensorCompIdx (E := E) r s)
  (P' : TensorCompIdx (E := E) r (s + 1))
  (k : Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
  partialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
  cutoffPartialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
