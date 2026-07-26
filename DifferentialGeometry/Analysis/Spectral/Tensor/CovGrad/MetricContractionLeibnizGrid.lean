import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

/-! # The abstract `rfns` covariant-Leibniz grid for a differentiated bilinear contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the curvature file `CurvatureContractionLeibnizGridConstruction` builds, for
the *specific* Riemann curvature contraction `R(X, Y)·`, the intrinsic `riemannianFiberNormSq`
(`rfns`) binomial covariant-Leibniz grid
```
rfns(∇^j(R(X, Y) Z))(x) ≤ 4^j · ∑_{p ≤ j} kappa p · ∑_{q ≤ j} rfns(∇^q Z)(x),
```
through the recursive differentiated-curvature operators `diffCurvOp p` (the exact covariant-Leibniz
remainders) and their per-order section-proportional fibre envelope `kappa p`.

This file **liberates that construction to its abstract form** (R7 — extend, do not duplicate): a
generic *fibrewise-linear, non-parallel, recursively-differentiated* bilinear contraction operator,
packaged as `DiffBilinOp`, with the *same* recursive Leibniz-remainder structure but no curvature
specifics.  The genuine constraints — the exact single-step covariant Leibniz of the family
(`covGrad_op`, the non-parallel rule `∇(D_p W) = D_{p+1} W + D_p(∇W)`) and the per-order
section-proportional fibre envelope (`rfns_op_le`) — are the structure *fields*, the genuine
mathematical inputs a working geometer supplies (exactly as `ParallelTensorProduct`'s fields are).
From them the `rfns` binomial grid is **proved outright** by the same binomial covariant-Leibniz
induction the curvature file uses, with **no posit of its own**.

This is the engine the covariant Faà-di-Bruno expansion of the second-order Ricci–DeTurck right-hand
side needs for its metric-built fields (`ricciTensor(g_t)`, the inverse-metric Neumann factor, the
`deTurckVF` Christoffel difference): each is a fibrewise-linear contraction of the metric jet against
the perturbation, non-parallel, with a bounded per-order envelope on the supercritical `H^{a+2}`
family — exactly a `DiffBilinOp`.

## Main definitions

* `DiffBilinOp g r₀ s₀` — a differentiated fibrewise-linear bilinear contraction operator family: a
  section-level operator `op p` at every differentiation order `p` and base width, satisfying the
  exact recursive covariant Leibniz (`covGrad_op`) and a per-order base-point-uniform proportional
  fibre envelope (`kappa`, `rfns_op_le`).

## Main results

* `DiffBilinOp.rfns_iteratedCovGrad_grid` — the binomial covariant-Leibniz `rfns` double grid
  `rfns(∇^j(op 0 W))(x) ≤ 4^j · ∑_{p ≤ j} kappa(p) · ∑_{q ≤ j} rfns(∇^q W)(x)`, proved by induction.
* `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` — its single-sum collapse
  `rfns(∇^j(op 0 W))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q W)(x)`, the shape the order-`m` jet induction and
  the intrinsic Moser-tame product consume. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

section RankCast

set_option linter.unusedSectionVars false in
/-- **Heterogeneous rank-congruence for `covGrad`.** If `h : a = b`, then `covGrad g r a Y` and
`covGrad g r b Z` are heterogeneously equal whenever `Y, Z` are. -/
private theorem covGrad_heq_congr_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** -/
private theorem iteratedCovGrad_covGrad_comm_heq_db (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero => rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]; exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_db g r (by omega : (s + 1) + k = s + (k + 1)) ih

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast.** -/
private theorem rfns_toSection_heq_congr_db (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The
intrinsic squared fibre norm of `∇^m(∇W)` at `x` equals that of `∇^{m+1}W`. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_db (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_db g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq_db g r s m W) x

/-- The rank-cast of a smooth compactly-supported tensor along a `Nat` equality of covariant ranks. -/
def castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ W

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [CompleteSpace E] in
/-- A covariant-rank cast preserves the intrinsic norm of a smooth tensor. -/
@[simp] theorem norm_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) :
    ‖castRankCc_db g r h W‖ = ‖W‖ := by
  subst h
  rfl

set_option linter.unusedSectionVars false in
/-- **The iterated-gradient `rfns` is invariant under the rank-cast `castRankCc_db`.** -/
theorem rfns_iteratedCovGrad_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (b + j) x
        ((iteratedCovGrad g r b j (castRankCc_db g r h W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (a + j) x
        ((iteratedCovGrad g r a j W).toSection x) := by
  subst h; rfl

/-- Two `range`-sum bookkeeping helpers (shift / truncate), used in the grid induction. -/
private lemma sum_range_shift_le_db (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

private lemma sum_range_le_succ_of_nonneg_db (n : ℕ) (f : ℕ → ℝ) (hlast : 0 ≤ f n) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right hlast

/-- **The order × rank window grid coefficient.** For a nonnegative two-index family `κ : ℕ → ℕ → ℝ`
(differentiation order, covariant rank), the differentiation-order `p`, base rank `r`, gradient-order
`j` window sum `∑_{p' < j+1} ∑_{r' < j+1} κ(p + p')(r + r')` — the double sum over the order window
`[p, p + j]` and the rank window `[r, r + j]` the covariant-Leibniz recursion of a *rank-climbing*
differentiated operator climbs (each gradient step advances either the order by one, keeping the rank,
or the rank by one, keeping the base order, so at gradient order `j` the leaves reach orders `≤ p + j`
and ranks `≤ r + j`). It replaces the order-only `∑_{p'} κ(p + p')` of a rank-uniform envelope: the
rank-`r` curvature derivation's fibre-operator constant grows with `r`, so no single order-only family
covers all ranks. -/
def gridWindowSum (κ : ℕ → ℕ → ℝ) (p r j : ℕ) : ℝ :=
  ∑ p' ∈ Finset.range (j + 1), ∑ r' ∈ Finset.range (j + 1), κ (p + p') (r + r')

theorem gridWindowSum_nonneg {κ : ℕ → ℕ → ℝ} (hκ : ∀ p r, 0 ≤ κ p r) (p r j : ℕ) :
    0 ≤ gridWindowSum κ p r j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hκ _ _

/-- The width-`0` order × rank window sum is the single coefficient `κ p r`. -/
theorem gridWindowSum_zero (κ : ℕ → ℕ → ℝ) (p r : ℕ) :
    gridWindowSum κ p r 0 = κ p r := by
  simp [gridWindowSum]

/-- **The shifted order × rank window is a sub-window of the one-larger window.** For nonnegative `κ`,
shifting the base order by `dp ≤ 1` and the base rank by `dr ≤ 1` and summing over the order × rank
window of width `j + 1` is dominated by the width-`(j + 2)` window at the unshifted base — the shifted
`(j + 1) × (j + 1)` grid sits inside the `(j + 2) × (j + 2)` grid, all summands nonnegative. This is
the monotonicity that dominates each covariant-Leibniz piece (the order-advanced `op (p + 1)` at the
same rank, and the rank-advanced `op p` on `∇W`) by the common one-larger window. -/
theorem gridWindowSum_shift_le {κ : ℕ → ℕ → ℝ} (hκ : ∀ p r, 0 ≤ κ p r)
    (p r j dp dr : ℕ) (hdp : dp ≤ 1) (hdr : dr ≤ 1) :
    gridWindowSum κ (p + dp) (r + dr) j ≤ gridWindowSum κ p r (j + 1) := by
  classical
  unfold gridWindowSum
  rw [← Finset.sum_product', ← Finset.sum_product']
  set f : ℕ × ℕ → ℝ := fun b => κ (p + b.1) (r + b.2) with hf_def

  have hshift : ∑ b ∈ (Finset.range (j + 1) ×ˢ Finset.range (j + 1)),
        κ ((p + dp) + b.1) ((r + dr) + b.2) =
      ∑ b ∈ ((Finset.range (j + 1) ×ˢ Finset.range (j + 1)).image
        (fun b : ℕ × ℕ => (dp + b.1, dr + b.2))), f b := by
    rw [Finset.sum_image (by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (by omega) (by omega))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hf_def]
    congr 1 <;> omega
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hκ _ _)
  intro a ha
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at ha
  obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := ha
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, by omega⟩

end RankCast

/-- **A differentiated fibrewise-linear bilinear contraction operator family.**

The genuine abstraction realized by a non-parallel metric contraction of the metric jet against a
varying tensor section (the structure of every nonlinear term `g⁻¹ · ∂g · ∂g`, `g⁻¹ · ∂²g`,
`R(X, Y)·` in the covariant Faà-di-Bruno expansion).  The family `op p` is the `p`-times covariantly
differentiated operator (a smooth compactly-supported `(0, r + p)`-tensor at each rank `r`,
fibrewise-`ℝ`-linear in the contracted section), with two genuine `∇`-compatibility / boundedness
fields:

* `covGrad_op` — the **exact recursive single-step covariant Leibniz** `∇(op p r W) = op (p+1) r W +
  (rank-cast) op p (r+1) (∇W)` (the operator is *not* parallel, so the differentiated-operator cross
  term `op (p+1)` survives; the right summand carries covariant rank `(r+1)+p`, rank-cast to the
  differentiated rank `(r+p)+1`).  This is the defining identity of the recursive Leibniz-remainder
  construction of the differentiated operators.
* `kappa`, `kappa_nonneg`, `rfns_op_le` — the **per-order base-point-uniform proportional fibre
  envelope in *jet* form** `rfns(op p r W)(x) ≤ kappa p r · ∑_{q < p + 1} rfns(∇^q W)(x)`, the
  boundedness of the smooth fixed operator on the compact manifold against the order-`≤ p` covariant
  jet of the contracted section, uniform over the section.

**Why the jet form (and not the single-value form `rfns(op p r W)(x) ≤ kappa p r · rfns(W)(x)`).**  The
single-value envelope is **Lean-refuted FALSE** at the rank-`0`-degenerate bases of the curvature
towers.  The order-`0` curvature contraction is value-local *per rank* but its rank-`0` value vanishes
(`riemannSec_tensor0SCov_zero_eq_zero`, the scalar curvature is zero), so `op 0 0 = 0`; the recursion
then forces `op 1 0 W = ∇(op 0 0 W) − (cast)(op 0 1 (∇W)) = −(cast)(op 0 1 (∇W))`, which reads the
*gradient* `∇W (x)` (not the value `W (x)`).  On a non-flat manifold, an `W` with `W (x) = 0`,
`∇W (x) ≠ 0` breaks `rfns(op 1 0 W)(x) ≤ kappa 1 0 · rfns(W)(x) = 0`.  Structurally the recursion
subtracts the *full* rank-`(r+1)` operator on `∇W`, while the genuine Leibniz spectator is the
slot-extended rank-`r` operator; the difference acts on the gradient slot — an irreducible one-jet term
at every step.  The honest invariant the recursion *does* satisfy is the jet bound: `op p r W (x)`
reads up to `∇^p W (x)`, so it is controlled by the order-`≤ p` jet `∑_{q < p + 1} rfns(∇^q W)(x)`.  The
downstream consumers (the iterated grid `rfns_iteratedCovGrad_grid`, whose own conclusion is the jet sum
`∑_q rfns(∇^q W)`) only ever need the jet shape; the single-value form was an over-strong intermediate.

These are genuine mathematical inputs (the consumer constructs `op` and discharges the two fields);
the structure is kept generic and decoupled from any specific nonlinearity as a reusable
covariant-calculus byproduct.  A degenerate `kappa ≡ 0` witness is rejected whenever `op 0 r W ≠ 0`
(then at `p = 0` the jet RHS is `kappa 0 r · rfns(W)(x) = 0` while `rfns(op 0 r W)(x) > 0`), so the
envelope genuinely uses the section; at the rank-`0`-degenerate base, `op 1 0 W = −cast(op 0 1 (∇W))`
is genuinely nonzero on a non-flat `M` with the jet RHS `kappa 1 0 · (rfns(W) + rfns(∇W))(x)` positive,
so it is not vacuous. -/
structure DiffBilinOp (g : SmoothRiemannianMetric I M) where

  op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)

  covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
    covGrad g 0 (r + p) (op p r W) =
      op (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W))

  kappa : ℕ → ℕ → ℝ

  kappa_nonneg : ∀ p r, 0 ≤ kappa p r

  rfns_op_le : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
      kappa p r * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x)

namespace DiffBilinOp

variable {g : SmoothRiemannianMetric I M}

/-- **The binomial covariant-Leibniz `rfns` double grid for a differentiated bilinear contraction.**

For every gradient order `j`, every differentiation order `p`, every base rank `r`, every section
`W`, and every point `x`, the intrinsic squared fibre norm of `∇^j(op p r W)` is bounded by the
binomial **jet** grid
```
rfns(∇^j(op p r W))(x) ≤ 4^j · ∑_{p' ≤ j} kappa(p + p') · ∑_{q < p + j + 1} rfns(∇^q W)(x),
```
the differentiated operator entering only as the base-point-uniform coefficient `kappa(p + p')` and
only the gradient order `q` of the contracted section surviving as a fibre-norm jet grid; the `4^j`
absorbs the binomial coefficients of the exact covariant Leibniz expansion.  The contracted-jet window
is `q < p + j + 1`: the order-`p` operator reads up to `∇^p W` (the jet field `rfns_op_le`), and each
of the `j` gradient steps can advance the read order by one, so the leaves reach `∇^{p + j} W`.  At the
consumer entry `p = 0` the window collapses to `q < j + 1` (only `∇^{≤ j} W` is read).

Proved by induction on `j`: the base case is the per-order **jet** envelope `rfns_op_le` (window
`q < p + 1`); the successor step front-commutes the innermost gradient
(`rfns_iteratedCovGrad_covGrad_comm_db`), expands the single covariant gradient by the exact recursive
Leibniz `covGrad_op`, distributes `∇^j` over the sum (`iteratedCovGrad_add`,
`riemannianFiberNormSq_add_le`), recurses on the two shifted pieces (the order-advanced `op (p + 1)`
with window `q < (p + 1) + j + 1`, equal to the target, and the rank-advanced `op p` on `∇W` with the
shifted window `q < p + j + 1` of `∇^{q+1} W ⊆ ∇^{≤ p + j + 1} W`), and dominates them by the common
target window `range (p + (j + 1) + 1)`, the two copies combining into the `4^{j+1}` factor.  No posit
(the curvature file's `rfns_iteratedCovGrad_diffCurvOp_grid` is the `R(X, Y)·` instance of this
proof). -/
theorem rfns_iteratedCovGrad_grid (Φ : DiffBilinOp g) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x
          ((iteratedCovGrad g 0 (r + p) j (Φ.op p r W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum Φ.kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum Φ.kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          Φ.kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact Φ.rfns_op_le p r W x
  | succ j ih =>
      intro p r W x
      set K : ℝ := gridWindowSum Φ.kappa p r (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg Φ.kappa_nonneg p r (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + p) (j + 1) (Φ.op p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad g 0 (r + p) (Φ.op p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_db g 0 (r + p) j (Φ.op p r W) x).symm]
      rw [Φ.covGrad_op p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + p) + 1) j (Φ.op (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
              (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum Φ.kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum Φ.kappa p (r + 1) j with hkB_def

      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def

      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j (Φ.op (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad g 0 r W) x
      have hBshift : gridWindowSum Φ.kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_db g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le Φ.kappa_nonneg p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le Φ.kappa_nonneg p r j 0 1 (Nat.zero_le _) le_rfl

      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))

      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_db (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg Φ.kappa_nonneg (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg Φ.kappa_nonneg p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _
      have hprodA : kA * sA ≤ K * S := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * S := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * S) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * S) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum Φ.kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
                (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (Φ.op p (r + 1) (covGrad g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-- **The single-sum collapse of the differentiated-operator `rfns` grid.**

Assembling the binomial grid `rfns_iteratedCovGrad_grid` at differentiation order `p = 0` (where
`op 0 r W` is the undifferentiated contraction): there is a single nonnegative order-dependent
constant `C : ℕ → ℝ` such that for every gradient order `j`, base rank `r`, section `W`, and point
`x`,
```
rfns(∇^j(op 0 r W))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q W)(x).
```
The `p'`-double-sum collapses to a single per-rank, per-order constant; because the
differentiated-operator coefficients are base-point-uniform (but rank-dependent), the constant is
`C r j := 4^j · gridWindowSum kappa 0 r j`, the `4^j`-scaled order × rank window sum over the
order window `[0, j]` and rank window `[r, r + j]` the recursion climbs.  This is the exact shape the
order-`m` jet induction and the intrinsic Moser-tame product
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le` consume.  Proved from the grid by `mul_assoc`. -/
theorem exists_rfns_iteratedCovGrad_singleSum_le (Φ : DiffBilinOp g) :
    ∃ C : ℕ → ℕ → ℝ, (∀ r j, 0 ≤ C r j) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
            ((iteratedCovGrad g 0 r j (Φ.op 0 r W)).toSection x) ≤
          C r j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  refine ⟨fun r j => (4 : ℝ) ^ j * gridWindowSum Φ.kappa 0 r j,
    fun r j => mul_nonneg (by positivity) (gridWindowSum_nonneg Φ.kappa_nonneg 0 r j),
    fun r W j x => ?_⟩
  have hgrid := Φ.rfns_iteratedCovGrad_grid j 0 r W x

  simpa only [Nat.add_zero, Nat.zero_add] using hgrid

/-- **The binomial covariant-Leibniz `rfns` double grid at a single centre `x₀`.**

The *at-the-centre* mirror of `rfns_iteratedCovGrad_grid`: the envelope is supplied **only at one
point** `x₀` (`hrfns_at`, the **jet** hypothesis `rfns(op p r W)(x₀) ≤ kappa p r · ∑_{q < p+1}
rfns(∇^q W)(x₀)` for every `p, r, W`, with no requirement at any other point), and the grid conclusion
is **at `x₀`** in jet form:
```
rfns(∇^j(op p r W))(x₀) ≤ 4^j · ∑_{p' ≤ j} kappa(p + p') · ∑_{q < p + j + 1} rfns(∇^q W)(x₀).
```
It is the same statement as the global grid restricted to one base point, but it does **not** require
the global field `rfns_op_le` of a `DiffBilinOp`; only the recursive single-step covariant Leibniz
`hcovGrad_op` (a section-level identity, point-free), the per-order constant `kappa` with
`kappa_nonneg`, and the pointwise **jet** envelope `hrfns_at` at `x₀`.  At the consumer entry `p = 0`
both windows collapse (`q < 1` in the hypothesis, `q < j + 1` in the conclusion).

The proof is the **verbatim single-point replay** of `rfns_iteratedCovGrad_grid`: the binomial
covariant-Leibniz induction on `j` evaluates everything at the *one* point `x₀` through the whole
recursion (the base case is the jet `hrfns_at` at `x₀`; the successor front-commutes the innermost
gradient with `rfns_iteratedCovGrad_covGrad_comm_db` at `x₀`, expands the single covariant gradient by
the point-free `hcovGrad_op`, distributes `∇^j` and `riemannianFiberNormSq_add_le` at `x₀`, and recurses
the inductive hypothesis on the two shifted pieces *at the same `x₀`*). The covariant Leibniz
recursion never invokes the envelope at any point other than `x₀`: `∇^k(op p r W)` at `x₀` is a fibre
value at `x₀`, and the recursion `op (p+1) = covGrad(op p) − cast` keeps every operator-application
read at `x₀`. This is exactly the engine the moving-centre curvature jet needs, where the envelope is
known only at the frame's own centre `x₀` (`smoothOrthoFrame g x₀`). -/
theorem rfns_iteratedCovGrad_grid_at
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p r, 0 ≤ kappa p r) (x₀ : M)
    (hrfns_at : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x₀ ((op p r W).toSection x₀) ≤
        kappa p r * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀)) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x₀
          ((iteratedCovGrad g 0 (r + p) j (op p r W)).toSection x₀) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
              ((iteratedCovGrad g 0 r q W).toSection x₀) := by
  induction j with
  | zero =>
      intro p r W
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) =
          kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns_at p r W
  | succ j ih =>
      intro p r W
      set K : ℝ := gridWindowSum kappa p r (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
          ((iteratedCovGrad g 0 r q W).toSection x₀) with hS_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p r (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x₀
            ((iteratedCovGrad g 0 (r + p) (j + 1) (op p r W)).toSection x₀) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad g 0 (r + p) (op p r W))).toSection x₀) from
        (rfns_iteratedCovGrad_covGrad_comm_db g 0 (r + p) j (op p r W) x₀).symm]
      rw [hcovGrad_op p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
          ((iteratedCovGrad g 0 ((r + p) + 1) j (op (p + 1) r W)).toSection x₀)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
              (op p (r + 1) (covGrad g 0 r W)))).toSection x₀)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (r + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
          ((iteratedCovGrad g 0 r q W).toSection x₀) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x₀
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x₀) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x₀
            ((iteratedCovGrad g 0 (r + (p + 1)) j (op (p + 1) r W)).toSection x₀) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad g 0 r W)
      have hBshift : gridWindowSum kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x₀
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x₀) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_db g 0 r q W x₀
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x₀
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (op p (r + 1) (covGrad g 0 r W))).toSection x₀) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_db (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x₀ _
      have hprodA : kA * sA ≤ K * S := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * S := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * S) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * S) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
                (op p (r + 1) (covGrad g 0 r W)))).toSection x₀) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x₀
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (op p (r + 1) (covGrad g 0 r W))).toSection x₀) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (op p (r + 1) (covGrad g 0 r W)) j x₀
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-- **The single-sum collapse of the at-centre differentiated-operator `rfns` grid.**

The at-`x₀` analogue of `exists_rfns_iteratedCovGrad_singleSum_le`: from the at-centre grid
`rfns_iteratedCovGrad_grid_at` at differentiation order `p = 0`, there is a single nonnegative
per-rank, per-order constant `C r j := 4^j · gridWindowSum kappa 0 r j` (the `4^j`-scaled order × rank
window sum over orders `[0, j]` and ranks `[r, r + j]`) such that, **at the one point `x₀`**,
```
rfns(∇^j(op 0 r W))(x₀) ≤ C r j · ∑_{q ≤ j} rfns(∇^q W)(x₀).
```
Only the pointwise **jet** envelope at `x₀` is required (per order, per rank — the rank-`r` operator's
fibre constant grows with `r`, and the order-`p` operator reads up to `∇^p W`); at the consumer's
differentiation order `p = 0` the grid's contracted-jet window collapses to `q < j + 1`.  The constant
is the same engine constant as the global collapse, so a single `x₀`-uniform family serves whichever
centre is chosen. -/
theorem exists_rfns_iteratedCovGrad_singleSum_le_at
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p r, 0 ≤ kappa p r) (x₀ : M)
    (hrfns_at : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x₀ ((op p r W).toSection x₀) ≤
        kappa p r * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀)) :
    ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x₀
          ((iteratedCovGrad g 0 r j (op 0 r W)).toSection x₀) ≤
        ((4 : ℝ) ^ j * gridWindowSum kappa 0 r j) *
          ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
              ((iteratedCovGrad g 0 r q W).toSection x₀) := by
  intro r W j
  have hgrid := rfns_iteratedCovGrad_grid_at op hcovGrad_op kappa kappa_nonneg x₀ hrfns_at j 0 r W
  simpa only [Nat.add_zero, Nat.zero_add] using hgrid

end DiffBilinOp

end Connection
end Integral
end DifferentialGeometry

end
