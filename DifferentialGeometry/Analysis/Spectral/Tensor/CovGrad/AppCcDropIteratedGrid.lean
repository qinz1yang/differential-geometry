import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS

/-! # The valence-dropping iterated covariant-gradient `rfns` grid for a fixed operator field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the analysis files `MetricContractionLeibnizGrid` (`DiffBilinOp`,
contravariant rank `0`) and `RankRDiffBilinGrid` (`DiffBilinOpRS g c`, contravariant valence `c`) build
the intrinsic `riemannianFiberNormSq` (`rfns`) binomial covariant-Leibniz grid for a differentiated
fibrewise-linear contraction whose covariant **output width equals its input width plus the
differentiation order** (`op : ∀ p r, SmoothCcTensor g c r → SmoothCcTensor g c (r + p)`).

The covariant Faà-di-Bruno arms of the Ricci–DeTurck right-hand-side linearization need a strictly more
general shape: the operator-field action `appCc C W` of a **fixed, valence-DROPPING** smooth coefficient
`C : SmoothCcTensor g b s₀` (covariant source width `b`, target width `s₀`, with `b ≠ s₀` in general —
the Christoffel-variation symbol drops `3 → 2`, the Ricci/Lichnerowicz symbol drops `4 → 2`) on a
`(0, b)`-tensor `W` lands in `(0, s₀)`, so the output width is `s₀`, **not** the input width `b`.  This
file liberates the engine to that valence-dropping shape (R7 — extend, do not duplicate):

* `DropTowerOp g b₀ s₀ C` — the order-`p` differentiated tower of the FIXED coefficient `C`, defined by
  the same exact covariant-Leibniz remainder recursion as `fixedCoeffTowerOp`, but with the output
  covariant width carried as `s₀ + (width − b₀) + p` (the drop `b₀ → s₀` baked into the base);
* `DropTower_covGrad_op` — its single-step covariant Leibniz, by `sub_add_cancel`;
* `DropTowerNormalForm` / `dropTower_normalForm` — the operator-field normal form of the tower (a finite
  sum of `appCcRS (Ψ k) (∇^k W)` of fixed smooth coefficient fields), proved by the same induction the
  RS engine uses;
* `appCc_iteratedCovGrad_drop_singleSum_le` — **the headline**: for the fixed coefficient `C`, at every
  base point `x`, gradient order `j`, and section `W`,
  ```
  rfns(∇^j (appCc C W))(x) ≤ K j · ∑_{q ≤ j} rfns(∇^q W)(x),
  ```
  the valence-dropping Moser-tame `rfns` grid the two deep Ricci–DeTurck arms (`appCc C₁ (∇(T − T'))`,
  `appCc C₂ (∇²(T − T'))`) consume, with the fixed coefficient's `C⁰` jet envelope absorbed into `K j`.

The construction is the verbatim drop-lift of `fixedCoeffTowerOp` /
`OperatorFieldCovariantCalculusRS`'s normal form: the gradient passenger rides the FRONT through the
order-advanced tower (never contracted away), and the per-order jet envelope is the uniform fibre-norm
bound of the fixed smooth operator fields on the compact base.  Sorry-free.
-/

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

/-! ## Local covariant-gradient bookkeeping helpers

The two helpers `rfns_iteratedCovGrad_covGrad_comm_dbRS` and `sum_range_shift_le_dbRS` of
`RankRDiffBilinGrid` are `private`; their contravariant-rank-`0` instances are reproduced here as local
privates serving the drop grid (the `covGrad`-commuting one through the public heterogeneous commute
`iteratedCovGrad_covGrad_comm_heq'`). -/

set_option linter.unusedSectionVars false in
/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast (heterogeneous form, rank-`0`).** -/
private theorem rfns_toSection_heq_congr_drop (g : SmoothRiemannianMetric I M)
    {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

set_option linter.unusedSectionVars false in
/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form, rank-`0`).** -/
private theorem rfns_iteratedCovGrad_covGrad_comm_drop (g : SmoothRiemannianMetric I M)
    (s m : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + m) x
        ((iteratedCovGrad g 0 (s + 1) m (covGrad g 0 s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1)) x
        ((iteratedCovGrad g 0 s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_drop g (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g 0 s m W) x

/-- **A `range`-sum shift bookkeeping helper.** -/
private lemma sum_range_shift_le_drop (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

set_option linter.unusedSectionVars false in
/-- **`rfns` front-commute of one covariant gradient through the iterated gradient (rank-`0`, public).**
The intrinsic squared fibre norm of `∇^m(∇W)` (at valence `(s + 1) + m`) equals that of `∇^{m+1}W` (at
valence `s + (m + 1)`).  The public rank-`0` instance of the heterogeneous commute
`iteratedCovGrad_covGrad_comm_heq'`; the valence-`c` instance `rfns_iteratedCovGrad_covGrad_comm_dbRS`
is `private` to `RankRDiffBilinGrid`. -/
theorem rfns_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (s m : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + m) x
        ((iteratedCovGrad g 0 (s + 1) m (covGrad g 0 s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1)) x
        ((iteratedCovGrad g 0 s (m + 1) W).toSection x) :=
  rfns_iteratedCovGrad_covGrad_comm_drop g s m W x

/-! ## The drop tower of a fixed coefficient field

We model the valence-dropping tower indexed by a base source width `b₀`, a base target width `s₀`, and
the *extra* covariant width `w` added on top of the base.  The base operator field
`C : SmoothCcTensor g b₀ s₀` is read at extra width `w` as the passenger-slot-extended field
`slotExtendIter g b₀ s₀ w C : SmoothCcTensor g (b₀ + w) (s₀ + w)` acting on `(0, b₀ + w)` inputs. -/

/-- **The `w`-fold passenger-slot extension of a fixed `(b₀, s₀)`-operator field.**  Iterates
`slotExtend` `w` times, lifting `C : SmoothCcTensor g b₀ s₀` to `SmoothCcTensor g (b₀ + w) (s₀ + w)`,
the coefficient field that acts on the extra-width-`w` input `(0, b₀ + w)`-tensor with `w` passenger
slots untouched. -/
def slotExtendIter (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) :
    ∀ (w : ℕ), SmoothCcTensor g b₀ s₀ → SmoothCcTensor g (b₀ + w) (s₀ + w)
  | 0, C => C
  | (w + 1), C =>
      slotExtend (I := I) (M := M) g (b₀ + w) (s₀ + w) (slotExtendIter g b₀ s₀ w C)

/-- **The order-`p` differentiated drop tower of a fixed coefficient `C`.**  At extra width `w`, the
`p`-times covariantly-differentiated operator-field action of `slotExtendIter w C` on a `(0, b₀ + w)`
input, defined by the same exact covariant-Leibniz remainder recursion as `fixedCoeffTowerOp`:

* `p = 0`: `appCcRS (slotExtendIter w C) W` (the operator-field action of the width-`w` coefficient);
* `p + 1`: `∇(op p w W) − (rank-cast) op p (w + 1) (∇W)` — the differentiated-coefficient remainder.

The output covariant width at order `p`, extra width `w` is `(s₀ + w) + p`. -/
def DropTowerOp (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) (C : SmoothCcTensor g b₀ s₀) :
    ∀ (p w : ℕ), SmoothCcTensor g 0 (b₀ + w) → SmoothCcTensor g 0 ((s₀ + w) + p)
  | 0, w => fun W =>
      appCcRS (I := I) (M := M) g 0 (b₀ + w) (s₀ + w) (slotExtendIter g b₀ s₀ w C) W
  | (p + 1), w => fun W =>
      covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
          (DropTowerOp g b₀ s₀ C p w W) -
        castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (DropTowerOp g b₀ s₀ C p (w + 1) (covGrad (I := I) (M := M) g 0 (b₀ + w) W))

/-- **The exact single-step covariant Leibniz of the drop tower.**  `∇(op p w W)` splits exactly into
the order-advanced remainder `op (p + 1) w W` and the rank-cast lower-order term on `∇W`.  Proved by
`sub_add_cancel` — the passenger gradient rides the FRONT through `op (p + 1)`. -/
theorem DropTower_covGrad_op (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) :
    covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
        (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W) =
      DropTowerOp (I := I) (M := M) g b₀ s₀ C (p + 1) w W +
        castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
            (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
      (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W) -
      castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
        (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
          (covGrad (I := I) (M := M) g 0 (b₀ + w) W))) + _
  rw [sub_add_cancel]

/-! ## The operator-field normal form of the drop tower -/

/-- **The operator-field normal form of the drop tower at order `p`, extra width `w`.**  The order-`p`
tower value `op p w W` decomposes as a finite sum of operator-field actions of fixed smooth operator
fields `Ψ k : SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p)` on the covariant jets `∇^k W` of the
contracted `(0, b₀ + w)`-section, `k < p + 1`. -/
def DropTowerNormalForm (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p),
    ∀ W : SmoothCcTensor g 0 (b₀ + w),
      DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W =
        ∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
            (iteratedCovGrad g 0 (b₀ + w) k W)

/-- **The gradient of a drop normal-form sum expands termwise** through the operator-field covariant
product rule (`covGrad_appCcRS_eq`): each `appCcRS (Ψ k) (∇^k W)` contributes the differentiated
coefficient action `appCcRS (∇Ψ k) (∇^k W)` plus the slot-extended action `appCcRS (slotExtend Ψ k)
(∇^{k+1} W)`. -/
theorem covGrad_dropNormalForm_sum (g : SmoothRiemannianMetric I M) (b₀ s₀ p w : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p))
    (W : SmoothCcTensor g 0 (b₀ + w)) :
    covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
        (∑ k ∈ Finset.range (p + 1),
          appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
            (iteratedCovGrad g 0 (b₀ + w) k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
            (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k))
            (iteratedCovGrad g 0 (b₀ + w) k W) +
          appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
            (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k))
            (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
    (iteratedCovGrad g 0 (b₀ + w) k W)]
  rw [show covGrad (I := I) (M := M) g 0 ((b₀ + w) + k) (iteratedCovGrad g 0 (b₀ + w) k W) =
      iteratedCovGrad g 0 (b₀ + w) (k + 1) W from (iteratedCovGrad_succ g 0 (b₀ + w) k W).symm]
  rfl

/-- **The rank-cast lower-tower drop normal form on `∇W` re-expressed in canonical jets.** -/
theorem castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M)
    (b₀ s₀ p w k : ℕ)
    (Ψ : SmoothCcTensor g ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p))
    (W : SmoothCcTensor g 0 (b₀ + w)) :
    castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
        (appCcRS (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p) Ψ
          (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))) =
      appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
        (castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
          (castRankCc_db g ((b₀ + (w + 1)) + k)
            (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) Ψ))
        (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) := by
  rw [appCcRS_castRankCc_db g 0 (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
    (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) Ψ
    (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g 0 (b₀ + w) k W)
  exact castRankCc_db_heq g 0 (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
    (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))

/-- **The drop normal form propagates up the differentiated tower.**  If order `p` admits the
operator-field normal form at *every* extra width, then so does order `p + 1` at extra width `w`. -/
theorem dropNormalForm_succ (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p : ℕ)
    (hp : ∀ w, DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C p w) (w : ℕ) :
    DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C (p + 1) w := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp w
  obtain ⟨Ψr1, hΨr1⟩ := hp (w + 1)
  set Tk : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k) -
      castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
        (castRankCc_db g ((b₀ + (w + 1)) + k)
          (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then
            covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1)) else 0)
          + Tk k, ?_⟩
  intro W
  have hrec : DropTowerOp (I := I) (M := M) g b₀ s₀ C (p + 1) w W =
      covGrad g 0 ((s₀ + w) + p) (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W) -
        castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
            (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
    rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W]; abel
  rw [hrec, hΨr W]
  rw [covGrad_dropNormalForm_sum (I := I) (M := M) g b₀ s₀ p w Ψr W]
  rw [hΨr1 (covGrad g 0 (b₀ + w) W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (appCcRS (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p) (Ψr1 k)
            (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W)))) =
      ∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
            (castRankCc_db g ((b₀ + (w + 1)) + k)
              (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (I := I) (M := M) g b₀ s₀ p w k (Ψr1 k) W)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    appCcRS (I := I) (M := M) g 0 ((b₀ + w) + j) ((s₀ + w) + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then
                covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g 0 (b₀ + w) j W)) (p + 1)]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          ((if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCcRS_add_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
            (castRankCc_db g ((b₀ + (w + 1)) + k)
              (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCcRS_sub_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
      (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k))
      (iteratedCovGrad g 0 (b₀ + w) k W)) p]
  abel

/-- **The order-`0` drop base factorisation is the order-`0` drop normal form.** -/
theorem dropNormalForm_zero (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (w : ℕ) :
    DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C 0 w := by
  refine ⟨fun k => match k with
    | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
    | (_ + 1) => 0, fun W => ?_⟩
  rw [Finset.sum_range_one]
  rfl

/-- **The drop normal form holds at every order.** -/
theorem dropTower_normalForm (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p : ℕ) :
    ∀ w : ℕ, DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C p w := by
  induction p with
  | zero => exact fun w => dropNormalForm_zero (I := I) (M := M) g b₀ s₀ C w
  | succ p ih => exact fun w => dropNormalForm_succ (I := I) (M := M) g b₀ s₀ C p ih w

/-! ## The explicit per-order jet envelope from the drop normal form

The per-order, per-width jet envelope constant of the drop tower is built as an **explicit functional**
of the fixed coefficient field `C`'s covariant jets, with no opaque outer `Classical.choose`.  Two named
ingredients carry the construction:

* `dropTowerPsi` — the drop-normal-form operator field `Ψ` of `(C, p, w)` (the `covGrad`/`slotExtend`
  jets of `C`), named from the witness of `dropTower_normalForm`;
* `dropFibreSup` — the per-`k` uniform fibre-norm-square envelope of the operator field `Ψ k`, named from
  the witness of `exists_uniform_riemannianFiberNormSq_appCcRS_le`.

The envelope constant `dropKappa C p w := (p + 1) · ∑_{k ≤ p} dropFibreSup C p w k` is then a plain
`def` whose value is a NAMED finite sum of fibre-norm sups of `C`'s jets — a transparent functional, not
hidden behind the outer existence's `Classical.choose`.  (Each `dropFibreSup` is itself a `Classical.choose`
of the per-`k` compactness sup, which is acceptable: it is now an explicit, named per-`k` functional of
`C`'s jets, exposed to downstream as the `dropKappa_le_of_fibreNormSup` handle.) -/

/-- **The drop-normal-form operator field `Ψ` of the fixed coefficient `(C, p, w)`, EXPLICIT.**  The
order-`k` `covGrad`/`slotExtend` jet of `C` in the operator-field normal form of the drop tower,
defined by the *explicit* witness recursion of `dropNormalForm_zero`/`dropNormalForm_succ` (NOT an
opaque `Classical.choose`):

* `p = 0`: `Ψ 0 = slotExtendIter w C`, `Ψ (k + 1) = 0`;
* `p + 1`: built from the order-`p` fields `Ψr = dropTowerPsi p w`, `Ψr1 = dropTowerPsi p (w + 1)` by the
  Leibniz remainder recursion — `Ψ 0 = ∇(Ψr 0)`, and for `k + 1`,
  `Ψ (k + 1) = (if k + 1 < p + 1 then ∇(Ψr (k + 1)) else 0) + (slotExtend (Ψr k) − cast (Ψr1 k))`.

Exposing the explicit recursion (in place of `Classical.choose`) is what makes the per-jet fibre-norm
bound `dropTowerPsi_fibreNormSq_le_iteratedCovGrad` provable: a `Classical.choose` witness's fibre norm
is uncontrolled (the operator-action normal-form equation does not pin the operator field down — there
is no `appCcRS` injectivity), whereas the explicit `covGrad`/`slotExtend` jets are bounded by the
`iteratedCovGrad` jets of `C`. -/
def dropTowerPsi (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) : (p w : ℕ) → (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p)
  | 0, w => fun k => match k with
      | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
      | (_ + 1) => 0
  | (p + 1), w => fun j => match j with
      | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p)
          (dropTowerPsi g b₀ s₀ C p w 0)
      | (k + 1) =>
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi g b₀ s₀ C p w (k + 1))
            else 0)
          + (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
              (dropTowerPsi g b₀ s₀ C p w k) -
            castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
              (castRankCc_db g ((b₀ + (w + 1)) + k)
                (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (dropTowerPsi g b₀ s₀ C p (w + 1) k)))

/-- The order-`0` value of `dropTowerPsi`. -/
theorem dropTowerPsi_zero (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (w : ℕ) :
    dropTowerPsi (I := I) (M := M) g b₀ s₀ C 0 w =
      fun k => match k with
        | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
        | (_ + 1) => 0 :=
  rfl

/-- **The drop normal form holds for the explicit operator field `dropTowerPsi`.**  Proved by induction on
`p`, re-using the `dropNormalForm_zero`/`dropNormalForm_succ` algebra against the explicit witness. -/
theorem dropTowerPsi_spec (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) :
    DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W =
      ∑ k ∈ Finset.range (p + 1),
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
          (iteratedCovGrad g 0 (b₀ + w) k W) := by
  induction p generalizing w W with
  | zero =>
      rw [Finset.sum_range_one]
      change appCcRS (I := I) (M := M) g 0 (b₀ + w) (s₀ + w)
          (slotExtendIter (I := I) (M := M) g b₀ s₀ w C) W = _
      rw [iteratedCovGrad_zero]
      rfl
  | succ p ih =>
      have hrec : DropTowerOp (I := I) (M := M) g b₀ s₀ C (p + 1) w W =
          covGrad g 0 ((s₀ + w) + p) (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W) -
            castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
        rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W]; abel
      rw [hrec, ih w W, covGrad_dropNormalForm_sum (I := I) (M := M) g b₀ s₀ p w _ W]
      rw [ih (w + 1) (covGrad g 0 (b₀ + w) W), castRankCc_db_finset_sum]
      rw [show (∑ k ∈ Finset.range (p + 1),
            castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (appCcRS (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)
                (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W)))) =
          ∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
                (castRankCc_db g ((b₀ + (w + 1)) + k)
                  (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                  (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from
        Finset.sum_congr rfl (fun k _ =>
          castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (I := I) (M := M) g b₀ s₀ p w k
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k) W)]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun j =>
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + j) ((s₀ + w) + (p + 1))
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w j)
          (iteratedCovGrad g 0 (b₀ + w) j W)) (p + 1)]
      have hPsi0 : dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w 0 =
          covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w 0) := rfl
      have hPsiSucc : ∀ k : ℕ, dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w (k + 1) =
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
            else 0)
          + (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
              (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) -
            castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
              (castRankCc_db g ((b₀ + (w + 1)) + k)
                (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k))) := fun k => rfl
      rw [hPsi0]
      have hsplit : (∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w (k + 1))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
          (∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (if k + 1 < p + 1 then
                  covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
                else 0)
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) +
          ((∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) -
          (∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (castSrcCc g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
                (castRankCc_db g ((b₀ + (w + 1)) + k)
                  (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                  (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W))) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hPsiSucc k, appCcRS_add_left, appCcRS_sub_left]
      rw [hsplit]
      rw [show (∑ k ∈ Finset.range (p + 1),
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (if k + 1 < p + 1 then
                  covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
                else 0)
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
          ∑ k ∈ Finset.range p,
            appCcRS (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
      rw [Finset.sum_range_succ' (fun k =>
        appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
          (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k))
          (iteratedCovGrad g 0 (b₀ + w) k W)) p]
      abel

/-- **The per-`k` uniform fibre-norm-square envelope of the operator field `dropTowerPsi`, CANONICAL.**
The supremum over the (compact) base of the intrinsic fibre-norm-square of the order-`k` jet field
`Ψ k = dropTowerPsi C p w k`:
```
dropFibreSup C p w k = ⨆ x, rfns(Ψ k)(x).
```
This is the canonical (least) uniform fibre-norm envelope: by `exists_bound_riemannianFiberNormSq_smoothCcTensor`
the fibre-norm-square `x ↦ rfns(Ψ k)(x)` is bounded above on the compact base, so the `iSup` is finite and
agrees with the operator-action proportionality constant of `exists_uniform_riemannianFiberNormSq_appCcRS_le`,
while now carrying a genuine upper-bound API (`dropFibreSup_le_of_fibreNormSup`): any uniform bound on the
field's fibre sups dominates it.  (On the degenerate empty base the `iSup` of a real-valued function is `0`,
so the constant is still nonnegative.) -/
def dropFibreSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) : ℝ :=
  ⨆ x : M, riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
    ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)

/-- **The fibre-norm-square field of the order-`k` jet `Ψ k` is bounded above on the compact base.**
The `BddAbove` witness underlying the finiteness of the canonical `dropFibreSup` iSup, from the global
fibre-norm bound on the fixed smooth section `Ψ k`. -/
private theorem dropFibreSup_bddAbove (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) :
    BddAbove (Set.range fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
        ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)) := by
  obtain ⟨K, _, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g
    ((b₀ + w) + k) ((s₀ + w) + p) (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
  exact ⟨K, by rintro _ ⟨x, rfl⟩; exact hK x⟩

/-- **The canonical fibre sup is the per-point upper bound of the jet field's fibre-norm-square.**
`rfns(Ψ k)(x) ≤ dropFibreSup C p w k` for every base point `x`, by `le_ciSup` against the `BddAbove`
witness.  This is the canonical analogue of the chosen-constant property the operator bound consumes. -/
theorem dropFibreSup_fibre_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
        ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x) ≤
      dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  le_ciSup (dropFibreSup_bddAbove (I := I) (M := M) g b₀ s₀ C p w k) x

theorem dropFibreSup_nonneg (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) :
    0 ≤ dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  Real.iSup_nonneg fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g ((b₀ + w) + k)
    ((s₀ + w) + p) x ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)

/-- **The canonical upper-bound API: any nonnegative uniform fibre-norm-square bound dominates
`dropFibreSup`.**  If `0 ≤ K` and `K` uniformly bounds the order-`k` jet field's fibre-norm-square
(`∀ x, rfns(Ψ k)(x) ≤ K`), then `dropFibreSup C p w k ≤ K`, by `Real.iSup_le` (which absorbs the
degenerate empty base via `sSup ∅ = 0`, where the nonnegativity of `K` carries the bound).  This is the
KEY new handle the envelope leaf consumes: it lets the supercritical-embedding ball-uniform control of
the field's covariant-jet fibre sups (themselves nonnegative) bound `dropFibreSup` ball-uniformly.  The
`0 ≤ K` side condition is automatically met by any genuine fibre-norm-square bound (the bounded
quantities are nonnegative), and is required only to handle the degenerate empty manifold, on which the
`iSup` collapses to `0`. -/
theorem dropFibreSup_le_of_fibreNormSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) {K : ℝ} (hK_nonneg : 0 ≤ K)
    (hK : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
      ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x) ≤ K) :
    dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k ≤ K :=
  Real.iSup_le hK hK_nonneg

theorem dropFibreSup_spec (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ)
    (W : SmoothCcTensor g 0 ((b₀ + w) + k)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
        ((appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) W).toSection x) ≤
      dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k *
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + k) x (W.toSection x) := by
  rw [appCcRS_toSection (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) W x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g 0 ((b₀ + w) + k)
    ((s₀ + w) + p) x ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)
    (W.toSection x)) ?_
  exact mul_le_mul_of_nonneg_right (dropFibreSup_fibre_le (I := I) (M := M) g b₀ s₀ C p w k x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + k) x (W.toSection x))

/-! ## The packaged per-order, per-width jet envelope -/

/-- **The packaged per-order, per-width jet envelope constant of the drop tower, EXPLICIT.**  The
nonnegative two-index family `(p, w) ↦ (p + 1) · ∑_{k ≤ p} dropFibreSup C p w k`: a NAMED finite sum of
the fibre-norm sups of `C`'s `covGrad`/`slotExtend` jets, with no opaque outer `Classical.choose`.  This
is the witness the drop-tower jet bound asserts; downstream may dominate it via the
`dropKappa_le_of_fibreNormSup` handle by ball-uniform bounds on the field's covariant-jet fibre sups. -/
def dropKappa (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) (C : SmoothCcTensor g b₀ s₀) :
    ℕ → ℕ → ℝ :=
  fun p w => (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k

/-- **`dropKappa` is, by definition, `(p + 1) · ∑_{k ≤ p} dropFibreSup C p w k`.**  The exposed unfolding
of the explicit envelope constant. -/
theorem dropKappa_eq_explicit (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    dropKappa (I := I) (M := M) g b₀ s₀ C p w =
      (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  rfl

theorem dropKappa_nonneg (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    0 ≤ dropKappa (I := I) (M := M) g b₀ s₀ C p w :=
  mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k _ => dropFibreSup_nonneg (I := I) (M := M) g b₀ s₀ C p w k)

/-- **The downstream domination handle: `dropKappa` is bounded by `(p + 1)` times the sum of any per-`k`
upper bounds on the operator-field fibre sups.**  If a two-index-plus-`k` family `S` dominates each
`dropFibreSup C p w k`, then `dropKappa C p w ≤ (p + 1) · ∑_{k ≤ p} S p w k`.  This is the explicit-functional
exposure the envelope leaf consumes: bounding the (covariant-jet) fibre sups `dropFibreSup` ball-uniformly
(which the supercritical embedding controls) bounds `dropKappa` ball-uniformly. -/
theorem dropKappa_le_of_fibreNormSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (S : ℕ → ℕ → ℕ → ℝ)
    (hS : ∀ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k ≤ S p w k) :
    dropKappa (I := I) (M := M) g b₀ s₀ C p w ≤
      (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), S p w k := by
  rw [dropKappa_eq_explicit]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hS) (by positivity)

theorem dropTower_rfns_op_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
        ((DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W).toSection x) ≤
      dropKappa (I := I) (M := M) g b₀ s₀ C p w * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
  set Ck : ℕ → ℝ := fun k => dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k with hCk_def
  have hCk_nn : ∀ k, 0 ≤ Ck k := fun k => dropFibreSup_nonneg (I := I) (M := M) g b₀ s₀ C p w k
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + k) x
    ((iteratedCovGrad g 0 (b₀ + w) k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + k) x _
  rw [dropKappa_eq_explicit, dropTowerPsi_spec (I := I) (M := M) g b₀ s₀ C p w W,
    SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 ((s₀ + w) + p) x
    (Finset.range (p + 1))
    (fun k => (appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
      (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
      (iteratedCovGrad g 0 (b₀ + w) k W)).toSection x)) ?_
  rw [Finset.card_range]
  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
          ((appCcRS (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
            (iteratedCovGrad g 0 (b₀ + w) k W)).toSection x) ≤ Ck k * a k := fun k _ =>
    dropFibreSup_spec (I := I) (M := M) g b₀ s₀ C p w k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_
  have hCa_le : (∑ k ∈ Finset.range (p + 1), Ck k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hCk_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), Ck k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

/-- **The per-order jet envelope of the drop tower from its operator-field normal form.**  The
existential packaging of `dropTower_rfns_op_le`: the explicit `dropKappa` constant is a valid witness.
If `op p w` admits the drop normal form, then its intrinsic squared fibre norm is bounded, uniformly over
the compact `M`, by a nonnegative constant times the order-`≤ p` covariant jet of the contracted
section. -/
theorem exists_dropTower_jet_bound (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g 0 (b₀ + w)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
            ((DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
              ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) :=
  ⟨dropKappa (I := I) (M := M) g b₀ s₀ C p w, dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C p w,
    fun W x => dropTower_rfns_op_le (I := I) (M := M) g b₀ s₀ C p w W x⟩

/-! ## The binomial covariant-Leibniz `rfns` grid of the drop tower -/

/-- **The binomial covariant-Leibniz `rfns` double grid for the drop tower.**  The drop-lift of
`DiffBilinOpRS.rfns_iteratedCovGrad_grid`: for every gradient order `j`, differentiation order `p`,
extra width `w`, section `W`, and point `x`,
```
rfns(∇^j(op p w W))(x) ≤ 4^j · gridWindowSum (dropKappa) p w j · ∑_{q < p + j + 1} rfns(∇^q W)(x).
```
Proved by the same binomial covariant-Leibniz induction on `j` (the recursion climbs the extra-width
index `w`, which plays the role of the rank index in `gridWindowSum`). -/
theorem dropTower_rfns_iteratedCovGrad_grid (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (j : ℕ) :
    ∀ (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + p) + j) x
          ((iteratedCovGrad g 0 ((s₀ + w) + p) j
            (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
              ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
  induction j with
  | zero =>
      intro p w W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) =
          dropKappa (I := I) (M := M) g b₀ s₀ C p w * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact dropTower_rfns_op_le (I := I) (M := M) g b₀ s₀ C p w W x
  | succ j ih =>
      intro p w W x
      set K : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) p w (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + p) + (j + 1)) x
            ((iteratedCovGrad g 0 ((s₀ + w) + p) (j + 1)
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
            ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
              (covGrad g 0 ((s₀ + w) + p)
                (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_drop g ((s₀ + w) + p) j
          (DropTowerOp (I := I) (M := M) g b₀ s₀ C p w W) x).symm]
      rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
          ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
            (DropTowerOp (I := I) (M := M) g b₀ s₀ C (p + 1) w W)).toSection x)
          ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
            (castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) (p + 1) w j with hkA_def
      set kB : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p (w + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + (q + 1)) x
          ((iteratedCovGrad g 0 (b₀ + w) (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + (p + 1)) + j) x
            ((iteratedCovGrad g 0 ((s₀ + w) + (p + 1)) j
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C (p + 1) w W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) w W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (w + 1) (covGrad g 0 (b₀ + w) W) x
      have hBshift : gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p (w + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + (w + 1)) + q) x
                ((iteratedCovGrad g 0 (b₀ + (w + 1)) q (covGrad g 0 (b₀ + w) W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_drop g (b₀ + w) q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + (w + 1)) + p) + j) x
            ((iteratedCovGrad g 0 ((s₀ + (w + 1)) + p) j
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C)
          p w j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C)
          p w j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_drop (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
            ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) (p + 1) w j
      have hkB_nn : 0 ≤ kB :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) p (w + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + (q + 1)) x _
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
          (4 : ℝ) ^ (j + 1) * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
            ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
              (castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
                  (covGrad g 0 (b₀ + w) W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + (w + 1)) + p) + j) x
            ((iteratedCovGrad g 0 ((s₀ + (w + 1)) + p) j
              (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_db g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (DropTowerOp (I := I) (M := M) g b₀ s₀ C p (w + 1) (covGrad g 0 (b₀ + w) W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

/-! ## The headline valence-dropping iterated `appCc` grid -/

/-- **The order-`0`, extra-width-`0` drop tower is the fixed-coefficient operator-field action.**  At
`p = 0`, `w = 0`, the tower is `appCcRS C W = appCc C W` (`slotExtendIter 0 C = C`,
`appCcRS_zero_eq_appCc`). -/
theorem dropTowerOp_zero_eq_appCc (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) :
    DropTowerOp (I := I) (M := M) g b₀ s₀ C 0 0 W = appCc (I := I) (M := M) g b₀ s₀ C W := by
  change appCcRS (I := I) (M := M) g 0 (b₀ + 0) (s₀ + 0)
      (slotExtendIter (I := I) (M := M) g b₀ s₀ 0 C) W = _
  simp only [slotExtendIter, Nat.add_zero]
  rw [appCcRS_zero_eq_appCc (I := I) (M := M) g b₀ s₀ C W]

/-- **The valence-dropping iterated covariant-gradient `rfns` grid for a fixed operator field, with the
EXPLICIT engine constant.**

For a fixed smooth coefficient `C : SmoothCcTensor g b₀ s₀` (covariant source width `b₀`, target `s₀`,
arbitrary drop), at every base point `x`, gradient order `j`, and section `W : SmoothCcTensor g 0 b₀`:
```
rfns(∇^j (appCc C W))(x) ≤ (4^j · gridWindowSum (dropKappa C) 0 0 j) · ∑_{q ≤ j} rfns(∇^q W)(x).
```
The per-order constant is the EXPOSED `4^j · gridWindowSum (dropKappa C) 0 0 j` (so a downstream
consumer can dominate it by a ball-uniform sup of the same window), absorbing the fixed coefficient's
`C⁰` jet envelope.  This is the chart-jet-free Moser-tame `rfns` grid the deep Ricci–DeTurck arms
`appCc C₁ (∇(T − T'))` (drop `3 → 2`) and `appCc C₂ (∇²(T − T'))` (drop `4 → 2`) consume; instantiate at
`b₀ = 3, s₀ = 2` and `b₀ = 4, s₀ = 2`.  Sorry-free. -/
theorem appCc_iteratedCovGrad_drop_singleSum_le_explicit (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
        ((iteratedCovGrad g 0 s₀ j (appCc (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
      ((4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) 0 0 j) *
        ∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + q) x
            ((iteratedCovGrad g 0 b₀ q W).toSection x) := by
  have hgrid := dropTower_rfns_iteratedCovGrad_grid (I := I) (M := M) g b₀ s₀ C j 0 0 W x
  rw [dropTowerOp_zero_eq_appCc (I := I) (M := M) g b₀ s₀ C W] at hgrid
  simpa only [Nat.add_zero, Nat.zero_add, mul_assoc] using hgrid

/-- **The valence-dropping iterated covariant-gradient `rfns` grid for a fixed operator field.**

The existential-constant packaging of `appCc_iteratedCovGrad_drop_singleSum_le_explicit`:
```
rfns(∇^j (appCc C W))(x) ≤ K j · ∑_{q ≤ j} rfns(∇^q W)(x),
```
with a single nonnegative per-order constant `K`.  Sorry-free. -/
theorem appCc_iteratedCovGrad_drop_singleSum_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
            ((iteratedCovGrad g 0 s₀ j (appCc (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
          K j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + q) x
              ((iteratedCovGrad g 0 b₀ q W).toSection x) :=
  ⟨fun j => (4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) 0 0 j,
    fun j => mul_nonneg (by positivity)
      (gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) 0 0 j),
    fun W j x => appCc_iteratedCovGrad_drop_singleSum_le_explicit (I := I) (M := M) g b₀ s₀ C W j x⟩

end Connection
end Integral
end DifferentialGeometry

end
