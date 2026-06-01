import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvL2Bound

/-!
# Sub-additivity of the intrinsic tensor fibre norm

For a smooth Riemannian metric `g` on a manifold `M` modelled on a real inner-product space
`E`, the intrinsic squared tensor fibre norm `riemannianFiberNormSq g r s x T` coincides with
the model Gram-matrix-based pointwise inner product
`tensorInnerPointwise g r s x (toModel T) (toModel T)`
(the bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`). Because `tensorInnerPointwise`
is a genuine symmetric, bilinear, positive-semidefinite form (its diagonal is `≥ 0`, with
pointwise Cauchy–Schwarz `⟨S, T⟩² ≤ ⟨S, S⟩ ⟨T, T⟩`), the squared fibre norm inherits the
elementary inner-product inequalities: it is `2`-sub-additive on a sum of two tensors, and
`n`-sub-additive on a finite frame sum of `n` tensors.

These are the analytic packaging used to turn a *decomposition of a tensor section value into a
fixed finite number of curvature-contraction summands* into a fibre-norm bound by the sum of
the summands' fibre norms — the form in which the per-summand curvature controls
(`Tensor3rdCurvFiberNormBound.lean`, `RiemannianFiberNormSqRiemannOpHigherRankParseval.lean`)
are consumed. Specifically, once the pointwise curried identity
```
covGradRoughLapCurv g T₀ (x) (unit) curried along w
  = Tensor3rdCurv g 0 2 (smoothExtensionTangent x w) T₀ x (unit) − residual(x, w)
```
is established (`CovGradRoughLapCommutatorClose3.lean`), the `n`-sub-additivity here reduces the
curvature defect's fibre norm to the sum of the `Tensor3rdCurv` summands' fibre norms (each a
curvature contraction, controlled by `RiemannianFiberNormSqRiemannOpHigherRankParseval.lean`)
plus the moving-frame residual's fibre norm, yielding the pointwise `hpt` hypothesis of
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound` (`CovGradRoughLapCurvL2Bound.lean`).

The single ingredient gating that curried identity is the slot-`0` frame-trace matching
`Δ_∇(∇T₀)(x)(unit) curried along w = ∑ᵢ ∇_{Bᵢ}∇_{Bᵢ}(∇_W T₀)(x)(unit)` (with
`B_i := smoothOrthoFrame g x i`, `W := smoothExtensionTangent x w`); it is the genuine
third-order tensor Weitzenböck Christoffel cancellation documented as open in
`CovGradRoughLapCommutatorClose{2,3}.lean`, and is **not** discharged here. This file supplies
the frame-sum fibre-norm packaging so that closing that matching immediately delivers `hpt`.

## Main results

* `riemannianFiberNormSq_add_le` — the `2`-sub-additivity
  `rfns g r s x (a + b) ≤ 2 · rfns g r s x a + 2 · rfns g r s x b`.

* `riemannianFiberNormSq_sub_le` — the same on a difference,
  `rfns g r s x (a − b) ≤ 2 · rfns g r s x a + 2 · rfns g r s x b`.

* `riemannianFiberNormSq_sum_le_card_mul` — the `n`-sub-additivity on a finite indexed sum,
  `rfns g r s x (∑ i ∈ I, F i) ≤ I.card · ∑ i ∈ I, rfns g r s x (F i)`.

## Conventions

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` — never a
model-space norm or a bundle continuous-linear-map operator norm.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The squared fibre norm of a sum, expanded by bilinearity of the underlying pointwise inner
product through the bridge:
`rfns(a + b) = rfns(a) + 2 ⟨a, b⟩ + rfns(b)`, where `⟨a, b⟩` is the pointwise inner product of
the trivialized model tensors. -/
lemma riemannianFiberNormSq_add_expand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
              (x := x) a)
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
              (x := x) b) +
        riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := x) b)
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := x) a)
  rw [hsymm]
  ring

/-- **`2`-sub-additivity of the squared fibre norm.** For any two `(r, s)`-tensors `a, b` at
`x`, `rfns(a + b) ≤ 2 · rfns(a) + 2 · rfns(b)`. This is the inner-product inequality
`‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`, transported through the fibre-norm bridge. -/
theorem riemannianFiberNormSq_add_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  set am := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
    (x := x) a with ham
  set bm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
    (x := x) b with hbm
  have haa : riemannianFiberNormSq (I := I) (M := M) g r s x a =
      tensorInnerPointwise (I := I) (M := M) g r s x am am := by
    rw [ham]; exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a
  have hbb : riemannianFiberNormSq (I := I) (M := M) g r s x b =
      tensorInnerPointwise (I := I) (M := M) g r s x bm bm := by
    rw [hbm]; exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b
  rw [riemannianFiberNormSq_add_expand (I := I) (M := M) g r s x a b, ← ham, ← hbm]
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x a with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x b with hB
  set C : ℝ := tensorInnerPointwise (I := I) (M := M) g r s x am bm with hC
  have hA_nn : 0 ≤ A := by rw [hA]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x a
  have hB_nn : 0 ≤ B := by rw [hB]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b
  have hCS : C ^ 2 ≤ A * B := by
    rw [haa, hbb]
    exact tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s x am bm
  nlinarith [hCS, hA_nn, hB_nn, sq_nonneg (A - B), sq_nonneg (C - A), sq_nonneg (C - B)]

/-- **`2`-sub-additivity on a difference.** `rfns(a − b) ≤ 2 · rfns(a) + 2 · rfns(b)`. -/
theorem riemannianFiberNormSq_sub_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  have hneg : riemannianFiberNormSq (I := I) (M := M) g r s x (-b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x b := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-b),
      riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
    rw [TensorRSSpace.toModel_neg]
    rw [show (-(TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
          (x := x) b)) = ((-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) b) from by rw [neg_one_smul]]
    rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
    ring
  rw [sub_eq_add_neg]
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (a + (-b))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
          2 * riemannianFiberNormSq (I := I) (M := M) g r s x (-b) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
    _ = 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
          2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by rw [hneg]

/-- Bilinearity of `tensorInnerPointwise` in the left argument over a *plain* finite sum
(without scalar coefficients), proved by direct induction from the two-term additivity. This
self-contained version avoids the `[CompactSpace M]` section assumption attached to the
scalar-coefficient `tensorInnerPointwise_sum_left` of `PreHilbert.lean`. -/
private lemma tensorInnerPointwise_plain_sum_left
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (A : ι → TensorRSModel r s' ℝ E) (B : TensorRSModel r s' ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s' x (∑ k ∈ s, A k) B =
      ∑ k ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x (A k) B := by
  classical
  induction s using Finset.induction with
  | empty => simp [tensorInnerPointwise_zero_left]
  | insert i₀ s'' hi₀ ih =>
      rw [Finset.sum_insert hi₀, tensorInnerPointwise_add_left, ih, Finset.sum_insert hi₀]

/-- Bilinearity of `tensorInnerPointwise` in the right argument over a *plain* finite sum. -/
private lemma tensorInnerPointwise_plain_sum_right
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (A : TensorRSModel r s' ℝ E) (s : Finset ι) (B : ι → TensorRSModel r s' ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s' x A (∑ l ∈ s, B l) =
      ∑ l ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x A (B l) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tensorInnerPointwise_zero_right]
  | insert j₀ s'' hj₀ ih =>
      rw [Finset.sum_insert hj₀, tensorInnerPointwise_add_right, ih, Finset.sum_insert hj₀]

/-- The squared fibre norm of a finite indexed sum, expanded by bilinearity through the bridge
as the double sum of pointwise inner products of the trivialized model tensors. -/
lemma riemannianFiberNormSq_sum_eq_double_sum
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (F : ι → TensorRSSpace r s' I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s' x (∑ i ∈ s, F i) =
      ∑ i ∈ s, ∑ j ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
            (x := x) (F i))
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
            (x := x) (F j)) := by
  classical
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s' x (∑ i ∈ s, F i)]
  have hsum_model : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
      (x := x) (∑ i ∈ s, F i) =
      ∑ i ∈ s, TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
        (x := x) (F i) :=
    map_sum (tensorRSSpace_continuousLinearEquiv (I := I) r s' x) F s
  rw [hsum_model]
  rw [tensorInnerPointwise_plain_sum_left (I := I) (M := M) g r s' x s _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorInnerPointwise_plain_sum_right (I := I) (M := M) g r s' x _ s _]

/-- **`n`-sub-additivity of the squared fibre norm on a finite indexed sum.** For a finite
index set `s` and a family `F` of `(r, s')`-tensors at `x`,
`rfns(∑ i ∈ s, F i) ≤ s.card · ∑ i ∈ s, rfns(F i)`. The proof expands the squared norm into the
double sum of pointwise inner products, bounds each cross term by the AM–GM consequence of
pointwise Cauchy–Schwarz `⟨Fᵢ, Fⱼ⟩ ≤ ½(rfns Fᵢ + rfns Fⱼ)`, and sums. -/
theorem riemannianFiberNormSq_sum_le_card_mul
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (F : ι → TensorRSSpace r s' I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s' x (∑ i ∈ s, F i) ≤
      (s.card : ℝ) * ∑ i ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) := by
  classical
  rw [riemannianFiberNormSq_sum_eq_double_sum (I := I) (M := M) g r s' x s F]
  set fm : ι → TensorRSModel r s' ℝ E := fun i =>
    TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s') (x := x) (F i)
    with hfm
  have hrfns_eq : ∀ i,
      riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) =
        tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm i) := by
    intro i; rw [hfm]
    exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s' x (F i)
  have hpair : ∀ i ∈ s, ∀ j ∈ s,
      tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j) ≤
        (1 / 2 : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
          riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) := by
    intro i _ j _
    set bij : ℝ := tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j) with hbij
    have hsq : bij ^ 2 ≤
        riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) *
          riemannianFiberNormSq (I := I) (M := M) g r s' x (F j) := by
      rw [hbij, hrfns_eq i, hrfns_eq j]
      exact tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s' x (fm i) (fm j)
    have hi_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s' x (F i)
    have hj_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s' x (F j) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s' x (F j)
    nlinarith [hsq, hi_nn, hj_nn, sq_nonneg (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i)
      - riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)), sq_nonneg bij]
  calc (∑ i ∈ s, ∑ j ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j))
      ≤ ∑ i ∈ s, ∑ j ∈ s, (1 / 2 : ℝ) *
          (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
            riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) := by
        refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i hi j hj))
    _ = (s.card : ℝ) * ∑ i ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) := by
        rw [show (∑ i ∈ s, ∑ j ∈ s, (1 / 2 : ℝ) *
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) =
            (1 / 2 : ℝ) * (∑ i ∈ s, ∑ j ∈ s,
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) from by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.mul_sum]]
        rw [show (∑ i ∈ s, ∑ j ∈ s,
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) =
            ∑ i ∈ s, ((s.card : ℝ) * riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
              ∑ j ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) from by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring

end Connection
end Integral
end DifferentialGeometry

end
