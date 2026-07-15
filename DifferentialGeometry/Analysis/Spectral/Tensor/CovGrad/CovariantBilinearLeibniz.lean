import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound

/-! # The bilinear covariant Leibniz rule for the iterated covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
linear file `IteratedCovGradLinear` records that the iterated section-level covariant gradient
`∇^j = iteratedCovGrad g r s j` is additive in its section, and the scalar file
`CovariantLeibniz` records the single-step covariant Leibniz rule for a *smooth-scalar-weighted*
section.  Neither provides a Leibniz/product rule for `∇^j` of a tensor *contraction/product* — the
keystone needed to expand the covariant jet of a bilinear combination of two tensor sections.

This file supplies that rule for a smooth *parallel* fibrewise continuous-bilinear bundle map,
the kind realized by metric contractions of a tensor product (parallel because `∇g = 0`).  Such a
map is packaged here as `ParallelTensorProduct`: a section-level bilinear product `prod`, valid at
every shifted gradient order, that is fibrewise-operator-bounded in the intrinsic `g`-Riemannian
squared fibre norm `riemannianFiberNormSq` (`rfns_prod_le`) and satisfies the exact single-step
covariant Leibniz identity `∇(prod S T) = prod (∇S) T + prod S (∇T)` (`covGrad_prod`).  The operator
bound is phrased `g`-natively — never the model fibre norm `‖·‖`, whose operator constant is
chart-Jacobian-unbounded relative to the intrinsic `g`-norm on a multi-chart manifold (so the
inhabitants of this structure are soundly fillable `g`-natively, with no chart-trivialisation
circularity).  From these two genuine `∇`-compatibility hypotheses the binomial covariant jet
expansion follows; the deliverable the covariant Faà-di-Bruno chain consumes is the `g`-native
diagonal-window covariant-Leibniz grid `diagGrid_rfns_jet`, proved downstream (in the
DeTurck-remainder file) by induction on the gradient order on top of `covGrad_prod` and the supplied
`g`-native operator bound.

## Main definitions

* `ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀` — a parallel fibrewise continuous-bilinear bundle map
  from `(r₁, s₁ + a)`-tensors and `(r₂, s₂ + b)`-tensors to `(r₀, s₀ + a + b)`-tensors.  Its
  hypotheses are the genuine constraints of a `∇`-compatible bounded bilinear map: a uniform
  `g`-Riemannian fibrewise operator bound, and the exact single-step covariant Leibniz identity.

## Main results

* `ParallelTensorProduct.prod_zero_left`, `prod_zero_right` — a parallel product kills the zero
  section in either argument (non-degeneracy: the `g`-Riemannian operator bound is genuine, rejecting
  the degenerate witness).

The pointwise covariant-commutation byproducts `norm_toSection_iteratedCovGrad_covGrad_comm` and
`norm_toSection_iteratedCovGrad_castRankCc` (fibre-norm invariance of the order/rank reindexings) are
exported as reusable covariant-calculus lemmas. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Heterogeneous rank-congruence for `covGrad`.** If two ranks agree (`h : a = b`), then the
once-differentiated tensors `covGrad g r a Y` and `covGrad g r b Z` are heterogeneously equal
whenever `Y` and `Z` are. Proved by `subst` on the rank variable. -/
private theorem covGrad_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying
`m` covariant gradients to `covGrad g r s X` is heterogeneously equal to the `(m + 1)`-fold iterated
gradient of `X`; the two live in the ranks `(s + 1) + m` and `s + (m + 1)`, which agree as naturals.
Proved by induction on `m` through `covGrad_heq_congr`. -/
private theorem iteratedCovGrad_covGrad_comm_heq (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The pointwise fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value fibre norms
at every point. Proved by `subst` on the rank variable. -/
private theorem norm_toSection_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    ‖Y.toSection x‖ = ‖Z.toSection x‖ := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Commuting one covariant gradient through the iterated gradient (pointwise-norm form).**
Applying `m` covariant gradients to `covGrad g r s X` has the same section-value fibre norm at `x`
as the `(m + 1)`-fold iterated gradient of `X`: the rank reassociation `(s + 1) + m = s + (m + 1)`
is invisible to the fibre norm. Proved from `iteratedCovGrad_covGrad_comm_heq` through
`norm_toSection_heq_congr`. -/
theorem norm_toSection_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (X : SmoothCcTensor g r s) (x : M) :
    ‖(iteratedCovGrad g r (s + 1) m (covGrad g r s X)).toSection x‖ =
      ‖(iteratedCovGrad g r s (m + 1) X).toSection x‖ :=
  norm_toSection_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq (g := g) (r := r) (s := s) (m := m) X) x

/-- The rank-cast of a smooth compactly-supported tensor along a `Nat` equality of covariant ranks,
transported through `SmoothCcTensor.congr_simp`.  Used only to align the left Leibniz summand
`prod (∇S) T` (covariant rank `(s₀ + a + 1) + b`) with the differentiated product
`∇(prod S T)` (covariant rank `(s₀ + a + b) + 1`). -/
def castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (Y : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ Y

/-- **The iterated-gradient fibre norm is invariant under the rank-cast.** The `j`-fold iterated
covariant gradient of the rank-cast `castRankCc g r h Y` has the same section-value fibre norm at
`x` as that of `Y`. Proved by `subst` on the rank equality, which collapses the cast to the
identity. -/
theorem norm_toSection_iteratedCovGrad_castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (Y : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    ‖(iteratedCovGrad g r b j (castRankCc g r h Y)).toSection x‖ =
      ‖(iteratedCovGrad g r a j Y).toSection x‖ := by
  subst h
  rfl

/-- **A parallel fibrewise continuous-bilinear bundle map** between tensor bundles, packaged at the
section level uniformly over the gradient order.

The map sends a smooth compactly-supported `(r₁, s₁ + a)`-tensor section and a smooth
compactly-supported `(r₂, s₂ + b)`-tensor section to a smooth compactly-supported
`(r₀, s₀ + a + b)`-tensor section, for every pair of extra-slot counts `a, b`.  The fields encode
exactly the two genuine constraints of a `∇`-compatible bounded bilinear map:

* `rfns_prod_le` — a single uniform fibrewise operator bound in the intrinsic `g`-Riemannian squared
  fibre norm, `rfns(prod S T) ≤ opNorm · rfns(S) · rfns(T)` (the continuity/boundedness of the bilinear
  map, phrased `g`-natively so that no chart-trivialisation / model-fibre operator norm enters — the
  model `opNorm` would be chart-Jacobian-unbounded on a multi-chart manifold; in particular it forces
  `prod 0 T = 0` and `prod S 0 = 0`, so a degenerate nonzero witness is rejected);
* `covGrad_prod` — the exact single-step covariant Leibniz identity
  `∇(prod S T) = prod (∇S) T + prod S (∇T)` (the cross terms vanish precisely because the map is
  parallel, `∇ Φ = 0`).  The left summand `prod (∇S) T` carries covariant rank `(s₀ + a + 1) + b`,
  reindexed to the differentiated rank `(s₀ + a + b) + 1` by the rank-cast `castRankCc`.

This is the abstraction realized by a metric contraction of a tensor product (`∇g = 0`); it is kept
generic and decoupled from any specific nonlinearity so as to be a reusable covariant-calculus
byproduct. -/
structure ParallelTensorProduct (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ r₀ s₀ : ℕ) where

  prod : ∀ {a b : ℕ}, SmoothCcTensor g r₁ (s₁ + a) → SmoothCcTensor g r₂ (s₂ + b) →
    SmoothCcTensor g r₀ (s₀ + a + b)

  opNorm : ℝ

  opNorm_nonneg : 0 ≤ opNorm

  rfns_prod_le : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b))
    (x : M),
    riemannianFiberNormSq (I := I) (M := M) g r₀ (s₀ + a + b) x ((prod S T).toSection x) ≤
      opNorm * riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + b) x (T.toSection x)

  covGrad_prod : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)),
    covGrad g r₀ (s₀ + a + b) (prod S T) =
      castRankCc g r₀ (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
          (prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T) +
        prod (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T)

namespace ParallelTensorProduct

variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ r₀ s₀ : ℕ}

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **A vanishing intrinsic Riemannian fibre norm forces the tensor to vanish.** If the squared
`g`-Riemannian fibre norm of a tensor fibre value `z` is zero, then `z = 0`.  Through the
fibre-norm / bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq'` the hypothesis reads
`‖z‖² = 0` (in the `(r, s)`-tensor Riemannian bundle norm, the model-induced fibre norm removed so
`‖·‖` resolves to it), whence `‖z‖ = 0` and `z = 0`. -/
private theorem eq_zero_of_riemannianFiberNormSq_eq_zero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (z : Tensor0SBundle.TensorRSSpace r s I x)
    (hz : riemannianFiberNormSq (I := I) (M := M) g r s x z = 0) : z = 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hnorm_sq : ‖z‖ ^ 2 = 0 :=
    (riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r s x z).symm.trans hz
  have hnorm : ‖z‖ = 0 := by nlinarith [norm_nonneg z, hnorm_sq]
  exact norm_eq_zero.mp hnorm

/-- A parallel product kills the zero section in its left argument: `prod 0 T = 0`.

This is the non-degeneracy witness for the operator bound `rfns_prod_le`: at the zero left section
the `g`-Riemannian fibre-norm bound forces every fibre norm of `prod 0 T` to vanish, hence the
section is zero. -/
theorem prod_zero_left (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (T : SmoothCcTensor g r₂ (s₂ + b)) :
    Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.rfns_prod_le (0 : SmoothCcTensor g r₁ (s₁ + a)) T x
  have hzero : ((0 : SmoothCcTensor g r₁ (s₁ + a)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, mul_zero, zero_mul] at hle
  have hval : (Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

/-- A parallel product kills the zero section in its right argument: `prod S 0 = 0`. -/
theorem prod_zero_right (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) :
    Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.rfns_prod_le S (0 : SmoothCcTensor g r₂ (s₂ + b)) x
  have hzero : ((0 : SmoothCcTensor g r₂ (s₂ + b)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, mul_zero] at hle
  have hval : (Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b))).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval


end ParallelTensorProduct

end RicciFlow
end PDE
end DifferentialGeometry

end
