import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGrad
import DifferentialGeometry.Integral.L2.PointwiseInner.SlotPermutation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The metric-isometry bridge for the section-level covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the `H^1` pre-Hilbert structure on smooth
compactly-supported `(r, s)`-tensor sections pairs the covariant derivatives
of two sections through the inverse-Gram-weighted double sum
`tensorCovDerivPointwiseInner`. This file proves that this inverse-Gram-weighted
pairing coincides, pointwise, with the genuine one-rank-higher tensor
pointwise inner product `tensorInnerPointwise g r (s + 1)` of the section-level
covariant gradients `covGrad g r s S` and `covGrad g r s T`.

## Main result

* `tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad` — for all smooth
  compactly-supported `(r, s)`-tensor sections `S`, `T` and every point `x`,

  `tensorCovDerivPointwiseInner g r s S T x
    = tensorInnerPointwise g r (s + 1) x
        (TensorRSSpace.toModel ((covGrad g r s S).toSection x))
        (TensorRSSpace.toModel ((covGrad g r s T).toSection x))`.

## Strategy

Both sides are the same metric contraction of the same data, written with the
`r + s + 1` covariant slots in a different order.

The covariant gradient `covGrad g r s S` is the `(r, s + 1)`-tensor whose extra
covariant slot — placed as the *leftmost* of the `s + 1` covariant slots, by the
gradient-bundle convention `covGradBundleEquiv_apply_eval` — carries the
differentiation direction. The mixed pointwise inner product
`tensorInnerPointwise g r (s + 1)` first lowers the `r` upper slots through the
metric (`lowerAllUpperIndices`, placing the `r` lowered slots *before* the
`s + 1` covariant slots), then contracts all `r + (s + 1)` covariant slots via
the inverse Gram matrix of `g`.

Consequently, in the lowered covariant `(0, r + (s + 1))`-tensor the
differentiation slot sits at index `r`: after the `r` lowered upper slots and
before the `s` genuine covariant slots. Splitting the index `r` slot out of the
`(0, r + (s + 1))` contraction — via the explicit closed form
`tensorInnerPointwise_0s_eq_sum` and the tuple-splitting equivalence
`Fin.insertNthEquiv` at position `r` — produces exactly the inverse-Gram weight
`(G⁻¹)ᵢⱼ` of the differentiation direction together with the inverse-Gram-weighted
`(0, r + s)` contraction of the directional covariant derivatives, i.e. the
summand of `tensorCovDerivPointwiseInner`.

The proof therefore expands both sides to explicit inverse-Gram-weighted sums
and reconciles them by the bijective slot reindexing `Fin.insertNthEquiv`; no
new predicate hypothesis is introduced and the identity holds unconditionally.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Evaluation of the model coercion of an `(r, s)`-tensor. For a tensor
`T : TensorRSSpace r s I x` and a model `(0, r)`-tensor `Dm`, the
`(0, s)`-model tensor `(TensorRSSpace.toModel T) Dm` is the model coercion of
`T` applied to the fibre `(0, r)`-tensor `Tensor0SSpace.ofModel Dm`. -/
private lemma tensorRSSpace_toModel_apply
    (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (Dm : Tensor0SModel r ℝ E) :
    (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E from
        TensorRSSpace.toModel T) Dm =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T)
          (Tensor0SSpace.ofModel Dm)) :=
  rfl

/-- **Model-fibre evaluation of the covariant gradient.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the model coercion of the
section value `(covGrad g r s S).toSection x` — an `(r, s + 1)`-model tensor —
evaluated on a model `(0, r)`-tensor `Dm` and a `Fin (s + 1)`-tuple `v`, equals
the model coercion of the directional covariant derivative
`tensorCovDerivAt g r s S x (v 0)` evaluated on `Dm` and the tail of `v`. -/
private lemma covGrad_toModel_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M)
    (Dm : Tensor0SModel r ℝ E) (v : Fin (s + 1) → E) :
    (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) Dm v =
      (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S x (v 0)))
        Dm (Matrix.vecTail v) := by
  change (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E from
      TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) Dm v = _
  rw [tensorRSSpace_toModel_apply (I := I) r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) Dm]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s S x
        (Tensor0SSpace.ofModel Dm) v]
  rw [tensorRSSpace_toModel_apply (I := I) r s x
        (tensorCovDerivAt (I := I) (M := M) g r s S x (v 0)) Dm]

/-- The index of the differentiation slot inside the lowered covariant
`(0, r + (s + 1))`-tensor: it sits at position `r`, after the `r` lowered upper
slots and before the `s` genuine covariant slots. -/
private def diffSlot (r s : ℕ) : Fin (r + (s + 1)) :=
  ⟨r, by omega⟩

/-- The differentiation slot is the `natAdd`-image of the leftmost covariant
slot: `lowerAllUpperIndices` maps the covariant block to the `natAdd r`
positions, and `covGrad` places the differentiation direction at the leftmost
of the `s + 1` covariant slots. -/
private lemma natAdd_zero_eq_diffSlot (r s : ℕ) :
    (Fin.natAdd r (0 : Fin (s + 1)) : Fin (r + (s + 1))) = diffSlot r s := by
  apply Fin.ext
  simp [diffSlot, Fin.natAdd]

/-- The omit-index-`r` embedding sends the `r` upper-slot positions
(`castAdd s` into `Fin (r + s)`) to the `r` upper-slot positions
(`castAdd (s + 1)` into `Fin (r + (s + 1))`): both blocks occupy positions
`0, …, r - 1`, which lie below the differentiation slot. -/
private lemma diffSlot_succAbove_castAdd (r s : ℕ) (a : Fin r) :
    (diffSlot r s).succAbove (Fin.castAdd s a) = Fin.castAdd (s + 1) a := by
  apply Fin.ext
  have hcond : (Fin.castSucc (Fin.castAdd s a) : Fin (r + (s + 1)))
      < diffSlot r s := by
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_castAdd, diffSlot]
    exact a.isLt
  rw [Fin.succAbove, if_pos hcond]
  simp only [Fin.val_castSucc, Fin.val_castAdd]

/-- The omit-index-`r` embedding sends the `s` covariant-slot positions
(`natAdd r` into `Fin (r + s)`) to the `s` genuine covariant-slot positions
(`natAdd r ∘ Fin.succ` into `Fin (r + (s + 1))`): the `Fin (r + s)` covariant
block occupies positions `r, …, r + s - 1`, which lie at or above the
differentiation slot, so each is shifted up by one. -/
private lemma diffSlot_succAbove_natAdd (r s : ℕ) (a : Fin s) :
    (diffSlot r s).succAbove (Fin.natAdd r a) =
      Fin.natAdd r (Fin.succ a) := by
  apply Fin.ext
  have hcond : ¬ (Fin.castSucc (Fin.natAdd r a) : Fin (r + (s + 1)))
      < diffSlot r s := by
    rw [Fin.lt_def, not_lt]
    simp only [Fin.val_castSucc, Fin.val_natAdd, diffSlot]
    omega
  rw [Fin.succAbove, if_neg hcond]
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

/-- **The lowered covariant gradient on an `insertNth` basis tuple.** For a
smooth compactly-supported `(r, s)`-tensor section `S`, an index `k : Fin n`
and a slot-index tuple `i : Fin (r + s) → Fin n`, the lowered covariant gradient
`lowerAllUpperIndices g r (s + 1) x (TensorRSSpace.toModel (covGrad g r s S))`,
evaluated on the basis tuple indexed by `Fin.insertNth (diffSlot r s) k i`,
equals the lowered directional covariant derivative
`lowerAllUpperIndices g r s x (TensorRSSpace.toModel (∇_{eₖ} S))` evaluated on
the basis tuple indexed by `i`. -/
private lemma lower_covGrad_insertNth_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (i : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s S).toSection x))
        (fun a : Fin (r + (s + 1)) => (chartModelBasis E)
          ((Fin.insertNth (diffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S x
            ((chartModelBasis E) k)))
        (fun a : Fin (r + s) => (chartModelBasis E) (i a)) := by
  classical
  set I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E) :=
    Fin.insertNth (diffSlot r s) k i with hI'
  rw [lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  have hdir : (chartModelBasis E) (I' (Fin.natAdd r (0 : Fin (s + 1)))) =
      (chartModelBasis E) k := by
    rw [natAdd_zero_eq_diffSlot, hI', Fin.insertNth_apply_same]
  have hupper : (fun a : Fin r =>
        (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))) =
      (fun a : Fin r => (chartModelBasis E) (i (Fin.castAdd s a))) := by
    funext a
    show (chartModelBasis E) (I' (Fin.castAdd (s + 1) a)) =
      (chartModelBasis E) (i (Fin.castAdd s a))
    rw [← diffSlot_succAbove_castAdd r s a, hI', Fin.insertNth_apply_succAbove]
  have hcov : Matrix.vecTail
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j))) =
      (fun a : Fin s => (chartModelBasis E) (i (Fin.natAdd r a))) := by
    funext a
    change (chartModelBasis E) (I' (Fin.natAdd r (Fin.succ a))) =
      (chartModelBasis E) (i (Fin.natAdd r a))
    rw [← diffSlot_succAbove_natAdd r s a, hI', Fin.insertNth_apply_succAbove]
  rw [covGrad_toModel_apply (I := I) (M := M) g r s S x
        (separableFormAt (I := I) (M := M) g x r
          (fun a : Fin r => (chartModelBasis E) (I' (Fin.castAdd (s + 1) a))))
        (fun j : Fin (s + 1) => (chartModelBasis E) (I' (Fin.natAdd r j)))]
  rw [hdir, hupper, hcov]

/-- Splitting the inverse-Gram product at the differentiation slot. For
slot-index tuples `i j : Fin (r + s) → Fin n` and differentiation indices
`k l : Fin n`, the product of inverse-Gram entries over all `r + (s + 1)`
covariant slots of the `insertNth`-assembled tuples equals the inverse-Gram
weight `(G⁻¹)ₖₗ` of the differentiation direction times the product over the
remaining `r + s` slots. -/
private lemma gramInv_prod_insertNth_split
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (k l : Fin (Module.finrank ℝ E))
    (i j : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (diffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (diffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ k l *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a) := by
  rw [show (∏ a : Fin (r + (s + 1)),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (diffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)
          ((Fin.insertNth (diffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) a)) =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹
          ((Fin.insertNth (diffSlot r s) k i : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (diffSlot r s))
          ((Fin.insertNth (diffSlot r s) l j : Fin (r + (s + 1)) →
            Fin (Module.finrank ℝ E)) (diffSlot r s)) *
        ∏ a : Fin (r + s),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹
            ((Fin.insertNth (diffSlot r s) k i : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((diffSlot r s).succAbove a))
            ((Fin.insertNth (diffSlot r s) l j : Fin (r + (s + 1)) →
              Fin (Module.finrank ℝ E)) ((diffSlot r s).succAbove a))
      from Fin.prod_univ_succAbove _ (diffSlot r s)]
  rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-- Reindexing a sum over `Fin (r + (s + 1))`-indexed slot tuples through the
tuple-splitting equivalence `Fin.insertNthEquiv` at the differentiation slot:
the sum equals the iterated sum over a differentiation index `k : Fin n` and a
`Fin (r + s)`-indexed slot tuple `i`, of the summand at the assembled tuple
`Fin.insertNth (diffSlot r s) k i`. -/
private lemma sum_reindex_diffSlot (r s : ℕ)
    (F : (Fin (r + (s + 1)) → Fin (Module.finrank ℝ E)) → ℝ) :
    ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
          F (Fin.insertNth (diffSlot r s) k i) := by
  have h1 : ∑ I' : Fin (r + (s + 1)) → Fin (Module.finrank ℝ E), F I' =
      ∑ ki : Fin (Module.finrank ℝ E) ×
          (Fin (r + s) → Fin (Module.finrank ℝ E)),
        F (Fin.insertNth (diffSlot r s) ki.1 ki.2) :=
    (Equiv.sum_comp
      (Fin.insertNthEquiv (fun _ : Fin (r + (s + 1)) => Fin (Module.finrank ℝ E))
        (diffSlot r s)) F).symm
  rw [h1, Fintype.sum_prod_type]

/-- **The metric-isometry bridge for the section-level covariant gradient.**

For a closed smooth Riemannian manifold `(M, g)` and smooth compactly-supported
`(r, s)`-tensor sections `S`, `T`, the inverse-Gram-weighted pairing of the
covariant derivatives of `S` and `T` — the gradient term
`tensorCovDerivPointwiseInner` of the `H^1` inner product — equals, at every
point `x`, the genuine one-rank-higher tensor pointwise inner product
`tensorInnerPointwise g r (s + 1)` of the section-level covariant gradients
`covGrad g r s S` and `covGrad g r s T`.

Both sides are the same metric contraction of the covariant derivatives,
written with the `r + (s + 1)` covariant slots in a different order: the mixed
inner product `tensorInnerPointwise g r (s + 1)` places the differentiation
slot at index `r`, after the `r` lowered upper slots; the gradient term
`tensorCovDerivPointwiseInner` separates the differentiation contraction as an
outer inverse-Gram-weighted double sum. The identity holds unconditionally — no
extra hypothesis on `S`, `T`, or `x`. -/
theorem tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s S).toSection x))
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s T).toSection x)) := by
  classical
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv_def
  set lowS : Fin (Module.finrank ℝ E) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    fun k => lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) k)))
    with hlowS_def
  set lowT : Fin (Module.finrank ℝ E) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
    fun l => lowerAllUpperIndices (I := I) (M := M) g r s x
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s T x ((chartModelBasis E) l)))
    with hlowT_def
  set common : ℝ :=
    ∑ k : Fin (Module.finrank ℝ E),
      ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
            Ginv k l *
              ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                (lowS k) (fun a => (chartModelBasis E) (i a)) *
                  (lowT l) (fun a => (chartModelBasis E) (j a)))
    with hcommon_def
  have hLHS : tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      common := by
    rw [tensorCovDerivPointwiseInner_def]
    have hexpand : ∀ k l : Fin (Module.finrank ℝ E),
        Ginv k l *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T x
                  ((chartModelBasis E) l))) =
          ∑ i : Fin (r + s) → Fin (Module.finrank ℝ E),
            ∑ j : Fin (r + s) → Fin (Module.finrank ℝ E),
              Ginv k l *
                ((∏ a : Fin (r + s), Ginv (i a) (j a)) *
                  (lowS k) (fun a => (chartModelBasis E) (i a)) *
                    (lowT l) (fun a => (chartModelBasis E) (j a))) := by
      intro k l
      rw [show tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T x
                  ((chartModelBasis E) l))) =
            tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (lowS k) (lowT l) from rfl]
      rw [tensorInnerPointwise_0s_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => hexpand k l))]
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  have hRHS : tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s S).toSection x))
        (TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g r s T).toSection x)) = common := by
    rw [show tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
            (TensorRSSpace.toModel
              ((covGrad (I := I) (M := M) g r s S).toSection x))
            (TensorRSSpace.toModel
              ((covGrad (I := I) (M := M) g r s T).toSection x)) =
          tensorInnerPointwise_0s (I := I) (M := M) (r + (s + 1)) g x
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((covGrad (I := I) (M := M) g r s S).toSection x)))
            (lowerAllUpperIndices (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel
                ((covGrad (I := I) (M := M) g r s T).toSection x)))
        from rfl]
    rw [tensorInnerPointwise_0s_eq_sum]
    rw [sum_reindex_diffSlot]
    rw [hcommon_def]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sum_reindex_diffSlot]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [gramInv_prod_insertNth_split (I := I) (M := M) g x r s k l i j]
    rw [lower_covGrad_insertNth_basis (I := I) (M := M) g r s S x k i]
    rw [lower_covGrad_insertNth_basis (I := I) (M := M) g r s T x l j]
    rw [hlowS_def, hlowT_def]
    ring
  rw [hLHS, hRHS]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
