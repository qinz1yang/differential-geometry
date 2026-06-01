import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Slot-permutation invariance of the pointwise tensor inner product

Let `M` be a smooth finite-dimensional manifold modelled on a real normed
space `E` equipped with a smooth Riemannian metric `g`. The pointwise inner
product `tensorInnerPointwise_0s` on covariant `(0, s)`-tensors (defined in
`PointwiseInner.Defs`) curries off one model slot at a time and contracts
through the inverse Gram matrix of `g(x)` on the fixed model-space basis
`chartModelBasis E`.

This file establishes that `tensorInnerPointwise_0s` is invariant under a
**simultaneous permutation of its `Fin s` covariant slots**: for any
`σ : Equiv.Perm (Fin s)`,

```
tensorInnerPointwise_0s s g x (S.domDomCongr σ) (T.domDomCongr σ)
  = tensorInnerPointwise_0s s g x S T,
```

where `ContinuousMultilinearMap.domDomCongr σ` reindexes the domain slots.

The proof goes through an explicit closed form: unfolding the recursion
fully expresses the pointwise inner product as a double sum over
slot-index tuples `i j : Fin s → Fin (Module.finrank ℝ E)`,

```
tensorInnerPointwise_0s s g x S T
  = ∑ i, ∑ j, (∏ a, (G(x))⁻¹ (i a) (j a))
                * S (e ∘ i) * T (e ∘ j),
```

with `e = chartModelBasis E`. In this form, simultaneously precomposing both
tuples by `σ` is a bijective reindexing of the double sum, leaving it
unchanged. The headline is therefore an `=`-identity, with the adjacent
transposition and block-move (cyclic) cases following as immediate
instances of the general permutation statement.
-/

noncomputable section

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Collapse a sum over a leading index together with a tail tuple into a
single sum over `(s+1)`-tuples, using the head/tail splitting equivalence
`Fin.consEquiv`. -/
private lemma sum_cons_collapse {n s : ℕ}
    (F : Fin n → (Fin s → Fin n) → ℝ)
    (G : (Fin (s + 1) → Fin n) → ℝ)
    (hF : ∀ p i, F p i = G (Fin.cons p i)) :
    ∑ p : Fin n, ∑ i : Fin s → Fin n, F p i =
      ∑ I : Fin (s + 1) → Fin n, G I := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
        (fun pi => F pi.1 pi.2) G
        (fun pi => by
          change F pi.1 pi.2 = G ((Fin.consEquiv _) pi)
          rw [hF]; rfl)]
  rw [Fintype.sum_prod_type]

/-- **Explicit closed form** of the pointwise `(0, s)` inner product.
Unfolding the recursion fully, the pointwise inner product is a double sum
over slot-index tuples `i j : Fin s → Fin (Module.finrank ℝ E)`: each term
is the product of the inverse-Gram-matrix entries `(G(x))⁻¹ (i a) (j a)`
over the slots `a`, weighted by the tensor components `S (e ∘ i)` and
`T (e ∘ j)` evaluated on the corresponding basis tuples, where
`e = chartModelBasis E`. -/
theorem tensorInnerPointwise_0s_eq_sum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S T =
      ∑ i : Fin s → Fin (Module.finrank ℝ E),
        ∑ j : Fin s → Fin (Module.finrank ℝ E),
          (∏ a : Fin s,
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a)) *
            S (fun a => (chartModelBasis E) (i a)) *
              T (fun a => (chartModelBasis E) (j a)) := by
  classical
  induction s with
  | zero =>
      rw [tensorInnerPointwise_0s_zero_arity]
      rw [Finset.sum_eq_single (fun a => Fin.elim0 a)]
      · rw [Finset.sum_eq_single (fun a => Fin.elim0 a)]
        · have hSarg :
              (fun a => (chartModelBasis E)
                  ((fun a : Fin 0 => Fin.elim0 a) a)) =
                (fun i : Fin 0 => Fin.elim0 i) :=
            funext fun a => Fin.elim0 a
          have hempty_prod :
              (∏ a : Fin 0,
                  (gramMatrixAt (I := I) (M := M) g x)⁻¹
                    ((fun a : Fin 0 => Fin.elim0 a) a)
                    ((fun a : Fin 0 => Fin.elim0 a) a)) = 1 :=
            Finset.prod_of_isEmpty _
          rw [hempty_prod, hSarg, one_mul]
        · intro b _ hb
          exact absurd (funext fun a => Fin.elim0 a) hb
        · intro hb
          exact absurd (Finset.mem_univ _) hb
      · intro b _ hb
        exact absurd (funext fun a => Fin.elim0 a) hb
      · intro hb
        exact absurd (Finset.mem_univ _) hb
  | succ s ih =>
      set n := Module.finrank ℝ E with hn_def
      rw [tensorInnerPointwise_0s_succ]
      have hstep :
          ∀ p q : Fin n,
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ p q *
                tensorInnerPointwise_0s (I := I) (M := M) s g x
                  (S.curryLeft ((chartModelBasis E) p))
                  (T.curryLeft ((chartModelBasis E) q))
              = ∑ i : Fin s → Fin n,
                  ∑ j : Fin s → Fin n,
                    (∏ a : Fin (s + 1),
                        (gramMatrixAt (I := I) (M := M) g x)⁻¹
                          ((Fin.cons p i : Fin (s + 1) → Fin n) a)
                          ((Fin.cons q j : Fin (s + 1) → Fin n) a)) *
                      S (fun a => (chartModelBasis E)
                          ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                        T (fun a => (chartModelBasis E)
                            ((Fin.cons q j : Fin (s + 1) → Fin n) a)) := by
        intro p q
        rw [ih, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        have hS :
            (S.curryLeft ((chartModelBasis E) p))
                (fun a => (chartModelBasis E) (i a))
              = S (fun a => (chartModelBasis E)
                  ((Fin.cons p i : Fin (s + 1) → Fin n) a)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext a
          refine Fin.cases ?_ ?_ a
          · simp
          · intro k; simp
        have hT :
            (T.curryLeft ((chartModelBasis E) q))
                (fun a => (chartModelBasis E) (j a))
              = T (fun a => (chartModelBasis E)
                  ((Fin.cons q j : Fin (s + 1) → Fin n) a)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext a
          refine Fin.cases ?_ ?_ a
          · simp
          · intro k; simp
        have hprod :
            (∏ a : Fin (s + 1),
                (gramMatrixAt (I := I) (M := M) g x)⁻¹
                  ((Fin.cons p i : Fin (s + 1) → Fin n) a)
                  ((Fin.cons q j : Fin (s + 1) → Fin n) a))
              = (gramMatrixAt (I := I) (M := M) g x)⁻¹ p q *
                  ∏ a : Fin s,
                    (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a) := by
          rw [Fin.prod_univ_succ]
          simp
        rw [hS, hT, hprod]
        ring
      rw [Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun q _ => hstep p q))]
      rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]
      have hcollapse_inner :
          ∀ (p : Fin n) (i : Fin s → Fin n),
            ∑ q : Fin n,
              ∑ j : Fin s → Fin n,
                (∏ a : Fin (s + 1),
                    (gramMatrixAt (I := I) (M := M) g x)⁻¹
                      ((Fin.cons p i : Fin (s + 1) → Fin n) a)
                      ((Fin.cons q j : Fin (s + 1) → Fin n) a)) *
                  S (fun a => (chartModelBasis E)
                      ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                    T (fun a => (chartModelBasis E)
                        ((Fin.cons q j : Fin (s + 1) → Fin n) a))
              = ∑ J : Fin (s + 1) → Fin n,
                  (∏ a : Fin (s + 1),
                      (gramMatrixAt (I := I) (M := M) g x)⁻¹
                        ((Fin.cons p i : Fin (s + 1) → Fin n) a) (J a)) *
                    S (fun a => (chartModelBasis E)
                        ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                      T (fun a => (chartModelBasis E) (J a)) := by
        intro p i
        refine sum_cons_collapse
          (fun q j =>
            (∏ a : Fin (s + 1),
                (gramMatrixAt (I := I) (M := M) g x)⁻¹
                  ((Fin.cons p i : Fin (s + 1) → Fin n) a)
                  ((Fin.cons q j : Fin (s + 1) → Fin n) a)) *
              S (fun a => (chartModelBasis E)
                  ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                T (fun a => (chartModelBasis E)
                    ((Fin.cons q j : Fin (s + 1) → Fin n) a)))
          _ ?_
        intro q j
        rfl
      rw [Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun i _ => hcollapse_inner p i))]
      have hcollapse_outer :
          ∑ p : Fin n,
            ∑ i : Fin s → Fin n,
              ∑ J : Fin (s + 1) → Fin n,
                (∏ a : Fin (s + 1),
                    (gramMatrixAt (I := I) (M := M) g x)⁻¹
                      ((Fin.cons p i : Fin (s + 1) → Fin n) a) (J a)) *
                  S (fun a => (chartModelBasis E)
                      ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                    T (fun a => (chartModelBasis E) (J a))
              = ∑ K : Fin (s + 1) → Fin n,
                  ∑ J : Fin (s + 1) → Fin n,
                    (∏ a : Fin (s + 1),
                        (gramMatrixAt (I := I) (M := M) g x)⁻¹ (K a) (J a)) *
                      S (fun a => (chartModelBasis E) (K a)) *
                        T (fun a => (chartModelBasis E) (J a)) := by
        refine sum_cons_collapse
          (fun p i =>
            ∑ J : Fin (s + 1) → Fin n,
              (∏ a : Fin (s + 1),
                  (gramMatrixAt (I := I) (M := M) g x)⁻¹
                    ((Fin.cons p i : Fin (s + 1) → Fin n) a) (J a)) *
                S (fun a => (chartModelBasis E)
                    ((Fin.cons p i : Fin (s + 1) → Fin n) a)) *
                  T (fun a => (chartModelBasis E) (J a)))
          _ ?_
        intro p i
        rfl
      rw [hcollapse_outer]

/-- **Slot-permutation invariance of the pointwise `(0, s)` inner
product.** Reindexing the `Fin s` covariant slots of *both* arguments by
the same permutation `σ` via `ContinuousMultilinearMap.domDomCongr` leaves
the pointwise inner product unchanged. In the explicit closed form, the
double sum over slot-index tuples is reindexed by the bijection
`i ↦ i ∘ σ`, which is the same bijection in both arguments; this is a
bijective reindexing of the sum, so the value is invariant. -/
theorem tensorInnerPointwise_0s_domDomCongr
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (σ : Equiv.Perm (Fin s))
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.domDomCongr σ) (T.domDomCongr σ) =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S T := by
  classical
  set n := Module.finrank ℝ E with hn_def
  rw [tensorInnerPointwise_0s_eq_sum, tensorInnerPointwise_0s_eq_sum]
  have hterm :
      ∀ i j : Fin s → Fin n,
        (∏ a : Fin s,
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a)) *
          (S.domDomCongr σ) (fun a => (chartModelBasis E) (i a)) *
            (T.domDomCongr σ) (fun a => (chartModelBasis E) (j a))
          = (∏ a : Fin s,
              (gramMatrixAt (I := I) (M := M) g x)⁻¹
                ((i ∘ σ) a) ((j ∘ σ) a)) *
            S (fun a => (chartModelBasis E) ((i ∘ σ) a)) *
              T (fun a => (chartModelBasis E) ((j ∘ σ) a)) := by
    intro i j
    have hprod :
        (∏ a : Fin s,
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a))
          = ∏ a : Fin s,
              (gramMatrixAt (I := I) (M := M) g x)⁻¹
                ((i ∘ σ) a) ((j ∘ σ) a) := by
      symm
      exact Equiv.prod_comp σ
        (fun a => (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a))
    have hS :
        (S.domDomCongr σ) (fun a => (chartModelBasis E) (i a))
          = S (fun a => (chartModelBasis E) ((i ∘ σ) a)) := by
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rfl
    have hT :
        (T.domDomCongr σ) (fun a => (chartModelBasis E) (j a))
          = T (fun a => (chartModelBasis E) ((j ∘ σ) a)) := by
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rfl
    rw [hprod, hS, hT]
  rw [Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => hterm i j))]
  have hreindex :
      ∀ K : (Fin s → Fin n) → ℝ,
        ∑ i : Fin s → Fin n, K (i ∘ σ) = ∑ i : Fin s → Fin n, K i := by
    intro K
    exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n)))
      (fun i => K (i ∘ σ)) K (fun i => by congr 1)
  rw [show (∑ i : Fin s → Fin n, ∑ j : Fin s → Fin n,
              (∏ a : Fin s,
                  (gramMatrixAt (I := I) (M := M) g x)⁻¹
                    ((i ∘ σ) a) ((j ∘ σ) a)) *
                S (fun a => (chartModelBasis E) ((i ∘ σ) a)) *
                  T (fun a => (chartModelBasis E) ((j ∘ σ) a)))
        = ∑ i : Fin s → Fin n,
            (fun i' => ∑ j : Fin s → Fin n,
                (∏ a : Fin s,
                    (gramMatrixAt (I := I) (M := M) g x)⁻¹
                      (i' a) ((j ∘ σ) a)) *
                  S (fun a => (chartModelBasis E) (i' a)) *
                    T (fun a => (chartModelBasis E) ((j ∘ σ) a)))
              (i ∘ σ) from rfl]
  rw [hreindex
        (fun i' => ∑ j : Fin s → Fin n,
            (∏ a : Fin s,
                (gramMatrixAt (I := I) (M := M) g x)⁻¹
                  (i' a) ((j ∘ σ) a)) *
              S (fun a => (chartModelBasis E) (i' a)) *
                T (fun a => (chartModelBasis E) ((j ∘ σ) a)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact hreindex
    (fun j => (∏ a : Fin s,
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ (i a) (j a)) *
      S (fun a => (chartModelBasis E) (i a)) *
        T (fun a => (chartModelBasis E) (j a)))

/-- **Adjacent / arbitrary transposition** special case of slot-permutation
invariance: swapping two covariant slots `a b : Fin s` of both arguments
simultaneously leaves the pointwise `(0, s)` inner product unchanged. -/
theorem tensorInnerPointwise_0s_domDomCongr_swap
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (a b : Fin s)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.domDomCongr (Equiv.swap a b)) (T.domDomCongr (Equiv.swap a b)) =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S T :=
  tensorInnerPointwise_0s_domDomCongr (I := I) (M := M) g x s
    (Equiv.swap a b) S T

/-- **Block-move (cyclic) special case** of slot-permutation invariance.
`Fin.cycleRange b : Equiv.Perm (Fin s)` is the cyclic permutation rotating
`{0, 1, …, b}` by one step (sending `b ↦ 0`, `k ↦ k + 1` for `k < b`, and
fixing the slots beyond `b`). Reindexing the covariant slots of both
arguments of the pointwise `(0, s)` inner product by `Fin.cycleRange b`
leaves the inner product unchanged.

This is the slot move used downstream when a distinguished slot must be
brought to the front past a block of earlier slots. -/
theorem tensorInnerPointwise_0s_domDomCongr_cycleRange
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (b : Fin s)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.domDomCongr (Fin.cycleRange b))
        (T.domDomCongr (Fin.cycleRange b)) =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S T :=
  tensorInnerPointwise_0s_domDomCongr (I := I) (M := M) g x s
    (Fin.cycleRange b) S T

/-- **Reverse-rotation block-move special case** of slot-permutation
invariance. `finRotate s : Equiv.Perm (Fin s)` is the full cyclic rotation
sending `k ↦ k + 1` (and the last slot to `0`). Reindexing the covariant
slots of both arguments of the pointwise `(0, s)` inner product by
`finRotate s` leaves the inner product unchanged. -/
theorem tensorInnerPointwise_0s_domDomCongr_finRotate
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.domDomCongr (finRotate s)) (T.domDomCongr (finRotate s)) =
      tensorInnerPointwise_0s (I := I) (M := M) s g x S T :=
  tensorInnerPointwise_0s_domDomCongr (I := I) (M := M) g x s
    (finRotate s) S T

end L2
end Integral
end DifferentialGeometry

end
