import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval

/-!
# Slot-`0` Parseval decomposition of the intrinsic `(0, s+1)`-tensor fibre norm

For a smooth Riemannian metric `g`, the intrinsic Riemannian fibre norm squared of a
`(0, s+1)` covariant tensor `T` at a point `x` decomposes, over the `g`-orthonormal tangent
frame direction in the first (slot `0`) covariant slot, into the frame-sum of the
slot-`s` fibre norms of the slot-`0` curries of `T`:

```
riemannianFiberNormSq g 0 (s+1) x T
  = ∑ (a : Fin (finrank ℝ E)), riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a)
```

where `slot0Curry g x s e K₀ T a` is the `(0, s)`-tensor obtained from `T` by evaluating
its underlying continuous linear map on the empty covector, currying off the first slot at
the `a`-th vector `e a` of the same orthonormal frame `e` used internally by
`riemannianFiberNormSq`, and repackaging the result as a `TensorRSSpace 0 s I x`.

This is Parseval applied along the slot-`0` frame direction: the multi-index `J : Fin (s+1)
→ Fin n` indexing the dual-tensor-frame components of `T` splits via `Fin.consEquiv` into a
head index `a : Fin n` (the slot-`0` frame direction) and a tail index `J' : Fin s → Fin n`,
and the curry identity `tensor0S_curry_apply_eval` identifies the corresponding frame
components.

## Main definitions

* `slot0Curry` — the slot-`0` curry of a `(0, s+1)`-tensor at a frame vector, as a
  `(0, s)`-tensor.

## Main results

* `slot0Curry_apply` — the defining evaluation formula for `slot0Curry`.
* `fiberNormSqComponent_slot0Curry` — the per-component slot-split identity: the
  slot-`(s+1)` frame component of `T` at `Fin.cons a J'` equals the slot-`s` frame
  component of `slot0Curry … a` at `J'`.
* `riemannianFiberNormSq_succ_eq_sum_slot0Curry` — the headline frame-sum decomposition.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def slot0Curry
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (tensor0S_curry (I := I) (M := M) s x
      ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k)))))
      (e a))

lemma slot0Curry_apply
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (slot0Curry (I := I) (M := M) g x s e K₀ T a :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        (tensor0S_curry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K₀ k)))))
          (e a)) := by
  change ((tensor00Scalar (I := I) (M := M) x).smulRight
    (tensor0S_curry (I := I) (M := M) s x
      ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k)))))
      (e a))) τ = _
  rw [ContinuousLinearMap.smulRight_apply]

lemma fiberNormSqComponent_slot0Curry
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) (J' : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) T n e K₀
        (Fin.cons a J') =
      fiberNormSqComponent (I := I) (M := M) g x 0 s
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) n e K₀ J' := by
  classical
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK
  set B : Tensor0SSpace (s + 1) I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x) ωK with hB
  rw [slot0Curry_apply (I := I) (M := M) g x s e K₀ T a ωK, ← hB]
  have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
    rw [hωK,
      show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
        coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
      tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      coframeS_apply (I := I) (M := M) g x 0 e K₀]
    simp
  rw [hscalar, one_smul]
  have hcurry := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (n := s) (b := x) B (e a) (fun k : Fin s => e (J' k))
  have htuple : (fun k : Fin (s + 1) => e ((Fin.cons a J' : Fin (s + 1) → Fin n) k)) =
      Fin.cons (e a) (fun k : Fin s => e (J' k)) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · simp
    · intro j; simp
  change (B (fun k : Fin (s + 1) => e ((Fin.cons a J' : Fin (s + 1) → Fin n) k)) : ℝ) =
    (tensor0S_curry (I := I) (M := M) s x B (e a)) (fun k : Fin s => e (J' k))
  rw [show (B (fun k : Fin (s + 1) => e ((Fin.cons a J' : Fin (s + 1) → Fin n) k)) : ℝ) =
      Tensor0SSpace.toModel B (Fin.cons (e a) (fun k : Fin s => e (J' k))) from by
    rw [htuple]; rfl]
  rw [show ((tensor0S_curry (I := I) (M := M) s x B (e a)) (fun k : Fin s => e (J' k)) : ℝ) =
      Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) s x B (e a))
        (fun k : Fin s => e (J' k)) from rfl]
  rw [hcurry]

theorem riemannianFiberNormSq_succ_eq_sum_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s e K₀ T a) := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J := by
    intro S; rfl
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
    intro S; rfl
  refine ⟨n, e, fun k => k.elim0, hn_def, ?_⟩
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x (s + 1) e hreprSucc T K₀]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
        (fun (pr : Fin n × (Fin s → Fin n)) =>
          (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) T n e K₀
            (Fin.cons pr.1 pr.2)) ^ 2)
        (fun J : Fin (s + 1) → Fin n =>
          (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) T n e K₀ J) ^ 2)
        (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) K₀]
  refine Finset.sum_congr rfl (fun J' _ => ?_)
  rw [fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ T a J']

end Connection
end Integral
end DifferentialGeometry
