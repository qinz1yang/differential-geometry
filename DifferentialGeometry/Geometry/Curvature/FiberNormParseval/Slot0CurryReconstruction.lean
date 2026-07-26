import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSplitParsevalBridge

/-!
# Slot-`0` uncurry reconstruction of a `(0, s+1)` covariant tensor field

The slot-`0` Parseval *fibre-norm* decomposition `riemannianFiberNormSq_succ_eq_sum_slot0Curry`
(in `SlotSplitParsevalBridge`) only goes FORWARD: it reads the fibre norm of a `(0, s+1)`-tensor
`T` as the frame-sum of the fibre norms of its slot-`0` curries `slot0Curry g x s e K₀ T a`. This
file supplies the INVERSE — the field-level reconstruction of `T` itself from its slot-`0` curried
slices, so that an identity known on each slot-`0` slice lifts to the full `(0, s+1)` field.

The point is Parseval applied in the *leading* (slot-`0`) covariant slot: for a `g`-orthonormal
tangent frame `e`, a tangent vector `w` expands as `w = ∑ₐ ⟨e a, w⟩_g • e a`, and the curry
`tensor0S_curry s x T` is a continuous linear map in the slot-`0` argument, so

```
T (Fin.cons w m) = ∑ₐ ⟨e a, w⟩_g • (tensor0S_curry s x T (e a)) m .
```

## Main results

* `tensor0S_uncurry_cons_eval_of_expansion` — the abstract (metric-free) core: if the slot-`0`
  argument `w` expands as `w = ∑ₐ c a • e a` for scalars `c`, then evaluating `T` at
  `Fin.cons w m` equals the `c`-weighted frame sum of the slot-`0` curries evaluated at `m`.
* `tensor0S_uncurry_cons_eval_orthonormal` — the `g`-orthonormal-frame specialization, with the
  weights the inner products `⟨e a, w⟩_g`.
* `tensorRS_section_uncurry_cons_eval_slot0Curry` — the same reconstruction phrased on the
  `(0, s+1)`-tensor `T : TensorRSSpace 0 (s+1)` via the on-disk `slot0Curry` wrapper, evaluated at
  the unit `(0, 0)` covector, matching the convention of
  `riemannianFiberNormSq_succ_eq_sum_slot0Curry`.
* `tensorRS_section_eq_sum_slot0Curry_uncurry` — the existence-packaged headline: there is a
  `g`-orthonormal frame in which the unit-section of `T` reconstructs as the inner-product-weighted
  frame sum of the slot-`0` curried slices, matching the frame conventions
  (`coframeS`/`dualTensorFrameS`/the witness) used by the forward fibre-norm decomposition.
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

/-- **Abstract slot-`0` uncurry reconstruction.** If the slot-`0` argument `w` of a
`(0, s+1)`-tensor `T` expands over a (finite) family `e` of tangent vectors as
`w = ∑ₐ c a • e a`, then evaluating `T` at the `cons`-tuple `Fin.cons w m` equals the
`c`-weighted frame sum of the slot-`0` curries `tensor0S_curry s x T (e a)` evaluated at `m`.

This is the field-level inverse of the slot-`0` curry: the slot-`0` argument is read by
linearity of the curry continuous linear map. No metric or orthonormality is needed here — only
the linear expansion of `w` in the family `e`. -/
theorem tensor0S_uncurry_cons_eval_of_expansion
    {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (c : Fin n → ℝ) (e : Fin n → TangentSpace I x)
    (w : TangentSpace I x) (hw : w = ∑ a : Fin n, c a • e a)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel T (Fin.cons w m) =
      ∑ a : Fin n, c a • Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (e a)) m := by
  classical
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s) (b := x) T w m]
  rw [hw]
  rw [map_sum (tensor0S_curry (I := I) (M := M) s x T) (fun a => c a • e a) Finset.univ]
  rw [show Tensor0SSpace.toModel
        (∑ a : Fin n, tensor0S_curry (I := I) (M := M) s x T (c a • e a)) =
      ∑ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (c a • e a)) from by
    rw [← Tensor0SSpace.toModelL_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Tensor0SSpace.toModelL_apply]]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [(tensor0S_curry (I := I) (M := M) s x T).map_smul (c a) (e a)]
  rw [Tensor0SSpace.toModel_smul (c a) (tensor0S_curry (I := I) (M := M) s x T (e a))]
  rw [ContinuousMultilinearMap.smul_apply]

/-- **Slot-`0` uncurry reconstruction in a `g`-orthonormal frame.** For a tangent frame `e`
whose Parseval expansion `hv_expand` holds (`u = ∑ₐ ⟨e a, u⟩_g • e a` for every `u`), the
slot-`0` argument of a `(0, s+1)`-tensor `T` reconstructs from the slot-`0` curries with the
inner-product weights:
`T (Fin.cons w m) = ∑ₐ ⟨e a, w⟩_g • (tensor0S_curry s x T (e a)) m`. -/
theorem tensor0S_uncurry_cons_eval_orthonormal
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel T (Fin.cons w m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x T (e a)) m :=
  tensor0S_uncurry_cons_eval_of_expansion (I := I) (M := M) T
    (fun a => g.inner x (e a) w) e w (hv_expand w) m

/-- **The slot-`0` curry slice, evaluated at the unit `(0, 0)` covector, is the raw slot-`0`
curry of the unit-section.** For `ωK := coframeS g x 0 e K₀` (the empty-index coframe covector,
whose scalar value is `1`), `(slot0Curry g x s e K₀ T a) ωK` equals
`tensor0S_curry s x ((T : CLM) ωK) (e a)`. This is the on-disk `slot0Curry` wrapper unwound to
the raw `tensor0S_curry` on the unit-section `(T : CLM) ωK`. -/
lemma slot0Curry_coframeS_eq_tensor0S_curry
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    (slot0Curry (I := I) (M := M) g x s e K₀ T a :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
        (coframeS (I := I) (M := M) g x 0 e K₀) =
      tensor0S_curry (I := I) (M := M) s x
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) (e a) := by
  classical
  rw [slot0Curry_apply (I := I) (M := M) g x s e K₀ T a
    (coframeS (I := I) (M := M) g x 0 e K₀)]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      (coframeS (I := I) (M := M) g x 0 e K₀) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      coframeS_apply (I := I) (M := M) g x 0 e K₀]
    simp
  rw [hscalar, one_smul]
  rfl

/-- **Slot-`0` uncurry reconstruction of the unit-section, via the `slot0Curry` wrapper.** For a
`(0, s+1)`-tensor `T : TensorRSSpace 0 (s+1)` and a `g`-orthonormal frame `e` (Parseval expansion
`hv_expand`), the unit-section `(T : CLM) (coframeS g x 0 e K₀)` reconstructs from the on-disk
slot-`0` curried slices `slot0Curry g x s e K₀ T a` (each evaluated at the unit covector) with the
inner-product weights:
`((T : CLM) ωK) (Fin.cons w m) = ∑ₐ ⟨e a, w⟩_g • ((slot0Curry g x s e K₀ T a) ωK) m`,
where `ωK := coframeS g x 0 e K₀`. This matches the frame/coframe conventions of the forward
`riemannianFiberNormSq_succ_eq_sum_slot0Curry`. -/
theorem tensorRS_section_uncurry_cons_eval_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (T : TensorRSSpace 0 (s + 1) I x)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) (Fin.cons w m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
      (coframeS (I := I) (M := M) g x 0 e K₀)) e hv_expand w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_coframeS_eq_tensor0S_curry (I := I) (M := M) g x s e K₀ T a]

/-- **Existence-packaged slot-`0` uncurry reconstruction of a `(0, s+1)`-tensor.** There is a
`g`-orthonormal tangent frame `e` (with `n = Module.finrank` directions, the same witness frame
used by the forward `riemannianFiberNormSq_succ_eq_sum_slot0Curry`) in which every
`(0, s+1)`-tensor `T` reconstructs from its slot-`0` curried slices `tensor0S_curry s x T (e a)`:
for every slot-`0` direction `w` and every tail tuple `m`,
`T (Fin.cons w m) = ∑ₐ ⟨e a, w⟩_g • (tensor0S_curry s x T (e a)) m`.

This is the field-level inverse of the slot-`0` curry: an identity known on each slot-`0` slice
`tensor0S_curry s x T (e a)` lifts to the full `(0, s+1)` field `T`. It is the genuinely-missing
reconstruction direction (the on-disk slot-`0` API runs only forward, to the fibre norm). -/
theorem tensor0S_eq_sum_slot0_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : Tensor0SSpace (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel T (Fin.cons w m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            (tensor0S_curry (I := I) (M := M) s x T (e a)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun T w m => ?_⟩
  exact tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g T e hv_expand w m

/-- **Existence-packaged slot-`0` uncurry reconstruction, via the on-disk `slot0Curry` wrapper.**
The same reconstruction as `tensor0S_eq_sum_slot0_uncurry`, phrased on the unit-section
`(T : CLM) ωK` (`ωK := coframeS g x 0 e K₀`) of a `(0, s+1)`-tensor `T : TensorRSSpace 0 (s+1)`
through the on-disk `slot0Curry g x s e K₀ T a` slices, matching the frame/coframe conventions of
`riemannianFiberNormSq_succ_eq_sum_slot0Curry`. -/
theorem tensorRS_section_eq_sum_slot0Curry_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
              (coframeS (I := I) (M := M) g x 0 e K₀)) (Fin.cons w m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
              (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  refine ⟨n, e, fun k => k.elim0, hn, horth, fun T w m => ?_⟩
  exact tensorRS_section_uncurry_cons_eval_slot0Curry (I := I) (M := M) g s x e
    (fun k => k.elim0) hv_expand T w m

end Connection
end Integral
end DifferentialGeometry
