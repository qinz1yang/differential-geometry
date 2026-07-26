import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSplitParsevalBridge

/-!
# Slot-`0` directional-slice fibre-norm domination for the intrinsic `(0, s+1)`-tensor norm

The forward slot-`0` Parseval decomposition `riemannianFiberNormSq_succ_eq_sum_slot0Curry`
(in `SlotSplitParsevalBridge`) reads the intrinsic Riemannian fibre norm squared of a
`(0, s+1)` covariant tensor `T` at a point `x` as the frame-sum, over the `g`-orthonormal
tangent frame direction in the first (slot `0`) slot, of the slot-`s` fibre norms of its
slot-`0` curries:

```
riemannianFiberNormSq g 0 (s+1) x T
  = ∑ (a : Fin n), riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a) .
```

Because every summand on the right is a non-negative fibre norm squared, *each individual*
slot-`0` slice is bounded by the whole: plugging a single (unit) orthonormal-frame direction
`e a` into the new (slot `0`) covariant slot of `T` cannot increase the Riemannian fibre
norm. This is Cauchy–Schwarz / Bessel in the contracted slot — the slice fixes one index to
a unit basis direction, so its `(0, s)`-fibre-norm² is `≤` the full `(0, s+1)`-fibre-norm².

## Main results

* `riemannianFiberNormSq_slot0Curry_le` — for the witness `g`-orthonormal frame of the
  forward decomposition, every slot-`0` curried slice is fibre-dominated by the whole:
  `riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a)
     ≤ riemannianFiberNormSq g 0 (s+1) x T`.
* `exists_riemannianFiberNormSq_slot0Curry_le` — the existence-packaged interface returning
  the witness frame data (with its orthonormality) together with the per-direction
  domination, so a consumer slicing `∇S` along a `g`-orthonormal moving frame reduces a
  directional-slice fibre bound to the full gradient fibre norm.
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

/-- **Frame-parametric slot-`0` Parseval decomposition of the `(0, s+1)` fibre norm.** For
*any* tangent frame `e` (with `n` directions) that represents the rank-`s` and rank-`(s+1)`
fibre norms as the frame double-sum (`hreprS`, `hreprSucc` — in particular every `g`-orthonormal
frame, via `tangent_orthonormalBasisS_witness`), the intrinsic `(0, s+1)` fibre norm of a tensor
`T` is the frame sum, over the slot-`0` direction, of the slot-`s` fibre norms of its slot-`0`
curries:
```
riemannianFiberNormSq g 0 (s+1) x T
  = ∑ (a : Fin n), riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a) .
```

This generalizes `riemannianFiberNormSq_succ_eq_sum_slot0Curry` (whose frame is the internal
`stdOrthonormalBasis`) to a frame supplied by the caller — so a consumer slicing along its own
`g`-orthonormal moving frame (e.g. `smoothOrthoFrame`) can run the decomposition in that frame. -/
theorem riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J)
    (T : TensorRSSpace 0 (s + 1) I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
      ∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (slot0Curry (I := I) (M := M) g x s e K₀ T a) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x (s + 1) e
    hreprSucc T K₀]
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

/-- **Frame-parametric slot-`0` directional-slice fibre-norm domination.** For *any* tangent
frame `e` representing the rank-`s` and rank-`(s+1)` fibre norms (`hreprS`, `hreprSucc` — in
particular every `g`-orthonormal frame), every slot-`0` curried slice of a `(0, s+1)`-tensor `T`
along a frame direction `e a` is fibre-dominated by the whole `(0, s+1)` fibre norm:
```
riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a)
  ≤ riemannianFiberNormSq g 0 (s+1) x T .
```

This is the per-direction reading of Parseval in the slot-`0` frame `e`: the full fibre norm is
the frame sum of the (non-negative) slice fibre norms, so each single slice is dominated by the
whole. With `e` supplied by the caller, a consumer slicing the covariant gradient `∇S` along its
own `g`-orthonormal moving frame `e` (e.g. `smoothOrthoFrame`) obtains, by plugging
`T := (∇S).toSection x`, that the slot-`0` slice of `∇S` in direction `e a` is bounded by the
full gradient fibre norm — the shared prerequisite of the moving-frame genuine-curvature-trace
`rfns(∇S)`-order fibre bound. -/
theorem riemannianFiberNormSq_slot0Curry_le_of_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc T]
  refine Finset.single_le_sum (f := fun a : Fin n =>
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a))
    (fun b _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
    (Finset.mem_univ a)

/-- **Slot-`0` directional-slice fibre-norm domination (witness-frame form).** There is a
`g`-orthonormal tangent frame `e` (the same witness frame as the forward decomposition
`riemannianFiberNormSq_succ_eq_sum_slot0Curry`, with `n = Module.finrank` directions) in
which every slot-`0` curried slice of a `(0, s+1)`-tensor `T` is bounded by the full
`(0, s+1)` fibre norm: for every frame index `a`,
```
riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a)
  ≤ riemannianFiberNormSq g 0 (s+1) x T .
```

This is the per-direction reading of Parseval in the slot-`0` orthonormal frame: the full
fibre norm is the frame sum of the (non-negative) slice fibre norms, so each single slice is
dominated by the whole. The slice fixes the leading covariant index to the unit direction
`e a`; its `(0, s)`-fibre-norm² therefore cannot exceed the full `(0, s+1)`-fibre-norm². -/
theorem riemannianFiberNormSq_slot0Curry_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      ∀ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  obtain ⟨n, e, K₀, hn, hsum⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, K₀, hn, fun a => ?_⟩
  rw [hsum]
  refine Finset.single_le_sum (f := fun a : Fin n =>
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a))
    (fun b _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
    (Finset.mem_univ a)

/-- **Existence-packaged slot-`0` directional-slice fibre-norm domination.** There is a
`g`-orthonormal tangent frame `e` (with `n = Module.finrank` directions) — orthonormal in the
explicit `δ`-form `g(e i, e j) = if i = j then 1 else 0`, hence each `e a` a unit direction —
in which every slot-`0` curried slice of a `(0, s+1)`-tensor `T` is fibre-dominated by the
whole `(0, s+1)` fibre norm:
```
riemannianFiberNormSq g 0 s x (slot0Curry g x s e K₀ T a)
  ≤ riemannianFiberNormSq g 0 (s+1) x T .
```

This is the directly-consumable interface: a consumer slicing the covariant gradient `∇S`
along a `g`-orthonormal moving frame obtains, by plugging `T := (∇S).toSection x`, that each
unit-direction slice of `∇S` is bounded by the full gradient fibre norm
`riemannianFiberNormSq g 0 (s+1) x ((∇S).toSection x)` — the single shared prerequisite of
the moving-frame genuine-curvature-trace `rfns(∇S)`-order fibre bound. The orthonormality
witness is returned so the consumer can match the frame against its own moving orthonormal
frame and exploit the unit-length Gram scalars `g(e a, e a) = 1`. -/
theorem exists_riemannianFiberNormSq_slot0Curry_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
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
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have horthb : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horthb i j
    rw [he_def, ← hinner_eq (eob i) (eob j)]
    exact hite
  refine ⟨n, e, fun k => k.elim0, hn_def, horth, fun a => ?_⟩
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
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
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc T a

end Connection
end Integral
end DifferentialGeometry
