import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.Multilinear.Tensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The covariant tensor-product / contraction Leibniz rule, and `∇(metric power) = 0`

This file builds the general **covariant tensor-product Leibniz rule** for the
`(0, s)` covariant derivative `nabla0SFun`, and uses it together with metric
compatibility (`nabla_metric_zero`) to prove that every tensor power of the metric
`(0, 2)` tensor is `∇`-parallel.

These are the tensor-layer primitives requested as "Step A" behind the `k = 1`
Bernstein–Bando–Shi producer (`Geometry/Flow/RicciFlow/Evolution/IteratedNablaRmTower.md`):
the genuinely missing covariant product/contraction rule from which the rank-`r`
index lowering/raising parallelism would follow.

## What is proved

* `nabla0SFun_product_eval` — the **evaluated tensor-product Leibniz rule**: for two
  smooth covariant tensor fields `A : (0, s)` and `B : (0, q)`, with realized
  covariant derivatives `nablaA`/`nablaB`, the `(0, s + q)` covariant derivative of
  the tensor product `A ⊗ B` evaluated on smooth slots splits as

  `∇(A ⊗ B)(slots) = ∇A(X :: slots₀..ₛ₋₁) · B(slotsₛ..) + A(slots₀..ₛ₋₁) · ∇B(X :: slotsₛ..)`.

  This is the concrete-evaluation analogue of the bundled `∇(A ⊗ B) = ∇A ⊗ B + A ⊗ ∇B`;
  it is derived from `nabla0SFun_eval_smooth_slots` (Definition 14.5) and the scalar
  product rule `extDerivFun_mul`, exactly mirroring `nabla_smul_metric` (the `s = 0`
  scalar-multiple case) but for a genuine second tensor factor.

* `nabla_product_zero_of_zero` — if both factors are `∇`-parallel (`∇A = 0`,
  `∇B = 0`), then so is their tensor product: `∇(A ⊗ B) = 0`.

* `metricPow` — the `r`-fold tensor power `g^{⊗r}` of the metric `(0, 2)` tensor, a
  `(0, 2r)` tensor field (`metricPow 0 = unit (0,0)`-tensor, `metricPow (r+1) =
  g ⊗ metricPow r`).

* `nabla_metricPow_zero` — `∇(g^{⊗r}) = 0` for a metric-compatible connection, by
  induction on `r` from `nabla_metric_zero` and `nabla_product_zero_of_zero`.

The `metricPow` section is exactly the (0, 2r) "metric-power section" that the
all-index lowering map contracts a mixed `(r, s)`-tensor against (each upper slot
paired against one metric factor); its parallelism is the metric-compatibility
content behind the rank-`r` lowering/raising intertwiner.
-/

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Scalar product rule (kept local to avoid a heavy operator-layer import) -/

/-- Directional derivative product rule for scalar functions.  A local copy of the
private `extDerivFun_mul_real`, built from the bundle-level
`fromTangentSpace_mfderiv_smul_apply`, to keep this file below the scalar-operator
layer. -/
private theorem extDerivFun_mul_real
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    extDerivFun (I := I) (fun y : M => f y * h y) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x := by
  change extDerivFun (I := I) (f • h) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := h) hf hh v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hprod

/-- `castAdd q a` and `natAdd s b` have disjoint images (first vs. last block). -/
private theorem castAdd_natAdd_ne {s q : ℕ} (a : Fin s) (b : Fin q) :
    Fin.castAdd q a ≠ Fin.natAdd s b := by
  intro h
  have hcoe := Fin.val_eq_of_eq h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hcoe
  omega

/-! ## The evaluated tensor-product Leibniz rule -/

/-- Splitting a `Fin (s + q)` slot tuple into the first `s` and last `q` slots:
the value of a tensor product `A ⊗ B` on a slot tuple `V` is `A(V ∘ castAdd) · B(V ∘ natAdd)`.
This is the section-level form of `product_fun_apply`. -/
theorem tensor0SField_product_apply {s q : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (x : M) (V : Fin (s + q) -> TangentSpace I x) :
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) x V =
      A x (V ∘ Fin.castAdd q) * B x (V ∘ Fin.natAdd s) := by
  change Bundle.continuousMultilinearMap.product_fun (A x) (B x) V = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply]

/-- **The evaluated tensor-product Leibniz rule for `nabla0SFun`.**

For smooth covariant tensor fields `A : (0, s)`, `B : (0, q)` with covariant
derivatives realized by `nablaA`, `nablaB`, and smooth tangent slots `V`, the
`(0, s + q)` covariant derivative of the tensor product `A ⊗ B` evaluated on `V`
splits as the sum of the two single-factor derivatives:

`∇(A ⊗ B)(V) = ∇A(X :: V∘castAdd) · B(V∘natAdd) + A(V∘castAdd) · ∇B(X :: V∘natAdd)`,

with `X` the differentiation direction.  Derived purely from the concrete derivation
rule `nabla0SFun_eval_smooth_slots` and the scalar product rule. -/
theorem nabla0SFun_product_eval {s q : ℕ}
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      q cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + q) cov X
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) x)
        (fun a : Fin (s + q) => V a x) =
      nablaA x (Fin.cons (X x) (fun a : Fin s => V (Fin.castAdd q a) x)) *
          B x (fun a : Fin q => V (Fin.natAdd s a) x) +
        A x (fun a : Fin s => V (Fin.castAdd q a) x) *
          nablaB x (Fin.cons (X x) (fun a : Fin q => V (Fin.natAdd s a) x)) := by
  classical
  -- Slot fields restricted to the first `s` and last `q` blocks.
  let Vfirst : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (Fin.castAdd q a)
  let Vlast : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (Fin.natAdd s a)
  -- The product field.
  let P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + q) :=
    MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B
  -- Scalar evaluation fields for the two factors.
  let af : M -> Real := fun y : M => A y (fun a : Fin s => Vfirst a y)
  let bf : M -> Real := fun y : M => B y (fun a : Fin q => Vlast a y)
  -- Expand the product `nabla0SFun` through the concrete derivation rule.
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V P x
  -- The product field's scalar evaluation is `af · bf`, pointwise.
  have hPeval : ∀ y : M, P y (fun a : Fin (s + q) => V a y) = af y * bf y := by
    intro y
    dsimp only [P]
    change Bundle.continuousMultilinearMap.product_fun (A y) (B y)
      (fun a : Fin (s + q) => V a y) = _
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    rfl
  -- Differentiability of the two scalar factor fields at `x`.
  have haf : MDifferentiableAt I 𝓘(Real, Real) af x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) A Vfirst x).mdifferentiableAt
      (by simp)
  have hbf : MDifferentiableAt I 𝓘(Real, Real) bf x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) B Vlast x).mdifferentiableAt
      (by simp)
  -- The directional-derivative part: product rule on `af · bf`.
  have hderiv :
      extDerivFun (I := I) (fun y : M => P y (fun a : Fin (s + q) => V a y)) x (X x) =
        af x * extDerivFun (I := I) bf x (X x) +
          extDerivFun (I := I) af x (X x) * bf x := by
    rw [show (fun y : M => P y (fun a : Fin (s + q) => V a y)) =
        fun y : M => af y * bf y from funext hPeval]
    exact extDerivFun_mul_real (I := I) (f := af) (h := bf) (X x) haf hbf
  -- Rewrite the two factor derivatives via their realizations.
  have hAeval := TotalNabla0SRealizes.eval_smooth_slots (I := I) hA X Vfirst x
  have hBeval := TotalNabla0SRealizes.eval_smooth_slots (I := I) hB X Vlast x
  -- The correction sum over `Fin (s + q)` slots splits over the two blocks; the
  -- first-block corrections rebuild `(∇A)·B`, the last-block corrections rebuild
  -- `A·(∇B)`, via `product_fun`'s slot split.
  rw [heval]
  -- Evaluate the correction sum.  Each term is `P x (update V a (cov Vₐ X))`.
  have hsplit :
      (∑ a : Fin (s + q),
          P x (Function.update (fun b : Fin (s + q) => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) =
        (∑ a : Fin s,
            A x (Function.update (fun b : Fin s => Vfirst b x) a
              ((cov (fun p : M => Vfirst a p) x) (X x)))) * bf x +
          af x *
            (∑ a : Fin q,
              B x (Function.update (fun b : Fin q => Vlast b x) a
                ((cov (fun p : M => Vlast a p) x) (X x)))) := by
    rw [Fin.sum_univ_add]
    congr 1
    · -- First block: slot index `Fin.castAdd q a`, updates only the `A` factor.
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      dsimp only [P]
      change Bundle.continuousMultilinearMap.product_fun (A x) (B x)
        (Function.update (fun b : Fin (s + q) => V b x) (Fin.castAdd q a)
          ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x))) = _
      rw [Bundle.continuousMultilinearMap.product_fun_apply]
      congr 1
      · -- `A` argument: the updated first block.
        congr 1
        funext b
        simp only [Function.comp_apply]
        by_cases hb : b = a
        · subst hb
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hb,
            Function.update_of_ne (fun h => hb (Fin.castAdd_injective _ _ h))]
      · -- `B` argument: the last block is untouched by a first-block update.
        congr 1
        funext b
        simp only [Function.comp_apply, Vlast]
        rw [Function.update_of_ne (fun h => by
          exact absurd h.symm (castAdd_natAdd_ne a b))]
    · -- Last block: slot index `Fin.natAdd s a`, updates only the `B` factor.
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      dsimp only [P]
      change Bundle.continuousMultilinearMap.product_fun (A x) (B x)
        (Function.update (fun b : Fin (s + q) => V b x) (Fin.natAdd s a)
          ((cov (fun p : M => V (Fin.natAdd s a) p) x) (X x))) = _
      rw [Bundle.continuousMultilinearMap.product_fun_apply]
      congr 1
      · -- `A` argument: the first block is untouched by a last-block update.
        congr 1
        funext b
        simp only [Function.comp_apply, Vfirst]
        rw [Function.update_of_ne (fun h => by
          exact absurd h (castAdd_natAdd_ne b a))]
      · -- `B` argument: the updated last block.
        congr 1
        funext b
        simp only [Function.comp_apply]
        by_cases hb : b = a
        · subst hb
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hb,
            Function.update_of_ne (fun h => hb (Fin.natAdd_injective _ _ h))]
  rw [hderiv, hsplit]
  -- Now rewrite `extDerivFun af`, `extDerivFun bf` through the factor realizations.
  have hAd : extDerivFun (I := I) af x (X x) =
      nablaA x (Fin.cons (X x) (fun a : Fin s => Vfirst a x)) +
        ∑ a : Fin s,
          A x (Function.update (fun b : Fin s => Vfirst b x) a
            ((cov (fun p : M => Vfirst a p) x) (X x))) := by
    have := hAeval
    -- `nablaA (X :: Vfirst) = extDerivFun af - Σ corrections`.
    rw [show af = fun y : M => A y (fun a : Fin s => Vfirst a y) from rfl]
    linarith [this]
  have hBd : extDerivFun (I := I) bf x (X x) =
      nablaB x (Fin.cons (X x) (fun a : Fin q => Vlast a x)) +
        ∑ a : Fin q,
          B x (Function.update (fun b : Fin q => Vlast b x) a
            ((cov (fun p : M => Vlast a p) x) (X x))) := by
    have := hBeval
    rw [show bf = fun y : M => B y (fun a : Fin q => Vlast a y) from rfl]
    linarith [this]
  rw [hAd, hBd]
  -- Close by ring; the correction sums cancel against the realization corrections.
  simp only [af, bf, Vfirst, Vlast]
  ring

/-- **Tensor product of parallel tensors is parallel.**  If `A` and `B` have
vanishing covariant derivative (witnessed by the zero `(s+1)`- and `(q+1)`-tensor
fields), then their tensor product `A ⊗ B` has vanishing covariant derivative. -/
theorem nabla_product_zero_of_zero {s q : ℕ}
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)))
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      q cov B
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (q + 1))) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + q + 1)) := by
  classical
  intro X x slots
  -- Realize each slot by a smooth section agreeing with it at `x`.
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin (s + q), V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  -- The realized derivative tuple at slot `Fin.cons (X x) slots`.
  have hslots : (fun a : Fin (s + q) => V a x) = slots := funext hV
  -- The product Leibniz, with both factor derivatives `= 0`.
  have hmain :=
    nabla0SFun_product_eval (I := I) cov A B
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1))
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (q + 1))
      hA hB X V x
  -- The LHS of the realization is the product `nabla0SFun` on `Fin.cons (X x) slots`.
  change (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + q + 1)) x (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + q) cov X
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) x slots
  rw [show slots = (fun a : Fin (s + q) => V a x) from hslots.symm]
  rw [hmain]
  -- Both summands vanish: the zero field evaluates to `0`.
  simp

/-! ## The metric power and its parallelism -/

variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The `r`-fold tensor power `g^{⊗r}` of the metric `(0, 2)` tensor, a `(0, 2r)`
tensor field.  `metricPow g 0` is the unit `(0, 0)`-tensor field (the constant `1`),
and `metricPow g (r + 1) = g ⊗ metricPow g r`. -/
noncomputable def metricPow
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    (r : ℕ) -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 * r)
  | 0 => Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞))
  | (r + 1) => by
      have hcast : 2 + 2 * r = 2 * (r + 1) := by ring
      exact hcast ▸
        MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 * r)
          (metricTensorField (I := I) g) (metricPow g r)

/-- The unit `(0, 0)`-tensor field is `∇`-parallel. -/
private theorem nabla_one0_zero
    [IsManifold I 2 M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      0 cov
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)))
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1) := by
  classical
  intro X x slots
  -- `one0 = fromScalarField (const 1)`; its (direct-coercion) evaluation is the
  -- constant `1`, whose directional derivative is `0`, and there are no covariant
  -- slots to correct.
  let V : Fin 0 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => Fin.elim0 a
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞))) x
  have hone_apply : ∀ (p : M) (w : Fin 0 -> TangentSpace I p),
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞))) p w = (1 : Real) := by
    intro p w
    change ContinuousMultilinearMap.constOfIsEmpty Real
      (fun _ : Fin 0 => TangentSpace I p) (1 : Real) w = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hconst :
      extDerivFun (I := I)
          (fun p : M =>
            (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞))) p (fun a : Fin 0 => V a p))
          x (X x) = 0 := by
    rw [show (fun p : M =>
        (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞))) p (fun a : Fin 0 => V a p)) =
          fun _ : M => (1 : Real) from funext fun p => hone_apply p _]
    simp [extDerivFun]
  change (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) x (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 cov X
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞))) x slots
  have hslots0 : slots = (fun a : Fin 0 => V a x) := by
    funext a; exact Fin.elim0 a
  rw [hslots0]
  rw [heval, hconst]
  simp

/-- Transport of the `∇ = 0` realization across a rank equality `h : s₁ = s₂`. -/
private theorem totalNabla0SRealizes_zero_cast
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s₁)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s₁ cov A
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s₁ + 1))) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s₂ cov (h ▸ A)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s₂ + 1)) := by
  subst h
  exact hA

/-- **The metric power is `∇`-parallel.**  For a metric-compatible connection, the
`r`-fold tensor power `g^{⊗r}` of the metric has vanishing covariant derivative,
`∇(g^{⊗r}) = 0`.  Proved by induction on `r`: the base is the parallel unit
`(0, 0)`-tensor, and the step is the tensor-product Leibniz `∇(g ⊗ g^{⊗r}) =
∇g ⊗ g^{⊗r} + g ⊗ ∇(g^{⊗r}) = 0` with `∇g = 0` (`nabla_metric_zero`) and the
induction hypothesis. -/
theorem nabla_metricPow_zero
    [IsManifold I 2 M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g) :
    ∀ r : ℕ,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (2 * r) cov (metricPow (I := I) g r)
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (2 * r + 1)) := by
  intro r
  induction r with
  | zero =>
    -- `metricPow g 0 = one0`.
    exact nabla_one0_zero (I := I) cov
  | succ r ih =>
    -- `metricPow g (r+1) = hcast ▸ (g ⊗ metricPow g r)`.
    have hg : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (metricTensorField (I := I) g)
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) :=
      zero_realizes_metric (I := I) cov g hmc
    have hprod :=
      nabla_product_zero_of_zero (I := I) cov
        (metricTensorField (I := I) g) (metricPow (I := I) g r) hg ih
    have hcast : 2 + 2 * r = 2 * (r + 1) := by ring
    have htrans :=
      totalNabla0SRealizes_zero_cast (I := I) cov hcast
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 * r)
          (metricTensorField (I := I) g) (metricPow (I := I) g r))
        hprod
    -- Identify `metricPow g (r+1)` with the cast product.
    have hmp : metricPow (I := I) g (r + 1) =
        hcast ▸ MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 2 * r)
          (metricTensorField (I := I) g) (metricPow (I := I) g r) := rfl
    rw [hmp]
    exact htrans

/-- **The covariant contraction-Leibniz against the metric power.**  For a smooth
`(0, s)` tensor field `A` with covariant derivative realized by `nablaA`, the
covariant derivative of the metric-power contraction `A ⊗ g^{⊗r}` evaluated on
smooth slots is the all-derivative-on-`A` term

`∇(A ⊗ g^{⊗r})(V) = ∇A(X :: V∘castAdd) · g^{⊗r}(V∘natAdd)`,

i.e. the metric-power factor passes through `∇` untouched (its own derivative
vanishes, `nabla_metricPow_zero`).  This is the `(0, s)`-against-metric form of the
general contraction-Leibniz: differentiating a metric contraction only hits the
non-metric factor.  Specialization of `nabla0SFun_product_eval` with the parallel
second factor `g^{⊗r}`. -/
theorem nabla0SFun_metricPow_contraction_eval {s r : ℕ}
    [IsManifold I 2 M] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin (s + 2 * r) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2 * r) cov X
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := 2 * r)
          A (metricPow (I := I) g r)) x)
        (fun a : Fin (s + 2 * r) => V a x) =
      nablaA x (Fin.cons (X x) (fun a : Fin s => V (Fin.castAdd (2 * r) a) x)) *
        (metricPow (I := I) g r) x (fun a : Fin (2 * r) => V (Fin.natAdd s a) x) := by
  rw [nabla0SFun_product_eval (I := I) cov A (metricPow (I := I) g r)
    nablaA
    (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (2 * r + 1))
    hA (nabla_metricPow_zero (I := I) cov g hmc r) X V x]
  -- The second summand `A ⊗ ∇(g^{⊗r})` vanishes since `∇(g^{⊗r}) = 0`.
  simp

end

end Tensor0SBundle
