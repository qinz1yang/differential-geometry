import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SBochnerSplit
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerLeibniz
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SPartialEval
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

/-!
# Discharging the hypothesis of the general Bochner Laplacian split

`Tensor/RSTensor/FiberMetric/Tensor0SBochnerSplit.lean` proves the rank-uniform
intrinsic Bochner Laplacian split `tensorNormBochnerSplit`

`Δ‖T‖² = 2⟨ΔT, T⟩ + 2‖∇T‖²`

sorry-free **except** for one standing hypothesis: the pointwise Hessian product
rule of the norm, `TensorNormHessianProductInBasis`,

`Hess‖T‖²(eᵢ,eⱼ) = 2(⟨∇²T(eᵢ,eⱼ,·),T⟩ + ⟨∇T(eᵢ,·),∇T(eⱼ,·)⟩)`.

This file **derives that rule at general rank** from the now-proved rank-uniform
covariant inner-product Leibniz (`Tensor0SInnerLeibniz.lean`,
`inner0S_nabla`/`normSq0S_nabla`), discharging the hypothesis and yielding the
hypothesis-free general Bochner Laplacian split `tensorNormBochnerSplit_mc`.

## Method

The proof is the rank-`s` generalisation of the `(0,2)` producer stack
`du_norm02`/`freeze02_deriv`/`hess_norm02`/`second_norm02_mc`
(`Geometry/Curvature/Bochner/BochnerTensor.lean`).

* `du_norm0S` — the first-order rule `∇_W‖T‖² = 2⟨∇_W T,T⟩` (the rank-uniform
  `du_norm02`); it is just `normSq0S_nabla`.
* `nabla_partialEval0S` — the **only nontrivial realization step**, the rank-`s`
  generalisation of `freeze02_deriv`'s `hBderiv`: the covariant derivative of the
  first-slot-frozen field `y ↦ (∇T)(Y_y, ·)` (= `tensor0SPartialEval ∇T Y`) is
  `∇²T(X,Y,·) + (∇T)(∇_X Y,·)`.  The frozen field's bundled smoothness is
  `contMDiff_tensor0SPartialEval` (`Tensor0SPartialEval.lean`); the realization
  combinatorics mirror `freeze02_deriv` over `Fin s` instead of `Fin 2`.
* `freeze0S_deriv` — applies the second Leibniz step `inner0S_nabla` to
  `(tensor0SPartialEval ∇T Y, T)` and substitutes `nabla_partialEval0S`, giving
  the rank-`s` `freeze02_deriv`.
* `hess_norm0S` — assembles the Hessian via `nablaDuAt`/`HessianRealizesNablaDuAt`
  (the rank-uniform `hess_norm02`), producing `TensorNormHessianProductInBasis`.

`#print axioms` for every public theorem is `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

-- File-local instances to ensure typeclass resolution finds the normed structure on
-- the variable-rank `Tensor0SModel`, resolving the instance diamond documented in
-- `Geometry/Metric/TensorInner/Tensor0SRiemannian.lean`.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

/-! ## The first-slot-frozen covariant-derivative field -/

/-- The first-slot partial evaluation of a smooth `(0,s+1)` field `nablaT`
(thought of as `∇T`) against a smooth tangent field `Y`, packaged as a smooth
`(0,s)` tensor field: at `y`, `(partialEval0SField nablaT Y) y` is the `(0,s)`
tensor `v ↦ nablaT y (Y y :: v)`.  This is the rank-`s` generalisation of the
`(0,2)` `freeze02Field`; its smoothness is `contMDiff_tensor0SPartialEval`. -/
noncomputable def partialEval0SField {s : ℕ}
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  (ContMDiffSection.mk
      (fun y : M => Tensor0SPartialEval.tensor0SPartialEval I M
        (fun b => nablaT b) (fun b => Y b) y)
      (Tensor0SPartialEval.contMDiff_tensor0SPartialEval (I := I) (M := M) (s := s)
        (T := fun b => nablaT b) nablaT.contMDiff (Y := fun b => Y b) Y.contMDiff) :
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
    Cₛ^∞⟮I; Tensor0SModel s Real E, (fun x : M => Tensor0SSpace s I x)⟯)

@[simp] theorem partialEval0SField_apply {s : ℕ}
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (y : M) :
    partialEval0SField (I := I) nablaT Y y =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) s y (nablaT y) (Y y) := rfl

/-! ## Differentiability of the fibre inner product (general rank) -/

/-- **The fibre inner product of two smooth covariant-tensor fields is
differentiable.**  Rank-uniform generalisation of the `(0,2)` `inner0S_two_mdiff`.
The local coordinate contraction `coordContract gInv (comps A) (comps B)` is a
finite sum of products of `MDifferentiableAt` scalar fields. -/
theorem inner0S_mdiff {s : ℕ}
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner0S (I := I) g y s (A y) (B y)) x := by
  classical
  set Idx : Type := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
    with hIdx
  set frame : Idx -> (y : M) -> TangentSpace I y :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x with hframe
  set U : M -> Idx -> Idx -> Real :=
    fun y i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x i j (extChartAt I x y) with hU
  set cA : M -> (Fin s -> Idx) -> Real :=
    fun y I0 => A y (fun a => frame (I0 a) y) with hcAdef
  set cB : M -> (Fin s -> Idx) -> Real :=
    fun y J0 => B y (fun a => frame (J0 a) y) with hcBdef
  have hx : x ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := inferInstance
  -- Differentiability of the component fields.
  have hUmdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => U y i j) x := by
    intro i j
    simpa [U, Idx] using
      DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt (I := I) g x i j
  have hcAmdiff : ∀ I0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cA y I0) x := by
    intro I0
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) A x I0
    exact h.mdifferentiableAt (by simp)
  have hcBmdiff : ∀ J0 : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => cB y J0) x := by
    intro J0
    have h := DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) (𝕜 := Real) B x J0
    exact h.mdifferentiableAt (by simp)
  -- Local agreement of the inner product with the coordinate contraction.
  have hlocal :
      (fun y : M => inner0S (I := I) g y s (A y) (B y)) =ᶠ[𝓝 x]
        fun y : M => coordContract (U y) (cA y) (cB y) := by
    filter_upwards
      [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x).mem_nhds hx]
      with y hy
    rw [inner0S_eq_coord (I := I) g y s
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)
      (U y) (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x hy)
      (A y) (B y)]
    rw [← coordContract_eq_coordInner0S (I := I) (U y) (A y) (B y)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x hy)]
    refine congrArg₂ (fun f h => coordContract (U y) f h) ?_ ?_
    · funext I0
      simp only [tensor0SComponent, cA, frame]
      refine congrArg (fun w => A y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
    · funext J0
      simp only [tensor0SComponent, cB, frame]
      refine congrArg (fun w => B y w) ?_
      funext a
      rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
  -- The coordinate contraction is differentiable: a finite sum of products of
  -- `MDifferentiableAt` factors.
  have hcontr :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => coordContract (U y) (cA y) (cB y)) x := by
    have hprodU : ∀ (I0 J0 : Fin s -> Idx),
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => ∏ a : Fin s, U y (I0 a) (J0 a)) x := by
      intro I0 J0
      have := MDifferentiableAt.prod (I := I) (𝕜 := Real)
        (f := fun a => fun y : M => U y (I0 a) (J0 a))
        (t := (Finset.univ : Finset (Fin s))) (z := x)
        (fun a _ => hUmdiff (I0 a) (J0 a))
      simpa [Finset.prod_fn] using this
    have hsummand : ∀ I0 J0 : Fin s -> Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x :=
      fun I0 J0 => ((hprodU I0 J0).mul (hcAmdiff I0)).mul (hcBmdiff J0)
    have hinner : ∀ I0 : Fin s -> Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) x := by
      intro I0
      have hsum := DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
        (I := I) (x := x) (t := (Finset.univ : Finset (Fin s -> Idx)))
        (fun J0 => fun y : M => (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0)
        (fun J0 _ => hsummand I0 J0)
      have heqfun :
          (Finset.univ : Finset (Fin s -> Idx)).sum
              (fun J0 => fun y : M =>
                (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) =
            fun y : M => ∑ J0 : Fin s -> Idx,
              (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0 := by
        funext y; rw [Finset.sum_apply]
      rwa [heqfun] at hsum
    have hsumI := DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
      (I := I) (x := x) (t := (Finset.univ : Finset (Fin s -> Idx)))
      (fun I0 => fun y : M => ∑ J0 : Fin s -> Idx,
        (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0)
      (fun I0 _ => hinner I0)
    have heqfun :
        (Finset.univ : Finset (Fin s -> Idx)).sum
            (fun I0 => fun y : M => ∑ J0 : Fin s -> Idx,
              (∏ a : Fin s, U y (I0 a) (J0 a)) * cA y I0 * cB y J0) =
          fun y : M => coordContract (U y) (cA y) (cB y) := by
      funext y
      rw [Finset.sum_apply]
      rfl
    rwa [heqfun] at hsumI
  exact hcontr.congr_of_eventuallyEq hlocal

/-! ## The covariant derivative of the first-slot-frozen field

The rank-`s` generalisation of `freeze02_deriv`'s `hBderiv`: differentiating the
first-slot partial evaluation `partialEval0SField nablaT Y` (= `(∇T)(Y,·)`) along
`X` produces the second covariant derivative `∇²T(X,Y,·)` plus the
moving-frame correction `(∇T)(∇_X Y,·)`.  This is the only nontrivial
tensor-realization step. -/

/-- **The covariant derivative of the first-slot-frozen covariant-derivative
field.**  For `nablaT` realizing `∇T` (`hA`) and `nabla2T` realizing `∇²T = ∇(∇T)`
(`h2`), the raw covariant derivative of the first-slot partial evaluation
`partialEval0SField nablaT Y` along a smooth field `X` is

`∇_X ((∇T)(Y,·)) = ∇²T(X,Y,·) + (∇T)(∇_X Y,·)`,

i.e.

`nabla0SFun s cov X (partialEval0SField nablaT Y) x
  = freezeFirstTwoArgs0S (nabla2T x) (X x) (Y x)
    + tensor0S_curry s x (nablaT x) ((cov Y x) (X x))`.

Rank-`s` generalisation of `freeze02_deriv`'s `hBderiv`. -/
theorem nabla_partialEval0S {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaT nabla2T)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (partialEval0SField (I := I) nablaT Y) x =
      freezeFirstTwoArgs0S (I := I) (nabla2T x) (X x) (Y x) +
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x)
          ((cov (fun y : M => Y y) x) (X x)) := by
  classical
  set B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := partialEval0SField (I := I) nablaT Y with hBdef
  -- Evaluate both sides on an arbitrary slot tuple `v`.
  ext v
  -- Realize each slot of `v` by a smooth section agreeing with it at `x`.
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (v a)).choose
  have hV : ∀ a : Fin s, V a x = v a := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (v a)).choose_spec
  have hVx : (fun a : Fin s => V a x) = v := funext hV
  -- The `(s+1)`-tuple `Fin.cons Y V` realizing `(Y, v)`.
  let V3 : Fin (s + 1) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons Y V
  -- The two raw eval-smooth-slots identities.
  have hfree_raw :=
    Tensor0SBundle.nabla0SFun_eval_smooth_slots (I := I) cov X V B x
  have htot_raw :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) h2 X V3 x
  -- Abbreviations for the directional derivative and the corrections.
  set D : Real :=
    extDerivFun (I := I)
      (fun p : M => nablaT p (fun a : Fin (s + 1) => V3 a p)) x (X x) with hDdef
  -- Pointwise reductions of the leading tuple `V3 = Fin.cons Y V`.
  have hV30 : ∀ p : M, V3 0 p = Y p := fun p => by
    simp only [V3, Fin.cons_zero]
  have hV3succ : ∀ (b : Fin s) (p : M), V3 b.succ p = V b p := fun b p => by
    simp only [V3, Fin.cons_succ]
  -- `B p (V·p) = nablaT p (Fin.cons (Y p) (V·p))` pointwise (the partialEval rule).
  have hBeval : ∀ (p : M) (w : Fin s -> TangentSpace I p),
      B p w = nablaT p (Fin.cons (Y p) w) := by
    intro p w
    rw [hBdef, partialEval0SField_apply]
    exact tensor0S_curry_apply_cons (I := I) s (nablaT p) (Y p) w
  -- The derivative of `B(V)` equals `D` (the derivative of `nablaT(Fin.cons Y V)`).
  have hDfree :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin s => V a p)) x (X x) = D := by
    rw [hDdef]
    refine DifferentialGeometry.Tensor.Coordinates.deriv_congr_nhds
      (I := I) (X x) ?_
    filter_upwards with p
    rw [hBeval p (fun a : Fin s => V a p)]
    congr 1
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · rw [Fin.cons_zero, hV30 p]
    · rw [Fin.cons_succ, hV3succ b p]
  -- LHS: `(∇_X B)(v) = D - Σ_{b} B(update V b (∇_X V_b))`.
  have hLHS :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X B x v =
        D - ∑ b : Fin s,
          B x (Function.update (fun a : Fin s => V a x) b
            ((cov (fun p : M => V b p) x) (X x))) := by
    rw [← hVx]
    rw [hfree_raw, hDfree]
  -- RHS first summand: `nabla2T x (X x :: Y x :: v) = freezeFirstTwoArgs0S … v`.
  have hV3x : (fun a : Fin (s + 1) => V3 a x) = Fin.cons (Y x) v := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · rw [Fin.cons_zero]; exact hV30 x
    · rw [Fin.cons_succ, hV3succ b x]; exact hV b
  -- Split the `(s+1)` correction sum into the `Y`-slot (a = 0) and the `V`-slots.
  have hcorrSplit :
      (∑ a : Fin (s + 1),
          nablaT x (Function.update (fun a : Fin (s + 1) => V3 a x) a
            ((cov (fun p : M => V3 a p) x) (X x)))) =
        nablaT x (Fin.cons ((cov (fun p : M => Y p) x) (X x)) v) +
          ∑ b : Fin s,
            B x (Function.update (fun a : Fin s => V a x) b
              ((cov (fun p : M => V b p) x) (X x))) := by
    rw [Fin.sum_univ_succ]
    congr 1
    · -- The `a = 0` term: update the head slot, giving `Fin.cons (∇_X Y) v`.
      rw [show (fun p : M => V3 0 p) = (fun p : M => Y p) from funext hV30]
      congr 1
      rw [hV3x]
      funext a
      refine Fin.cases ?_ (fun b => ?_) a
      · simp [Function.update]
      · simp [Function.update, Fin.cons_succ]
    · -- The `a = succ b` terms: `update` past the head, identifying `B`.
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (fun p : M => V3 b.succ p) = (fun p : M => V b p) from funext (hV3succ b)]
      rw [hBeval x (Function.update (fun a : Fin s => V a x) b
        ((cov (fun p : M => V b p) x) (X x)))]
      congr 1
      rw [hV3x]
      -- `update (Fin.cons (Y x) v) (succ b) c = Fin.cons (Y x) (update v b c)`.
      rw [← Fin.cons_update]
      rw [hVx]
  -- RHS via `eval_smooth_slots` for `nabla2T`.
  have hRHStot :
      nabla2T x (Fin.cons (X x) (fun a : Fin (s + 1) => V3 a x)) =
        D - (nablaT x (Fin.cons ((cov (fun p : M => Y p) x) (X x)) v) +
          ∑ b : Fin s,
            B x (Function.update (fun a : Fin s => V a x) b
              ((cov (fun p : M => V b p) x) (X x)))) := by
    rw [htot_raw, hcorrSplit]
  -- Assemble: identify the two RHS tensor pieces.
  have hfreeze :
      freezeFirstTwoArgs0S (I := I) (nabla2T x) (X x) (Y x) v =
        nabla2T x (Fin.cons (X x) (fun a : Fin (s + 1) => V3 a x)) := by
    rw [freezeFirstTwoArgs0S_apply, hV3x]
    congr 1
  have hcurry :
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x)
          ((cov (fun y : M => Y y) x) (X x)) v =
        nablaT x (Fin.cons ((cov (fun p : M => Y p) x) (X x)) v) :=
    tensor0S_curry_apply_cons (I := I) s (nablaT x)
      ((cov (fun p : M => Y p) x) (X x)) v
  -- Conclude pointwise, splitting the tensor sum on the right.
  change nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov X B x v =
    (freezeFirstTwoArgs0S (I := I) (nabla2T x) (X x) (Y x) +
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x)
          ((cov (fun y : M => Y y) x) (X x))) v
  rw [ContinuousMultilinearMap.add_apply]
  rw [hLHS, hfreeze, hcurry, hRHStot]
  ring

/-! ## The second-order frozen-derivative rule and the norm Hessian -/

/-- **The derivative of the frozen first covariant derivative paired with `T`.**
Rank-`s` generalisation of `freeze02_deriv`.  Differentiating `2⟨(∇T)(Y,·),T⟩`
along `X` produces the three Bochner terms: the second covariant derivative
`∇²T(X,Y,·)` paired with `T`, the moving-frame correction `(∇T)(∇_X Y,·)` paired
with `T`, and the cross term `⟨(∇T)(Y,·),(∇T)(X,·)⟩`. -/
theorem freeze0S_deriv {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov T nablaT)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaT nabla2T)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M =>
          2 * inner0S (I := I) g y s (partialEval0SField (I := I) nablaT Y y) (T y))
        x (X x) =
      2 *
        (inner0S (I := I) g x s
            (freezeFirstTwoArgs0S (I := I) (nabla2T x) (X x) (Y x)) (T x) +
          inner0S (I := I) g x s
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x)
              ((cov (fun y : M => Y y) x) (X x))) (T x) +
          inner0S (I := I) g x s
            (partialEval0SField (I := I) nablaT Y x)
            (partialEval0SField (I := I) nablaT X x)) := by
  set B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := partialEval0SField (I := I) nablaT Y with hBdef
  -- Pull out the constant `2`.
  have hf : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner0S (I := I) g y s (B y) (T y)) x :=
    inner0S_mdiff (I := I) g B T x
  have hscale := congrArg (fun L => L (X x))
    (DifferentialGeometry.extDerivFun_const_mul I (2 : Real) hf)
  -- The Leibniz rule for `⟨B, T⟩`.
  have hinner := inner0S_nabla (I := I) cov g hmc B T X x
  -- `∇_X T = (∇T)(X,·) = partialEval0SField nablaT X`.
  have hAderiv :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X T x =
        partialEval0SField (I := I) nablaT X x := by
    ext v
    rw [partialEval0SField_apply, tensor0S_curry_apply_cons]
    exact (TotalNabla0SRealizes.apply (I := I) hA X x v).symm
  -- `∇_X B = ∇²T(X,Y,·) + (∇T)(∇_X Y,·)`.
  have hBderiv := nabla_partialEval0S (I := I) cov nablaT nabla2T h2 X Y x
  -- Additivity of the fibre inner product in the left slot.
  have hadd : ∀ (P Q R : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) s x),
      inner0S (I := I) g x s (P + Q) R =
        inner0S (I := I) g x s P R + inner0S (I := I) g x s Q R := by
    intro P Q R
    simp only [inner0S, MetricFiberData.inner, map_add, LinearMap.add_apply]
  calc
    extDerivFun (I := I)
        (fun y : M =>
          2 * inner0S (I := I) g y s (B y) (T y)) x (X x)
        =
      2 * extDerivFun (I := I)
        (fun y : M => inner0S (I := I) g y s (B y) (T y)) x (X x) := by
        simpa [Pi.smul_apply, smul_eq_mul] using hscale
    _ =
      2 *
        (inner0S (I := I) g x s
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              s cov X B x) (T x) +
          inner0S (I := I) g x s (B x)
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              s cov X T x)) := by
        rw [hinner]
    _ =
      2 *
        (inner0S (I := I) g x s
            (freezeFirstTwoArgs0S (I := I) (nabla2T x) (X x) (Y x)) (T x) +
          inner0S (I := I) g x s
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x)
              ((cov (fun y : M => Y y) x) (X x))) (T x) +
          inner0S (I := I) g x s
            (partialEval0SField (I := I) nablaT Y x)
            (partialEval0SField (I := I) nablaT X x)) := by
        rw [hAderiv, hBderiv, hBdef, hadd]

/-- **The first-order directional derivative of the norm square as a one-form.**
Rank-`s` generalisation of `du_norm02`.  For a realized differential `du` of
`‖T‖²`, `du(W) = 2⟨(∇T)(W,·),T⟩`.  Derived from `normSq0S_nabla`. -/
theorem du_norm0S {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov T nablaT)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq0S (I := I) g y s (T y)) du)
    {x : M} (W : TangentSpace I x) :
    du x (fun _ : Fin 1 => W) =
      2 * inner0S (I := I) g x s
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x) W) (T x) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  -- `∇_W T = (∇T)(W,·)` from the realization of `∇T`.
  have hAderiv :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov Wsec T x =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x) (Wsec x) := by
    ext v
    rw [tensor0S_curry_apply_cons]
    exact (TotalNabla0SRealizes.apply (I := I) hA Wsec x v).symm
  calc
    du x (fun _ : Fin 1 => W)
        = differential1FormFun (I := I)
            (fun y : M => normSq0S (I := I) g y s (T y)) x (fun _ : Fin 1 => W) := by
          rw [hdu x]; rfl
    _ = extDerivFun (I := I)
          (fun y : M => normSq0S (I := I) g y s (T y)) x W :=
          differential1FormFun_apply_eq_extDerivFun
            (I := I) (fun y : M => normSq0S (I := I) g y s (T y)) x W
    _ = extDerivFun (I := I)
          (fun y : M => normSq0S (I := I) g y s (T y)) x (Wsec x) := by
          rw [hWsec]
    _ = 2 * inner0S (I := I) g x s
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov Wsec T x) (T x) :=
          normSq0S_nabla (I := I) cov g hmc T Wsec x
    _ = 2 * inner0S (I := I) g x s
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x (nablaT x) W) (T x) := by
          rw [hAderiv, hWsec]

/-- Kato bound for the differential of the squared norm of a covariant tensor. -/
theorem normSq0S_du_le {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov T nablaT)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq0S (I := I) g y s (T y)) du)
    (x : M) :
    normSq0S (I := I) g x 1 (du x) <=
      4 * normSq0S (I := I) g x s (T x) *
        normSq0S (I := I) g x (s + 1) (nablaT x) := by
  classical
  obtain ⟨_mu, basis, hinv, _hinv', _hmu0, _hmu1⟩ :=
    exists_diagInv_of_equiv (I := I) g g x (C := 1) (by norm_num)
      (by intro v; simp)
  rw [normSq0S_identity_eq_sum_sq (I := I) g x 1 basis hinv]
  rw [sum_fin_one_fun]
  calc
    (∑ i,
        (component0S (I := I) basis (du x) (fun _ : Fin 1 => i)) ^ 2) =
        ∑ i,
          (2 * inner0S (I := I) g x s
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
              (nablaT x) (basis i)) (T x)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [component0S_apply,
            du_norm0S (I := I) cov g hmc T nablaT hA du hdu (basis i)]
    _ <= ∑ i,
          4 *
            (normSq0S (I := I) g x s
              (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
                (nablaT x) (basis i)) *
              normSq0S (I := I) g x s (T x)) := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (2 * inner0S (I := I) g x s
                (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
                  (nablaT x) (basis i)) (T x)) ^ 2 =
                4 * (inner0S (I := I) g x s
                  (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
                    (nablaT x) (basis i)) (T x)) ^ 2 := by ring
            _ <= 4 *
                (normSq0S (I := I) g x s
                    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
                      (nablaT x) (basis i)) *
                  normSq0S (I := I) g x s (T x)) :=
              mul_le_mul_of_nonneg_left
                (inner0S_sq_le_mul (I := I) g x s
                  (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
                    (nablaT x) (basis i)) (T x)) (by norm_num)
    _ = 4 * normSq0S (I := I) g x s (T x) *
          ∑ i, normSq0S (I := I) g x s
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
              (nablaT x) (basis i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 4 * normSq0S (I := I) g x s (T x) *
          normSq0S (I := I) g x (s + 1) (nablaT x) := by
          rw [normSq0S_curry_sum (I := I) g x s basis hinv]

/-- **The pointwise Hessian product rule of a covariant-tensor norm**, in basis
component form — the genuine geometric input of the general Bochner Laplacian
split, here **derived** (not assumed) from metric compatibility.  This is the
rank-`s` generalisation of `BochnerTensor.hess_norm02`, and it discharges the
`TensorNormHessianProductInBasis` hypothesis of `tensorNormBochnerSplit`. -/
theorem hess_norm0S {s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Xb : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis Xb)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov T nablaT)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaT nabla2T)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq0S (I := I) g y s (T y)) du)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du normSecond x) :
    TensorNormHessianProductInBasis (I := I) basis gInv (T x) (nablaT x)
      (nabla2T x) (normSecond x) := by
  classical
  intro i j
  -- The field `y ↦ du(y)(X_j y) = 2⟨(∇T)(X_j y,·),T⟩`.
  have hfun :
      (fun y : M => du y (fun _ : Fin 1 => Xb j y)) =
        fun y : M =>
          2 * inner0S (I := I) g y s
            (partialEval0SField (I := I) nablaT (Xb j) y) (T y) := by
    funext y
    rw [du_norm0S (I := I) cov g hmc T nablaT hA du hdu (Xb j y)]
    rw [partialEval0SField_apply]
  -- The Hessian as `∇(du)`.
  have hnablaDu :
      nablaDuAt (I := I) cov (Xb i) du x (fun _ : Fin 1 => basis j) =
        extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => Xb j y))
          x (Xb i x) -
        du x (fun _ : Fin 1 => (cov (fun y : M => Xb j y) x) (Xb i x)) := by
    have h := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots
      (I := I) cov (Xb i) (Xb j) du x
    simpa [nablaDuAt, hfields j] using h
  -- The frozen-derivative rule and the moving-frame correction.
  have hder := freeze0S_deriv (I := I) cov g hmc T nablaT nabla2T hA h2
    (Xb i) (Xb j) x
  have hcorr := du_norm0S (I := I) cov g hmc T nablaT hA du hdu
    ((cov (fun y : M => Xb j y) x) (Xb i x))
  -- Assemble the intrinsic Hessian identity.
  have hraw :
      normSecond x (vec2 (I := I) (basis i) (basis j)) =
        2 *
          (inner0S (I := I) g x s
              (freezeFirstTwoArgs0S (I := I) (nabla2T x) (basis i) (basis j))
              (T x) +
            inner0S (I := I) g x s
              (partialEval0SField (I := I) nablaT (Xb j) x)
              (partialEval0SField (I := I) nablaT (Xb i) x)) := by
    calc
      normSecond x (vec2 (I := I) (basis i) (basis j))
          = normSecond x (vec2 (I := I) (Xb i x) (basis j)) := by
              rw [hfields i]
      _ = nablaDuAt (I := I) cov (Xb i) du x (fun _ : Fin 1 => basis j) :=
              hHess (Xb i) (basis j)
      _ =
          extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => Xb j y))
            x (Xb i x) -
          du x (fun _ : Fin 1 => (cov (fun y : M => Xb j y) x) (Xb i x)) := hnablaDu
      _ =
          extDerivFun (I := I)
            (fun y : M =>
              2 * inner0S (I := I) g y s
                (partialEval0SField (I := I) nablaT (Xb j) y) (T y))
            x (Xb i x) -
          du x (fun _ : Fin 1 => (cov (fun y : M => Xb j y) x) (Xb i x)) := by
            rw [hfun]
      _ =
          2 *
            (inner0S (I := I) g x s
                (freezeFirstTwoArgs0S (I := I) (nabla2T x) (Xb i x) (Xb j x))
                (T x) +
              inner0S (I := I) g x s
                (partialEval0SField (I := I) nablaT (Xb j) x)
                (partialEval0SField (I := I) nablaT (Xb i) x)) := by
            rw [hder, hcorr]
            ring
      _ =
          2 *
            (inner0S (I := I) g x s
                (freezeFirstTwoArgs0S (I := I) (nabla2T x) (basis i) (basis j))
                (T x) +
              inner0S (I := I) g x s
                (partialEval0SField (I := I) nablaT (Xb j) x)
                (partialEval0SField (I := I) nablaT (Xb i) x)) := by
            rw [hfields i, hfields j]
  -- Convert the two intrinsic inner products to the coordinate form, matching the
  -- slot ordering of `TensorNormHessianProductInBasis`.
  rw [hraw]
  rw [inner0S_eq_coord (I := I) g x s basis gInv hinv
    (freezeFirstTwoArgs0S (I := I) (nabla2T x) (basis i) (basis j)) (T x)]
  rw [inner0S_symm (I := I) g x
    (partialEval0SField (I := I) nablaT (Xb j) x)
    (partialEval0SField (I := I) nablaT (Xb i) x)]
  rw [inner0S_eq_coord (I := I) g x s basis gInv hinv
    (partialEval0SField (I := I) nablaT (Xb i) x)
    (partialEval0SField (I := I) nablaT (Xb j) x)]
  rw [partialEval0SField_apply, partialEval0SField_apply, hfields i, hfields j]

/-! ## The hypothesis-free general Bochner Laplacian split -/

/-- **The general Bochner Laplacian split of a covariant-tensor norm, with the
pointwise Hessian product rule discharged.**

This is `tensorNormBochnerSplit` (`Tensor0SBochnerSplit.lean`) with its standing
hypothesis `TensorNormHessianProductInBasis` (`hprod`) **removed**: it is now
derived from metric compatibility via `hess_norm0S`.  For a metric-compatible
connection `cov`, a tangent basis with genuine inverse `gInv`, smooth basis
fields, a smooth `(0,s)` field `T` with realized first and second covariant
derivatives `nablaT`/`nabla2T`, and a realized differential `du` / Hessian
`normSecond` of `‖T‖²`, the scalar Laplacian splits as

`Δ‖T‖² = 2⟨ΔT,T⟩ + 2‖∇T‖²`,

i.e.

`metricTrace0S2InBasis basis gInv (normSecond x) Fin.elim0
  = 2 · inner0S g x s (metricTrace0S2TensorInBasis basis gInv (nabla2T x)) (T x)
    + 2 · normSq0S g x (s+1) (nablaT x)`.

The rough Laplacian `metricTrace0S2TensorInBasis basis gInv (nabla2T x)` is
`ΔT = g^{ab}∇_a∇_b T`.  Rank-uniform and sorry-free; the `(0,2)` analogue is the
chain `BochnerTensor.second_norm02_mc` + `tensor02_norm_product_rule_of_second_product`. -/
theorem tensorNormBochnerSplit_mc {s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Xb : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis Xb)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov T nablaT)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov nablaT nabla2T)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq0S (I := I) g y s (T y)) du)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du normSecond x) :
    metricTrace0S2InBasis (I := I) basis gInv (normSecond x) Fin.elim0 =
      2 * inner0S (I := I) g x s
            (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2T x)) (T x) +
        2 * normSq0S (I := I) g x (s + 1) (nablaT x) :=
  tensorNormBochnerSplit (I := I) g basis gInv hinv (T x) (nablaT x) (nabla2T x)
    (normSecond x)
    (hess_norm0S (I := I) cov g hmc basis gInv hinv Xb hfields T nablaT nabla2T
      hA h2 du normSecond hdu hHess)

end

end Tensor0SBundle
