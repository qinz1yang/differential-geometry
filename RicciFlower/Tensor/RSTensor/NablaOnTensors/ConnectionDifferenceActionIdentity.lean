import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceAction
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Connection-Difference Action Identity

This file bridges the checked mixed-tensor covariant-derivative difference
formula to the component action `connActComp`.  It is the `k = 0` geometric
identity behind the one-step estimate in MSM135 Lemma 4.5.
-/

namespace Tensor0SBundle

noncomputable section

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

set_option backward.isDefEq.respectTransparency false in
/-- Component form of the first-order connection-change identity, rewritten
using the reusable action `connActComp`.

This is just `componentRS_nablaRSFun_sub` with the connection-difference
coefficients repackaged by `componentRS_connectionDifferenceTensorAt`. -/
theorem componentRS_nablaRSFun_sub_connAct {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx)
    (hX_at : X x₀ = basis (lower 0))
    (hβ_at : β x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => (T p (β p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    componentRS (I := I) basis
        (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s cov X T x₀ -
          nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s cov' X T x₀)
        upper (fun b : Fin s => lower b.succ) =
      connActComp
        (fun l i j =>
          componentRS (I := I) basis
            (connectionDifferenceTensorAt (I := I) cov cov' x₀)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' => componentRS (I := I) basis (T x₀) upper' lower')
        upper lower := by
  classical
  have h :=
    componentRS_nablaRSFun_sub
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) cov cov' X T β x₀ basis V upper lower
      hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord
  simpa [connActComp, connActLowerTail, componentRS_connectionDifferenceTensorAt,
    componentRS_apply, basisTensor0S_apply]
    using h

set_option backward.isDefEq.respectTransparency false in
/-- Square-root norm form of `componentRS_nablaRSFun_sub_connAct` for one
directional covariant derivative.

This is the checked first-order norm producer behind MSM135 Lemma 4.5: once the
two directional covariant derivatives are evaluated against a basis direction,
their difference is controlled by the connection-difference tensor and the
original tensor.  No approximate-isometry hypothesis is used here; that
specialization belongs to HCG. -/
theorem nablaDirSubNorm_le {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (dir : Idx)
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : X x₀ = basis dir)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s
          (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov X T x₀ -
            nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov' X T x₀)) <=
      Real.sqrt
        ((Fintype.card (Fin r -> Idx) : Real) *
          ((Fintype.card (Fin s -> Idx) : Real) *
            (connActConst (Idx := Idx) r s
              (Real.sqrt
                (normSqRS (I := I) (g := g) (x := x₀) 1 2
                  (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
              (Real.sqrt
                (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))) ^ 2)) := by
  let B : Real :=
    connActConst (Idx := Idx) r s
      (Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
      (Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))
  have hB : 0 <= B := by
    exact connActConst_nonneg (Idx := Idx)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine sqrt_normRS_le_comps (I := I) g x₀ r s basis hinv
    (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀ -
      nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀) hB ?_
  intro upper lower
  have hcomp :=
    componentRS_nablaRSFun_sub_connAct
      (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) cov cov' X T (β upper) x₀ basis V upper (Fin.cons dir lower)
      (by simpa using hX_at) (hβ_at upper) hV_at (by simpa using hpairT upper lower)
      (hpairβ upper) (hβmodel upper) hV hVmodel hcoord
  simpa [B] using
    calc
      |componentRS (I := I) basis
          (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov X T x₀ -
            nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov' X T x₀) upper lower|
          =
        |connActComp
          (fun l i j =>
            componentRS (I := I) basis
              (connectionDifferenceTensorAt (I := I) cov cov' x₀)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' => componentRS (I := I) basis (T x₀) upper' lower')
          upper (Fin.cons dir lower)| := by
            simpa using congrArg abs hcomp
      _ <= B := by
        simpa [B] using
        abs_connActTensor_le (I := I) g x₀ basis hinv
            (connectionDifferenceTensorAt (I := I) cov cov' x₀) (T x₀)
            upper (Fin.cons dir lower)

set_option backward.isDefEq.respectTransparency false in
/-- Directional first-order one-step inequality following from
`nablaDirSubNorm_le` and the square-root tensor-norm triangle inequality. -/
theorem nablaDirNorm_le {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (dir : Idx)
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : X x₀ = basis dir)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s
          (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s cov' X T x₀)) <=
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r s
            (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov X T x₀)) +
        Real.sqrt
          ((Fintype.card (Fin r -> Idx) : Real) *
            ((Fintype.card (Fin s -> Idx) : Real) *
              (connActConst (Idx := Idx) r s
                (Real.sqrt
                  (normSqRS (I := I) (g := g) (x := x₀) 1 2
                    (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
                (Real.sqrt
                  (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))) ^ 2)) := by
  have htri :=
    sqrt_normRS_le_add_sub
      (I := I) (g := g) (x := x₀) r s
      (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀)
      (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀)
  have hdiff :=
    nablaDirSubNorm_le
      (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (Idx := Idx) g cov cov' X T β x₀ basis hinv
      dir V hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord
  exact htri.trans (add_le_add (le_refl _) hdiff)

set_option backward.isDefEq.respectTransparency false in
/-- Component form of the connection-change identity for supplied total
covariant derivative fields.

This converts the realization predicates for total covariant derivatives into
the same component action used by `componentRS_nablaRSFun_sub_connAct`. -/
theorem totalNablaSub_comp {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    componentRS (I := I) basis (nablaT x₀ - nablaT' x₀) upper lower =
      connActComp
        (fun l i j =>
          componentRS (I := I) basis
            (connectionDifferenceTensorAt (I := I) cov cov' x₀)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' => componentRS (I := I) basis (T x₀) upper' lower')
        upper lower := by
  let X := Xfield (lower 0)
  let tail : Fin s -> Idx := fun a => lower a.succ
  let slots : Fin s -> TangentSpace I x₀ := fun a => basis (tail a)
  have hslots :
      (fun a : Fin (s + 1) => basis (lower a)) =
        Fin.cons (X x₀) slots := by
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [X, slots, hX_at]
    | succ a =>
        simp [tail, slots, Fin.cons_succ]
  have hdir_comp :
      componentRS (I := I) basis (nablaT x₀ - nablaT' x₀) upper lower =
        componentRS (I := I) basis
          (nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov X T x₀ -
            nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              r s cov' X T x₀)
          upper tail := by
    rw [componentRS_apply]
    rw [componentRS_apply]
    simp only [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
    rw [hslots]
    rw [hreal.apply X x₀ (basisTensor0S (I := I) basis upper) slots]
    rw [hreal'.apply X x₀ (basisTensor0S (I := I) basis upper) slots]
  rw [hdir_comp]
  exact componentRS_nablaRSFun_sub_connAct
    (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov cov' X T (β upper) x₀ basis V upper lower
    (by simpa [X] using hX_at (lower 0)) (hβ_at upper) hV_at
    (hpairT upper lower) (hpairβ upper) (hβmodel upper) hV hVmodel hcoord

set_option backward.isDefEq.respectTransparency false in
/-- Tensor form of `totalNablaSub_comp`.

The difference of the supplied total covariant derivatives is the actual
connection-action tensor built from the connection-difference tensor and `T`.
This removes one component-only layer from the Lemma 4.5 route; the remaining
frontier is differentiating this action tensor. -/
theorem totalNablaSub_eq_connActTensor {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    nablaT x₀ - nablaT' x₀ =
      connActTensorAt (I := I) basis
        (connectionDifferenceTensorAt (I := I) cov cov' x₀) (T x₀) := by
  apply extRS_basis (I := I) basis
  intro upper lower
  rw [totalNablaSub_comp
    (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov cov' T nablaT nablaT' hreal hreal' β x₀ basis
    Xfield V hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord upper lower]
  rw [connActTensorAt_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Antidiagonal `k = 0` form of `totalNablaSub_comp`.

This is the base case of the iterated connection-action Leibniz realization
needed for MSM135 Lemma 4.5.  The higher-order frontier is to replace the
constant arrays below by genuine `h`-covariant derivative jets of the
connection difference and of `T`. -/
theorem totalNablaSub_anti0 {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    componentRS (I := I) basis (nablaT x₀ - nablaT' x₀) upper lower =
      Finset.sum (Finset.antidiagonal 0)
        (fun ab => (Nat.choose 0 ab.1 : Real) *
          connActComp
            (fun l i j =>
              componentRS (I := I) basis
                (connectionDifferenceTensorAt (I := I) cov cov' x₀)
                (fun _ : Fin 1 => l)
                (fun q : Fin 2 => if q = 0 then i else j))
            (fun upper' lower' =>
              componentRS (I := I) basis (T x₀) upper' lower')
            upper lower) := by
  rw [totalNablaSub_comp
    (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov cov' T nablaT nablaT' hreal hreal' β x₀ basis
    Xfield V hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord upper lower]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Norm form of `totalNablaSub_comp`.  This is the total-derivative version of
the first-order connection-change estimate. -/
theorem totalNablaSubNorm_le {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
          (nablaT x₀ - nablaT' x₀)) <=
      Real.sqrt
        ((Fintype.card (Fin r -> Idx) : Real) *
          ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
            (connActConst (Idx := Idx) r s
              (Real.sqrt
                (normSqRS (I := I) (g := g) (x := x₀) 1 2
                  (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
              (Real.sqrt
                (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))) ^ 2)) := by
  let B : Real :=
    connActConst (Idx := Idx) r s
      (Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
      (Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))
  have hB : 0 <= B := by
    exact connActConst_nonneg (Idx := Idx)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine sqrt_normRS_le_comps (I := I) g x₀ r (s + 1) basis hinv
    (nablaT x₀ - nablaT' x₀) hB ?_
  intro upper lower
  rw [totalNablaSub_comp
    (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov cov' T nablaT nablaT' hreal hreal' β x₀ basis
    Xfield V hX_at hβ_at hV_at hpairT hpairβ hβmodel hV hVmodel hcoord upper lower]
  simpa [B] using
    abs_connActTensor_le (I := I) g x₀ basis hinv
      (connectionDifferenceTensorAt (I := I) cov cov' x₀) (T x₀) upper lower

set_option backward.isDefEq.respectTransparency false in
/-- Antidiagonal `k = 0` norm-bound form of the total first-order one-step
estimate.

This is the norm version of `totalNablaSub_anti0`, phrased with the same
`connActAntiStepConst` used by the future iterated Leibniz estimate. -/
theorem totalNablaAnti0 {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀)
    {eps B N : Real} (heps : 0 <= eps) (hB : 0 <= B) (hN : 0 <= N)
    (hA :
      Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x₀)) <= eps * B)
    (hT :
      Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)) <= N) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
          (nablaT' x₀)) <=
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
            (nablaT x₀)) +
        eps * connActAntiStepConst (Idx := Idx) r s 0 (fun _ => B) * N := by
  let A : Nat -> TensorRSSpace 1 2 I x₀ :=
    fun _ => connectionDifferenceTensorAt (I := I) cov cov' x₀
  let U : Nat -> TensorRSSpace r s I x₀ := fun _ => T x₀
  have htri :=
    sqrt_normRS_le_add_sub
      (I := I) (g := g) (x := x₀) r (s + 1) (nablaT x₀) (nablaT' x₀)
  have hdiff :
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
            (nablaT x₀ - nablaT' x₀)) <=
        eps * connActAntiStepConst (Idx := Idx) r s 0 (fun _ => B) * N := by
    refine norm_connActAnti_bound_step
      (I := I) g x₀ 0 basis hinv A U (nablaT x₀ - nablaT' x₀) ?hcomp
      (B := fun _ => B) heps (fun _ => hB) hN ?hA ?hU
    · intro upper lower
      simpa [A, U] using
        totalNablaSub_anti0
          (E := E) (H := H) (I := I) (M := M)
          (r := r) (s := s) cov cov' T nablaT nablaT' hreal hreal' β
          x₀ basis Xfield V hX_at hβ_at hV_at hpairT hpairβ hβmodel
          hV hVmodel hcoord upper lower
    · intro a
      simpa [A] using hA
    · intro b
      simpa [U] using hT
  exact htri.trans (add_le_add_right hdiff _)

set_option backward.isDefEq.respectTransparency false in
/-- Total first-order one-step inequality following from
`totalNablaSubNorm_le`. -/
theorem totalNablaNorm_le {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
          (nablaT' x₀)) <=
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
            (nablaT x₀)) +
        Real.sqrt
          ((Fintype.card (Fin r -> Idx) : Real) *
            ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
              (connActConst (Idx := Idx) r s
                (Real.sqrt
                  (normSqRS (I := I) (g := g) (x := x₀) 1 2
                    (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
                (Real.sqrt
                  (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)))) ^ 2)) := by
  have htri :=
    sqrt_normRS_le_add_sub
      (I := I) (g := g) (x := x₀) r (s + 1) (nablaT x₀) (nablaT' x₀)
  have hdiff :=
    totalNablaSubNorm_le
      (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (Idx := Idx) g cov cov' T nablaT nablaT'
      hreal hreal' β x₀ basis hinv Xfield V hX_at hβ_at hV_at hpairT
      hpairβ hβmodel hV hVmodel hcoord
  exact htri.trans (add_le_add (le_refl _) hdiff)

set_option backward.isDefEq.respectTransparency false in
/-- Epsilon-shaped first-order total one-step inequality.

This is the form consumed by the scalar Lemma 4.5 induction at `k = 0`: a
pointwise `eps`-bound for the connection difference and a pointwise bound for
`T` give an `eps`-multiple error term. -/
theorem totalNablaNorm_bound {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT nablaT' : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1))
    (hreal : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hreal' : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov' T nablaT')
    (β : (Fin r -> Idx) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E)
      (H := H) (I := I) (M := M) r x)
    (x₀ : M)
    (basis : Module.Basis Idx Real (TangentSpace I x₀))
    (hinv :
      MetricInverseInBasis (I := I) g x₀ basis (identityInvMetric (Idx := Idx)))
    (Xfield : Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Idx -> (x : M) -> TangentSpace I x)
    (hX_at : forall i : Idx, Xfield i x₀ = basis i)
    (hβ_at : forall upper : Fin r -> Idx,
      β upper x₀ = basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x₀ = basis i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => (T p (β upper p)) (fun a : Fin s => V (lower a.succ) p)) x₀)
    (hpairβ : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => β upper p (fun a : Fin r => V (slots a) p)) x₀)
    (hβmodel : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x₀ (β upper))
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x₀)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord j
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V i)
              (extChartAt I x₀ p))) x₀)
    {eps B N : Real} (heps : 0 <= eps)
    (hA :
      Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x₀)) <= eps * B)
    (hT :
      Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀)) <= N) :
    Real.sqrt
        (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
          (nablaT' x₀)) <=
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
            (nablaT x₀)) +
        eps * connActNormConst (Idx := Idx) r s B N := by
  have hbase :=
    totalNablaNorm_le
      (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (Idx := Idx) g cov cov' T nablaT nablaT'
      hreal hreal' β x₀ basis hinv Xfield V hX_at hβ_at hV_at hpairT
      hpairβ hβmodel hV hVmodel hcoord
  have herr :
      connActNormConst (Idx := Idx) r s
        (Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) 1 2
            (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
        (Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀))) <=
        eps * connActNormConst (Idx := Idx) r s B N :=
    connActNormConst_le_mul_left (Idx := Idx)
      heps (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hT
  have hbase' :
      Real.sqrt
          (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
            (nablaT' x₀)) <=
        Real.sqrt
            (normSqRS (I := I) (g := g) (x := x₀) r (s + 1)
              (nablaT x₀)) +
          connActNormConst (Idx := Idx) r s
            (Real.sqrt
              (normSqRS (I := I) (g := g) (x := x₀) 1 2
                (connectionDifferenceTensorAt (I := I) cov cov' x₀)))
            (Real.sqrt
              (normSqRS (I := I) (g := g) (x := x₀) r s (T x₀))) := by
    simpa [connActNormConst] using hbase
  exact hbase'.trans (add_le_add_right herr _)

end

end Tensor0SBundle
