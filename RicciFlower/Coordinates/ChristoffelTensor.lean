import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.LocalCoframe
import RicciFlower.Coordinates.MetricCompatibility.Covariant
import RicciFlower.Coordinates.NablaComponents.OneForm.Smoothness
import RicciFlower.Coordinates.NablaComponents.TensorRS.Special12
import RicciFlower.Coordinates.Tensor
import RicciFlower.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import RicciFlower.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Christoffel Components of the Connection-Difference Tensor

This file is the coordinate projection of the invariant connection-difference
tensor.  It identifies the `(1,2)` tensor introduced in the tensor layer with
the existing local-frame Christoffel-difference components.
-/

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle Module Tensor0SBundle
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

private theorem sub_swap_of_sub_eq_sub
    {V : Type*} [AddCommGroup V] {a b c d : V}
    (h : a - b = c - d) :
    a - c = b - d := by
  have ha : a = (c - d) + b := sub_eq_iff_eq_add.mp h
  calc
    a - c = ((c - d) + b) - c := by rw [ha]
    _ = b - d := by abel

/-- Local-frame `(1,2)` components of the invariant
`connectionDifferenceTensorAt` are the existing Christoffel-symbol difference
components. -/
theorem tensor12Comp_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j k : Idx) :
    tensor12CompInFrame (I := I)
        (fun y : M => connectionDifferenceTensorAt (I := I) cov cov' y)
        frame hframe x hx k i j =
      christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k := by
  unfold tensor12CompInFrame tensorRSComponentInFrame
    christoffelSymbolDifferenceInFrame
  change
    componentRS (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      (hframe.coeff k x)
        (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- In a local frame whose inverse-metric components are the identity, the
invariant squared norm of the connection-difference tensor is the sum of
squares of the Christoffel-symbol difference components. -/
theorem normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum
    [IsManifold I ∞ M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      MetricInverseInBasis (I := I) g x (hframe.toBasisAt hx)
        (identityInvMetric (Idx := Idx))) :
    normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x) =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k) ^ 2 := by
  rw [normSqRS_one_two_identity_eq_sum (I := I) g x
    (hframe.toBasisAt hx) hinv
    (connectionDifferenceTensorAt (I := I) cov cov' x)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold christoffelSymbolDifferenceInFrame
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- Difference of two Levi-Civita connections is symmetric in its two tangent
inputs.  This is the invariant torsion-free content behind the symmetry of
`Gamma(g)-Gamma(h)`. -/
theorem lcDiffBasis_symm
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b : Idx) :
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis b)) (basis a) =
      ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis a)) (basis b) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hXd :
      MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd :
      MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hdY :
      ((CovariantDerivative.difference covG covH x) (Y x)) (X x) =
        ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covG.isCovariantDerivativeOnUniv)
        (hcov' := covH.isCovariantDerivativeOnUniv)
        (σ := fun p : M => Y p) (x := x) (hx := by trivial) hYd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (X x)) hdiff
  have hdX :
      ((CovariantDerivative.difference covG covH x) (X x)) (Y x) =
        ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covG.isCovariantDerivativeOnUniv)
        (hcov' := covH.isCovariantDerivativeOnUniv)
        (σ := fun p : M => X p) (x := x) (hx := by trivial) hXd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (Y x)) hdiff
  have htorG :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) g)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have htorH :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) h)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have hsub :
      ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) =
        ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
    have htor : ((covG (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => X p) x) (Y x)) =
        ((covH (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
      rw [htorG, htorH]
    exact sub_swap_of_sub_eq_sub htor
  calc
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis b)) (basis a)
        = ((CovariantDerivative.difference covG covH x) (Y x)) (X x) := by
          simp [covG, covH, hX, hY]
    _ = ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) := hdY
    _ = ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := hsub
    _ = ((CovariantDerivative.difference covG covH x) (X x)) (Y x) := hdX.symm
    _ = ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis a)) (basis b) := by
          simp [covG, covH, hX, hY]

/-- Component form of `lcDiffBasis_symm`. -/
theorem lcDiff_symm
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b e : Idx) :
    componentRS (I := I) basis
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      componentRS (I := I) basis
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then b else a) := by
  rw [componentRS_connectionDifferenceTensorAt]
  rw [componentRS_connectionDifferenceTensorAt]
  exact congrArg (basis.coord e)
    (lcDiffBasis_symm (I := I) g h basis a b)

/-- Local-frame components of `Gamma_g - Gamma_h`, the Levi-Civita
connection-difference tensor. -/
def lcDiffCompInFrame
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (a b e : Idx) : Real :=
  christoffelSymbolDifferenceInFrame
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
    frame hframe x a b e

/-- The local-frame component definition agrees with the invariant
connection-difference tensor. -/
theorem lcDiffCompInFrame_eq_component
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (a b e : Idx) :
    componentRS (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      lcDiffCompInFrame (I := I) g h frame hframe x a b e := by
  rw [componentRS_connectionDifferenceTensorAt]
  simp [lcDiffCompInFrame, christoffelSymbolDifferenceInFrame,
    IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- Local scalar evaluation of a supplied connection-difference field agrees
eventually with the corresponding local-frame Christoffel-difference component.

The one-form input is not arbitrary: it is certified locally as the dual coframe
by its pairings with the local frame extensions.  This is the scalar
eventual-equality needed by moving-slot covariant-derivative formulas. -/
theorem lcDiffComp_eventually
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b e : Idx)
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x] fun y : M => frame j y)
    (hpair : ∀ j : Idx,
      (fun y : M => α y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x]
        fun _ : M => if j = e then (1 : Real) else 0) :
    (fun y : M =>
      (D y (α y)) (fun q : Fin 2 => Z (lowerIdx2 a b q) y))
      =ᶠ[𝓝 x]
    fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e := by
  classical
  have hcof :=
    oneForm_eventually_eq_localFrame_dual
      (I := I) Z α frame hframe (x₀ := x) e hZ hpair
  have hZall : ∀ᶠ y in 𝓝 x, ∀ j : Idx, Z j y = frame j y := by
    exact Filter.eventually_all.mpr hZ
  filter_upwards [hu.mem_nhds hx, hcof, hZall] with y hy hcofy hZy
  let basis := hframe.toBasisAt hy
  have hslots :
      (fun q : Fin 2 => Z (lowerIdx2 a b q) y) =
        fun q : Fin 2 => basis (lowerIdx2 a b q) := by
    funext q
    simp [basis, IsLocalFrameOn.toBasisAt_coe, hZy (lowerIdx2 a b q)]
  have hcomp :=
    lcDiffCompInFrame_eq_component
      (I := I) g h frame hframe (x := y) hy a b e
  calc
    (D y (α y)) (fun q : Fin 2 => Z (lowerIdx2 a b q) y)
        = (D y (basisTensor0S (I := I) (hframe.toBasisAt hy)
            (fun _ : Fin 1 => e)))
            (fun q : Fin 2 => Z (lowerIdx2 a b q) y) := by
          rw [hcofy hy]
    _ = (D y (basisTensor0S (I := I) (hframe.toBasisAt hy)
            (fun _ : Fin 1 => e)))
            (fun q : Fin 2 => basis (lowerIdx2 a b q)) := by
          rw [hslots]
    _ = componentRS (I := I) basis (D y)
          (fun _ : Fin 1 => e) (lowerIdx2 a b) := by
          simp [componentRS_apply, basis]
    _ = lcDiffCompInFrame (I := I) g h frame hframe y a b e := by
          simpa [basis, hD y] using hcomp

/-- Coordinate-frame components of a supplied field realizing
`connectionDifferenceTensorAt` are the local Christoffel-difference
components. -/
theorem coordComponentRS_lcDiff_coordFrame
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (x₀ : M) (a b e : CoordinateIdx (𝕜 := Real) E) :
    coordComponentRSAt (I := I) (D x₀) (upperIdx1 e) (lowerIdx2 a b) =
      lcDiffCompInFrame
        (I := I) g h (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ a b e := by
  have hcomp :=
    lcDiffCompInFrame_eq_component
      (I := I) g h (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (x := x₀) (coordinateFrameAt_mem (I := I) x₀) a b e
  simpa [coordComponentRSAt, coordinateFrameAt_toBasis, hD x₀] using hcomp

/-- Local-frame component of the covariant derivative, with respect to
`h`'s Levi-Civita connection, of the Christoffel-difference tensor
`Gamma(g)-Gamma(h)`.

The slot order is `d,a,b,e`, meaning
`(nabla^h_d (Gamma(g)-Gamma(h)))^e_ab`. -/
def lcDiffCovDerivCompInFrame
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b e : Idx) : Real :=
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  extDerivFun (I := I)
      (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
      x (frame d x) +
    (∑ p : Idx,
      christoffelSymbolInFrame covH frame hframe x d p e *
        lcDiffCompInFrame (I := I) g h frame hframe x a b p) -
    (∑ p : Idx,
      christoffelSymbolInFrame covH frame hframe x d a p *
        lcDiffCompInFrame (I := I) g h frame hframe x p b e) -
    (∑ p : Idx,
      christoffelSymbolInFrame covH frame hframe x d b p *
        lcDiffCompInFrame (I := I) g h frame hframe x a p e)

/-- Directional derivative of a coordinate-frame component of a supplied
connection-difference field agrees with the scalar derivative of the
corresponding Christoffel-difference component. -/
theorem coordDerivRSAt_lcDiff_coordFrame
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (X : (x : M) -> TangentSpace I x)
    (x₀ : M) (a b e : CoordinateIdx (𝕜 := Real) E) :
    coordDerivRSAt (I := I) X x₀ (fun y => D y) (upperIdx1 e) (lowerIdx2 a b) =
      extDerivFun (I := I)
        (fun y : M =>
          lcDiffCompInFrame
            (I := I) g h (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀) y a b e)
        x₀ (X x₀) := by
  unfold coordDerivRSAt
  change
    extDerivFun (I := I)
        (fun y : M =>
          (D y
            (Tensor0SSpace.constInChart
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (upperIdx1 e)) y))
            (fun b' : Fin 2 =>
              coordinateFrameAt (I := I) x₀ (lowerIdx2 a b b') y))
        x₀ (X x₀) =
      extDerivFun (I := I)
        (fun y : M =>
          lcDiffCompInFrame
            (I := I) g h (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀) y a b e)
        x₀ (X x₀)
  exact extDerivFun_congr_eventually (I := I) (X x₀) (by
    filter_upwards
      [(coordinateFrameSet_open (I := I) x₀).mem_nhds
        (coordinateFrameAt_mem (I := I) x₀)] with y hy
    have hconst :=
      constInChart_eq_basis0S_coordFrame
        (𝕜 := Real) (I := I) (M := M) (r := 1) x₀ hy
        (upperIdx1 e)
    have hcomp :=
      lcDiffCompInFrame_eq_component
        (I := I) g h (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (x := y) hy a b e
    simpa [coordComponentRSAt, componentRS_apply, hD y, hconst,
      coordinateFrameAt_basis, coordinateFrameAt_basis_apply,
      IsLocalFrameOn.toBasisAt_coe] using hcomp)

/-- A realized total `h`-covariant derivative of a supplied
connection-difference field has coordinate-frame components given by
`lcDiffCovDerivCompInFrame`. -/
theorem totalNabla_lcDiff_coordFrame
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (D1 : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (hD1 :
      TotalNablaRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x₀ : M) (d a b e : CoordinateIdx (𝕜 := Real) E)
    (hX : X x₀ = coordinateFrameAt (I := I) x₀ d x₀) :
    componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀)
        (D1 x₀) (upperIdx1 e) (slots3 d a b) =
      lcDiffCovDerivCompInFrame
        (I := I) g h (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ d a b e := by
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  let β := basisTensor0S (I := I) basis (upperIdx1 e)
  let slots : Fin 2 -> TangentSpace I x₀ :=
    fun q => basis (lowerIdx2 a b q)
  have hslots :
      (fun q : Fin 3 => basis (slots3 d a b q)) =
        Fin.cons (X x₀) slots := by
    funext q
    fin_cases q
    · simp [basis, slots, hX, slots3]
    · change basis (slots3 d a b 1) = slots 0
      simp [basis, slots, slots3, lowerIdx2]
    · change basis (slots3 d a b 2) = slots 1
      simp [basis, slots, slots3, lowerIdx2]
  have happly := hD1.apply X x₀ β slots
  have hcoord :=
    nablaRS_coordFrame_1_2_of_smooth
      (𝕜 := Real) (I := I) covH X D x₀ e a b
  calc
    componentRS (I := I) (coordinateFrameAt_toBasis (I := I) x₀)
        (D1 x₀) (upperIdx1 e) (slots3 d a b)
        = D1 x₀ β (fun q : Fin 3 => basis (slots3 d a b q)) := by
          simp [componentRS_apply, β, basis]
    _ = D1 x₀ β (Fin.cons (X x₀) slots) := by
          rw [hslots]
    _ = nablaRSFun
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 2 covH X D x₀ β slots := happly
    _ = coordComponentRSAt (I := I)
          (nablaRSFun
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            1 2 covH X D x₀)
          (upperIdx1 e) (lowerIdx2 a b) := by
          simp [coordComponentRSAt, componentRS_apply, β, basis, slots]
    _ = lcDiffCovDerivCompInFrame
        (I := I) g h (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ d a b e := by
          rw [hcoord]
          rw [coordDerivRSAt_lcDiff_coordFrame
            (I := I) g h D hD (fun y => X y) x₀ a b e]
          simp_rw [coordComponentRS_lcDiff_coordFrame
            (I := I) g h D hD x₀]
          simp [lcDiffCovDerivCompInFrame, covH, hX]


/-- Upper-slot correction term for the moving-slot derivative of the
Christoffel-difference tensor in a local frame.

This is the contribution from differentiating the dual coframe input:
`D(∇θ^e)(e_a,e_b) = -∑_p Γ^e_p(X) D^p_ab`. -/
theorem lcDiffUpperCorr
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (i a b : Idx)
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x] fun y : M => frame j y)
    (hpair : ∀ j : Idx,
      (fun y : M => α y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x]
        fun _ : M => if j = i then (1 : Real) else 0)
    (hα_eval : ∀ W : TangentSpace I x,
      α x (fun _ : Fin 1 => W) = hframe.coeff i x W) :
    (D x
      (localCovariantDerivTensor0SAt
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X
        (fun y : M => α y) x))
      (fun q : Fin 2 => (hframe.toBasisAt hx) (lowerIdx2 a b q)) =
      -∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) p i *
          lcDiffCompInFrame (I := I) g h frame hframe x a b p := by
  classical
  let basis := hframe.toBasisAt hx
  have hcof :=
    localCovariantDerivTensor0SAt_one_localFrame_dual_eq
      (I := I) cov X Z α frame hframe hu hx i hZ hpair hα_eval
  have hcomp : ∀ p : Idx,
      (D x (basisTensor0S (I := I) basis (fun _ : Fin 1 => p)))
          (fun q : Fin 2 => basis (lowerIdx2 a b q)) =
        lcDiffCompInFrame (I := I) g h frame hframe x a b p := by
    intro p
    have hcomp0 :=
      lcDiffCompInFrame_eq_component
        (I := I) g h frame hframe (x := x) hx a b p
    simpa [componentRS_apply, basis, hD x] using hcomp0
  calc
    (D x
      (localCovariantDerivTensor0SAt
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X
        (fun y : M => α y) x))
      (fun q : Fin 2 => basis (lowerIdx2 a b q))
        =
      (D x
        (-∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x (X x) p i •
            basisTensor0S (I := I) basis (fun _ : Fin 1 => p)))
        (fun q : Fin 2 => basis (lowerIdx2 a b q)) := by
          rw [hcof]
    _ = -∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) p i *
          lcDiffCompInFrame (I := I) g h frame hframe x a b p := by
          let S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x :=
            ∑ p : Idx,
              christoffelAlongInFrame cov frame hframe x (X x) p i •
                basisTensor0S (I := I) basis (fun _ : Fin 1 => p)
          have hneg : (D x) (-S) = - (D x) S := map_neg (D x) S
          have hsumD :
              (D x) S =
                ∑ p : Idx,
                  (D x)
                    (christoffelAlongInFrame cov frame hframe x (X x) p i •
                      basisTensor0S (I := I) basis (fun _ : Fin 1 => p)) := by
            simp [S, map_sum]
          change (((D x) (-S)) (fun q : Fin 2 => basis (lowerIdx2 a b q))) =
            -∑ p : Idx,
              christoffelAlongInFrame cov frame hframe x (X x) p i *
                lcDiffCompInFrame (I := I) g h frame hframe x a b p
          rw [hneg, hsumD]
          rw [ContinuousMultilinearMap.neg_apply]
          rw [tensor0S_sum_apply]
          simp [map_smul, hcomp]

/-- First lower-slot correction term for the moving-slot derivative of the
Christoffel-difference tensor in a local frame. -/
theorem lcDiffLowerCorr0
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (e a b : Idx) :
    (D x (basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 e)))
      (Function.update
        (fun q : Fin 2 => (hframe.toBasisAt hx) (lowerIdx2 a b q)) 0
        ((cov (frame a) x) (X x))) =
      ∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) a p *
          lcDiffCompInFrame (I := I) g h frame hframe x p b e := by
  classical
  let basis := hframe.toBasisAt hx
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    D x (basisTensor0S (I := I) basis (upperIdx1 e))
  have hcomp : ∀ p : Idx,
      component0S (I := I) basis A (lowerIdx2 p b) =
        lcDiffCompInFrame (I := I) g h frame hframe x p b e := by
    intro p
    have h :=
      lcDiffCompInFrame_eq_component
        (I := I) g h frame hframe (x := x) hx p b e
    simpa [A, componentRS_apply, basis, hD x] using h
  have hcomp_apply : ∀ p : Idx,
      A (fun q : Fin 2 => frame (lowerIdx2 p b q) x) =
        lcDiffCompInFrame (I := I) g h frame hframe x p b e := by
    intro p
    simpa [component0S_apply, basis, IsLocalFrameOn.toBasisAt_coe]
      using hcomp p
  have hcoeff : ∀ p : Idx,
      (basis.repr ((cov (frame a) x) (X x))) p =
        christoffelAlongInFrame cov frame hframe x (X x) a p := by
    intro p
    simp [basis, christoffelAlongInFrame, IsLocalFrameOn.coeff, hx]
  have hupdate :=
    component0S_update_basis_sum
      (I := I) basis A (lowerIdx2 a b) (0 : Fin 2)
      ((cov (frame a) x) (X x))
  simpa [A, basis, IsLocalFrameOn.toBasisAt_coe,
    Function_update_lowerIdx2_zero, hcoeff, hcomp_apply] using hupdate

/-- Second lower-slot correction term for the moving-slot derivative of the
Christoffel-difference tensor in a local frame. -/
theorem lcDiffLowerCorr1
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (e a b : Idx) :
    (D x (basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 e)))
      (Function.update
        (fun q : Fin 2 => (hframe.toBasisAt hx) (lowerIdx2 a b q)) 1
        ((cov (frame b) x) (X x))) =
      ∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) b p *
          lcDiffCompInFrame (I := I) g h frame hframe x a p e := by
  classical
  let basis := hframe.toBasisAt hx
  let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    D x (basisTensor0S (I := I) basis (upperIdx1 e))
  have hcomp : ∀ p : Idx,
      component0S (I := I) basis A (lowerIdx2 a p) =
        lcDiffCompInFrame (I := I) g h frame hframe x a p e := by
    intro p
    have h :=
      lcDiffCompInFrame_eq_component
        (I := I) g h frame hframe (x := x) hx a p e
    simpa [A, componentRS_apply, basis, hD x] using h
  have hcomp_apply : ∀ p : Idx,
      A (fun q : Fin 2 => frame (lowerIdx2 a p q) x) =
        lcDiffCompInFrame (I := I) g h frame hframe x a p e := by
    intro p
    simpa [component0S_apply, basis, IsLocalFrameOn.toBasisAt_coe]
      using hcomp p
  have hcoeff : ∀ p : Idx,
      (basis.repr ((cov (frame b) x) (X x))) p =
        christoffelAlongInFrame cov frame hframe x (X x) b p := by
    intro p
    simp [basis, christoffelAlongInFrame, IsLocalFrameOn.coeff, hx]
  have hupdate :=
    component0S_update_basis_sum
      (I := I) basis A (lowerIdx2 a b) (1 : Fin 2)
      ((cov (frame b) x) (X x))
  simpa [A, basis, IsLocalFrameOn.toBasisAt_coe,
    Function_update_lowerIdx2_one, hcoeff, hcomp_apply] using hupdate

set_option backward.isDefEq.respectTransparency false in
/-- A realized total `h`-covariant derivative of a supplied
connection-difference field has local-frame components given by
`lcDiffCovDerivCompInFrame`.

The local sections `Z` and `α` certify the moving lower frame vectors and upper
dual coframe used to evaluate the scalar derivative term. -/
theorem totalNabla_lcDiff_localFrame
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (D1 : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (hD1 :
      TotalNablaRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x] fun y : M => frame j y)
    (hpair : ∀ j : Idx,
      (fun y : M => α y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x]
        fun _ : M => if j = e then (1 : Real) else 0) :
    componentRS (I := I) (hframe.toBasisAt hx) (D1 x) (upperIdx1 e)
        (slots3 d a b) =
      lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let V : Fin 2 -> (y : M) -> TangentSpace I y :=
    fun q y => Z (lowerIdx2 a b q) y
  let Vsec : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun q => Z (lowerIdx2 a b q)
  have hcof_ev :=
    oneForm_eventually_eq_localFrame_dual
      (I := I) Z α frame hframe (x₀ := x) e hZ hpair
  have hα_eq : α x = basisTensor0S (I := I) basis (upperIdx1 e) := by
    have h0 := hcof_ev.self_of_nhds
    simpa [basis, upperIdx1] using h0 hx
  have hα_eval : ∀ W : TangentSpace I x,
      α x (fun _ : Fin 1 => W) = hframe.coeff e x W := by
    intro W
    rw [hα_eq]
    simp [basis, basisTensor0S_apply, IsLocalFrameOn.coeff, hx]
  have hX_at : X x = basis (slots3 d a b 0) := by
    simpa [basis, slots3, IsLocalFrameOn.toBasisAt_coe] using hX
  have hV_at : ∀ q : Fin 2, V q x = basis (slots3 d a b q.succ) := by
    intro q
    have hZq := (hZ (lowerIdx2 a b q)).eq_of_nhds
    fin_cases q <;>
      simpa [V, basis, slots3, lowerIdx2, IsLocalFrameOn.toBasisAt_coe] using hZq
  have hVslots :
      (fun q : Fin 2 => V q x) =
        fun q : Fin 2 => basis (lowerIdx2 a b q) := by
    funext q
    have hZq := (hZ (lowerIdx2 a b q)).eq_of_nhds
    simp [V, basis, IsLocalFrameOn.toBasisAt_coe, hZq]
  have hpairDiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => (D p (α p)) (fun q : Fin 2 => V q p)) x := by
    have hsmooth :=
      tensorRSField_eval_smooth_input_slots_contMDiffAt
        (I := I) D α Vsec x
    simpa [V, Vsec] using hsmooth.mdifferentiableAt (by simp)
  have hβmodel : DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 1 x (fun p : M => α p))
      (Set.range I) (extChartAt I x x) := by
    exact tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) α x (α.contMDiff x)
  have hV : ∀ q : Fin 2, MDiffAt (T% (V q)) x := by
    intro q
    simpa [V] using
      (Z (lowerIdx2 a b q)).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ q : Fin 2,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart
          (𝕜 := Real) (I := I) x (V q))
        (Set.range I) (extChartAt I x x) := by
    intro q
    exact tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) (V q) x (by
        simpa [V] using (Z (lowerIdx2 a b q)).contMDiff.contMDiffAt)
  have hcoord : ∀ q : Fin 2, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (TensorLieDeriv.tangentFieldModelInChart
              (𝕜 := Real) (I := I) x (V q)
              (extChartAt I x p))) x := by
    intro q i
    exact tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
      (I := I) (V q) x (by
        simpa [V] using (Z (lowerIdx2 a b q)).contMDiff.contMDiffAt) i
  have hraw :=
    TotalNablaRSRealizes.component_moving_slots
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      hD1 X (fun y : M => α y) V x basis (upperIdx1 e) (slots3 d a b)
      hα_eq hX_at hV_at hpairDiff hβmodel hV hVmodel hcoord
  have hext :
      extDerivFun (I := I)
          (fun p : M => (D p (α p)) (fun q : Fin 2 => V q p)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
          x (frame d x) := by
    have hlocal :=
      lcDiffComp_eventually
        (I := I) g h D hD Z α frame hframe hu hx a b e hZ hpair
    calc
      extDerivFun (I := I)
          (fun p : M => (D p (α p)) (fun q : Fin 2 => V q p)) x (X x)
          =
        extDerivFun (I := I)
          (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
          x (X x) := by
            exact extDerivFun_congr_eventually (I := I) (X x) (by
              simpa [V] using hlocal)
      _ =
        extDerivFun (I := I)
          (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
          x (frame d x) := by
            rw [hX]
  have hupper :
      (D x
        (localCovariantDerivTensor0SAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 covH X
          (fun y : M => α y) x))
        (fun q : Fin 2 => V q x) =
      -∑ p : Idx,
        christoffelSymbolInFrame covH frame hframe x d p e *
          lcDiffCompInFrame (I := I) g h frame hframe x a b p := by
    have h :=
      lcDiffUpperCorr
        (I := I) g h D hD covH X Z α frame hframe hu hx e a b
        hZ hpair hα_eval
    simpa [V, basis, hVslots, hX, christoffelAlongInFrame_frame] using h
  have hcov0 :
      covH (V 0) x = covH (frame a) x := by
    have hV0 : MDiffAt (T% (V 0)) x := hV 0
    have hframe0 : MDiffAt (T% (frame a)) x :=
      (hframe.contMDiffAt hu hx a).mdifferentiableAt one_ne_zero
    exact covH.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hV0 hframe0 (by simp) (by
        simpa [V, lowerIdx2] using hZ a)
  have hcov1 :
      covH (V 1) x = covH (frame b) x := by
    have hV1 : MDiffAt (T% (V 1)) x := hV 1
    have hframe1 : MDiffAt (T% (frame b)) x :=
      (hframe.contMDiffAt hu hx b).mdifferentiableAt one_ne_zero
    exact covH.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hV1 hframe1 (by simp) (by
        simpa [V, lowerIdx2] using hZ b)
  have hlower0 :
      (D x (α x))
        (Function.update (fun q : Fin 2 => V q x) 0
          ((covH (V 0) x) (X x))) =
      ∑ p : Idx,
        christoffelSymbolInFrame covH frame hframe x d a p *
          lcDiffCompInFrame (I := I) g h frame hframe x p b e := by
    have h :=
      lcDiffLowerCorr0
        (I := I) g h D hD covH X frame hframe hx e a b
    simpa [hα_eq, hVslots, hcov0, hX, basis,
      IsLocalFrameOn.toBasisAt_coe, christoffelAlongInFrame_frame] using h
  have hlower1 :
      (D x (α x))
        (Function.update (fun q : Fin 2 => V q x) 1
          ((covH (V 1) x) (X x))) =
      ∑ p : Idx,
        christoffelSymbolInFrame covH frame hframe x d b p *
          lcDiffCompInFrame (I := I) g h frame hframe x a p e := by
    have h :=
      lcDiffLowerCorr1
        (I := I) g h D hD covH X frame hframe hx e a b
    simpa [hα_eq, hVslots, hcov1, hX, basis,
      IsLocalFrameOn.toBasisAt_coe, christoffelAlongInFrame_frame] using h
  rw [hraw]
  simp only [Fin.sum_univ_two]
  rw [hext, hupper, hlower0, hlower1]
  simp [lcDiffCovDerivCompInFrame, covH]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- Trivialization-local-frame version of `totalNabla_lcDiff_localFrame`.

This wrapper chooses the smooth local frame and coframe section extensions from
`existsTrivFrameCoframePair`, so callers only provide the tangent
trivialization model basis and no longer pass arbitrary frame/coframe pairing
assumptions. -/
theorem totalNabla_lcDiff_trivFrame
    [CompleteSpace E] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (D : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (D1 : TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3)
    (hD : ∀ y : M,
      D y =
        connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) y)
    (hD1 :
      TotalNablaRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (basisE : Module.Basis Idx Real E) {x : M}
    (d a b e : Idx)
    (hX :
      X x =
        (trivializationAt E (TangentSpace I : M -> Type _) x).localFrame basisE d x) :
    let e₀ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => e₀.localFrame basisE i y
    let u : Set M := e₀.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE
    let hx : x ∈ u := mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
    componentRS (I := I) (hframe.toBasisAt hx) (D1 x) (upperIdx1 e)
        (slots3 d a b) =
      lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e := by
  classical
  let e₀ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => e₀.localFrame basisE i y
  let u : Set M := e₀.baseSet
  let hframe : IsLocalFrameOn I E 1 frame u :=
    e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hu : IsOpen u := e₀.open_baseSet
  have hx : x ∈ u := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  obtain ⟨Z, θ, hZ, _hθ, hpair⟩ :=
    existsTrivFrameCoframePair (J := I) (N := M) x basisE
  exact
    totalNabla_lcDiff_localFrame
      (I := I) (M := M) (Idx := Idx) (u := u)
      g h D D1 hD hD1 X Z (θ e) frame hframe hu hx d a b e
      (by
        change X x = e₀.localFrame basisE d x
        exact hX)
      (by
        intro j
        simpa [frame] using hZ j)
      (by
        intro j
        simpa using hpair e j)

/-- The symmetrized covariant derivative of `g` appearing in DC1:
`A_{abc} + A_{bac} - A_{cab}`, where `A = ∇_h g`. -/
def lcDiffSymMetricCovComp
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (a b c : Idx) : Real :=
  metricCovDerivForMetricCompInFrame (I := I) g cov frame hframe x a b c +
    metricCovDerivForMetricCompInFrame (I := I) g cov frame hframe x b a c -
    metricCovDerivForMetricCompInFrame (I := I) g cov frame hframe x c a b

/-- The RHS of the first covariant derivative of DC1, before replacing
`∇ g^{-1}` by the quadratic `g^{-1}*(∇g)*g^{-1}` expression. -/
def lcDiffCovDerivRHS
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b e : Idx) : Real :=
  (∑ c : Idx,
    inverseMetricCovDerivForMetricCompInFrame
        (I := I) gInv cov frame hframe x d e c *
      lcDiffSymMetricCovComp (I := I) g cov frame hframe x a b c) +
    (∑ c : Idx,
      gInv x e c *
        (metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d a b c +
          metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d b a c -
          metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d c a b))

/-- The first-derivative DC1 RHS after substituting
`nabla g^{-1} = - g^{-1} * (nabla g) * g^{-1}`.

This contains only second covariant derivatives of `g` and quadratic products
of first covariant derivatives of `g`. -/
def lcDiffQuadRHS
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b e : Idx) : Real :=
  (∑ c : Idx,
    (-(∑ r : Idx, ∑ q : Idx,
      gInv x e r * gInv x c q *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x d r q)) *
      lcDiffSymMetricCovComp (I := I) g cov frame hframe x a b c) +
    (∑ c : Idx,
      gInv x e c *
        (metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d a b c +
          metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d b a c -
          metricCovDeriv2ForMetricCompInFrame
            (I := I) g cov frame hframe x d c a b))

/-- Component form of `∇_h g` expressed by the connection difference
`D = Gamma(g) - Gamma(h)`. -/
theorem covMetric_lcDiff
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b c : Idx) :
    metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x a b c =
      (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else b) *
        metricCompForMetricInFrame (I := I) g frame x p c) +
      (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else c) *
        metricCompForMetricInFrame (I := I) g frame x b p) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) (hframe.toBasisAt hx)
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  have hframe_b : MDiffAt (T% (frame b)) x :=
    (hframe.contMDiffAt hu hx b).mdifferentiableAt one_ne_zero
  have hframe_c : MDiffAt (T% (frame c)) x :=
    (hframe.contMDiffAt hu hx c).mdifferentiableAt one_ne_zero
  have hDsub : ∀ i j k : Idx,
      D i j k =
        christoffelSymbolInFrame covG frame hframe x i j k -
          christoffelSymbolInFrame covH frame hframe x i j k := by
    intro i j k
    have hj : MDiffAt (T% (frame j)) x :=
      (hframe.contMDiffAt hu hx j).mdifferentiableAt one_ne_zero
    have hsub :=
      christoffelSymbolDifferenceInFrame_eq_sub
        covG covH frame hframe (x := x) i j k hj
    unfold D
    rw [componentRS_connectionDifferenceTensorAt]
    simpa [covG, covH, christoffelSymbolDifferenceInFrame,
      IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using hsub
  have hderiv :=
    metricCompForMetricInFrame_extDerivFun_eq_christoffel
      (I := I) g covG
      (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      frame hframe hu hx a b c
  unfold metricCovDerivForMetricCompInFrame
  rw [hderiv]
  change
    ((∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a b p * G p c) +
        (∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a c p * G b p)) -
      (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a b p * G p c) -
      (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a c p * G b p) =
    (∑ p : Idx, D a b p * G p c) + (∑ p : Idx, D a c p * G b p)
  simp only [hDsub]
  calc
    ((∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a b p * G p c) +
          (∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a c p * G b p)) -
        (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a b p * G p c) -
        (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a c p * G b p)
        =
      (∑ p : Idx,
        (christoffelSymbolInFrame covG frame hframe x a b p * G p c -
          christoffelSymbolInFrame covH frame hframe x a b p * G p c)) +
        (∑ p : Idx,
          (christoffelSymbolInFrame covG frame hframe x a c p * G b p -
            christoffelSymbolInFrame covH frame hframe x a c p * G b p)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ =
      (∑ p : Idx,
        ((christoffelSymbolInFrame covG frame hframe x a b p -
          christoffelSymbolInFrame covH frame hframe x a b p) * G p c)) +
        (∑ p : Idx,
          ((christoffelSymbolInFrame covG frame hframe x a c p -
            christoffelSymbolInFrame covH frame hframe x a c p) * G b p)) := by
          congr 1
          · refine Finset.sum_congr rfl fun p _hp => ?_
            ring
          · refine Finset.sum_congr rfl fun p _hp => ?_
            ring

/-- Koszul-style combination of the three `∇_h g` components. -/
theorem lcDiff_combo
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b e : Idx) :
    metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x a b e +
      metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x b a e -
      metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x e a b =
      2 * (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else b) *
        metricCompForMetricInFrame (I := I) g frame x p e) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let A : Idx -> Idx -> Idx -> Real := fun i j k =>
    metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x i j k
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) basis
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  have hA : ∀ i j k : Idx,
      A i j k = (∑ p : Idx, D i j p * G p k) +
        (∑ p : Idx, D i k p * G j p) := by
    intro i j k
    simpa [A, D, G, covG, covH, basis] using
      covMetric_lcDiff (I := I) g h frame hframe hu hx i j k
  have hsym : ∀ i j k : Idx, D i j k = D j i k := by
    intro i j k
    simpa [D, basis, covG, covH] using
      lcDiff_symm (I := I) g h basis i j k
  have hGsym : ∀ i j : Idx, G i j = G j i := by
    intro i j
    simpa [G, metricCompForMetricInFrame] using g.symm x (frame i x) (frame j x)
  have hcancel1 :
      (∑ p : Idx, D a e p * G b p) =
        (∑ p : Idx, D e a p * G p b) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym a e p, hGsym b p]
  have hcancel2 :
      (∑ p : Idx, D b e p * G a p) =
        (∑ p : Idx, D e b p * G a p) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym b e p]
  have hba :
      (∑ p : Idx, D b a p * G p e) =
        (∑ p : Idx, D a b p * G p e) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym b a p]
  change A a b e + A b a e - A e a b =
      2 * (∑ p : Idx, D a b p * G p e)
  rw [hA a b e, hA b a e, hA e a b]
  rw [hba]
  rw [hcancel1, hcancel2]
  ring

/-- DC1: local-frame Christoffel-difference equation
`Gamma_g - Gamma_h = 1/2 g^{-1} * sym(nabla_h g)`. -/
theorem lcDiffComp_eq
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (a b e : Idx) :
    2 *
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
      ∑ c : Idx,
        gInv x e c *
          (metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b c +
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x b a c -
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x c a b) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) basis
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  have hcombo : ∀ c : Idx,
      metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b =
      2 * (∑ p : Idx, D a b p * G p c) := by
    intro c
    simpa [D, G, covG, covH, basis] using
      lcDiff_combo (I := I) g h frame hframe hu hx a b c
  have hGsym : ∀ i j : Idx, G i j = G j i := by
    intro i j
    simpa [G, metricCompForMetricInFrame] using g.symm x (frame i x) (frame j x)
  have hcollapse :
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) =
        D a b e := by
    calc
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
          = ∑ p : Idx, D a b p *
              (∑ c : Idx, gInv x e c * G c p) := by
            calc
              (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
                  =
                ∑ c : Idx, ∑ p : Idx, gInv x e c * (D a b p * G p c) := by
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ c : Idx, gInv x e c * (D a b p * G p c) := by
                  rw [Finset.sum_comm]
              _ = ∑ p : Idx, D a b p *
                    (∑ c : Idx, gInv x e c * G c p) := by
                  refine Finset.sum_congr rfl fun p _hp => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [hGsym p c]
                  ring
      _ = ∑ p : Idx, D a b p * (if e = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [(hinv x e p).1]
      _ = D a b e := by
            simp
  change 2 * D a b e =
      ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b)
  calc
    2 * D a b e =
        2 * (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) := by
          rw [hcollapse]
    _ = ∑ c : Idx, gInv x e c * (2 * (∑ p : Idx, D a b p * G p c)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _hc => ?_
          ring
    _ = ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b) := by
          refine Finset.sum_congr rfl fun c _hc => ?_
          rw [hcombo c]

/-- DC1 written with the local-frame component abbreviation
`lcDiffCompInFrame`. -/
theorem lcDiffCompInFrame_eq
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (a b e : Idx) :
    2 * lcDiffCompInFrame (I := I) g h frame hframe x a b e =
      ∑ c : Idx,
        gInv x e c *
          (metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b c +
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x b a c -
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x c a b) := by
  rw [← lcDiffCompInFrame_eq_component
    (I := I) g h frame hframe hx a b e]
  exact lcDiffComp_eq (I := I) g h gInv frame hframe hu hx hinv a b e

/-- Local form of DC1 with only a pointwise inverse-metric hypothesis. -/
theorem lcDiffComp_eq_local
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvLeftX : forall i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0))
    (a b e : Idx) :
    2 *
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
      ∑ c : Idx,
        gInv x e c *
          (metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b c +
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x b a c -
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x c a b) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) basis
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  have hcombo : ∀ c : Idx,
      metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b =
      2 * (∑ p : Idx, D a b p * G p c) := by
    intro c
    simpa [D, G, covG, covH, basis] using
      lcDiff_combo (I := I) g h frame hframe hu hx a b c
  have hGsym : ∀ i j : Idx, G i j = G j i := by
    intro i j
    simpa [G, metricCompForMetricInFrame] using g.symm x (frame i x) (frame j x)
  have hcollapse :
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) =
        D a b e := by
    calc
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
          = ∑ p : Idx, D a b p *
              (∑ c : Idx, gInv x e c * G c p) := by
            calc
              (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
                  =
                ∑ c : Idx, ∑ p : Idx, gInv x e c * (D a b p * G p c) := by
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ c : Idx, gInv x e c * (D a b p * G p c) := by
                  rw [Finset.sum_comm]
              _ = ∑ p : Idx, D a b p *
                    (∑ c : Idx, gInv x e c * G c p) := by
                  refine Finset.sum_congr rfl fun p _hp => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [hGsym p c]
                  ring
      _ = ∑ p : Idx, D a b p * (if e = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hinvLeftX e p]
      _ = D a b e := by
            simp
  change 2 * D a b e =
      ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b)
  calc
    2 * D a b e =
        2 * (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) := by
          rw [hcollapse]
    _ = ∑ c : Idx, gInv x e c * (2 * (∑ p : Idx, D a b p * G p c)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _hc => ?_
          ring
    _ = ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b) := by
          refine Finset.sum_congr rfl fun c _hc => ?_
          rw [hcombo c]

/-- Local-frame abbreviation form of `lcDiffComp_eq_local`. -/
theorem lcDiffCompInFrame_eq_local
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvLeftX : forall i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0))
    (a b e : Idx) :
    2 * lcDiffCompInFrame (I := I) g h frame hframe x a b e =
      ∑ c : Idx,
        gInv x e c *
          (metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b c +
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x b a c -
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x c a b) := by
  rw [← lcDiffCompInFrame_eq_component
    (I := I) g h frame hframe hx a b e]
  exact lcDiffComp_eq_local
    (I := I) g h gInv frame hframe hu hx hinvLeftX a b e

/-- Directional derivative of DC1 along a local-frame vector.

This is the scalar product-rule part of the first positive-order
Christoffel-difference calculation.  It differentiates
`2 D = g^{-1} * sym(∇_h g)` before the Christoffel correction terms are
reassembled into a full covariant derivative. -/
theorem lcDiffCompInFrame_extDeriv_eq
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x)
    :
    2 * extDerivFun (I := I)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
        x (frame d x) =
      ∑ c : Idx,
        (gInv x e c *
          extDerivFun (I := I)
            (fun y : M =>
              lcDiffSymMetricCovComp
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe y a b c)
            x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c)
            x (frame d x) *
          lcDiffSymMetricCovComp
            (I := I) g
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe x a b c) := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let Dfun : M -> Real := fun y =>
    lcDiffCompInFrame (I := I) g h frame hframe y a b e
  let Sfun : Idx -> M -> Real := fun c y =>
    lcDiffSymMetricCovComp (I := I) g covH frame hframe y a b c
  let F : Idx -> M -> Real := fun c y => gInv y e c * Sfun c y
  have hS_mdiff : ∀ c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (Sfun c) x := by
    intro c
    dsimp [Sfun, lcDiffSymMetricCovComp]
    exact ((hA_mdiff a b c).add (hA_mdiff b a c)).sub (hA_mdiff c a b)
  have hF_mdiff : ∀ c ∈ (Finset.univ : Finset Idx),
      MDifferentiableAt I 𝓘(Real, Real) (F c) x := by
    intro c _hc
    exact (hginv_mdiff e c).mul (hS_mdiff c)
  have hDC_ev :
      (fun y : M => 2 * Dfun y) =ᶠ[nhds x]
        ((Finset.univ : Finset Idx).sum F) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    simpa [Dfun, F, Sfun, covH, lcDiffSymMetricCovComp] using
      lcDiffCompInFrame_eq
      (I := I) g h gInv frame hframe hu hy hinv a b e
  have hleft :
      extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) =
        2 * extDerivFun (I := I) Dfun x (frame d x) := by
    have h := RicciFlower.extDerivFun_const_mul
      (I := I) (c := (2 : Real)) (f := Dfun) (x := x) hD_mdiff
    have hv := DFunLike.congr_fun h (frame d x)
    simpa [Dfun, Pi.smul_apply, smul_eq_mul] using hv
  have hcongr :
      extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) =
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) :=
    deriv_congr_nhds (I := I) (frame d x) hDC_ev
  have hsum :
      extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
        ∑ c : Idx, extDerivFun (I := I) (F c) x (frame d x) := by
    simpa using
      extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
  have hprod : ∀ c : Idx,
      extDerivFun (I := I) (F c) x (frame d x) =
        gInv x e c * extDerivFun (I := I) (Sfun c) x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c) x (frame d x) *
            Sfun c x := by
    intro c
    simpa [F, Sfun, mul_comm, mul_left_comm, mul_assoc] using
      extDerivFun_mul_real
        (I := I) (x := x) (frame d x) (hginv_mdiff e c) (hS_mdiff c)
  calc
    2 * extDerivFun (I := I) Dfun x (frame d x)
        = extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) :=
          hleft.symm
    _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) :=
          hcongr
    _ = ∑ c : Idx, extDerivFun (I := I) (F c) x (frame d x) :=
          hsum
    _ = ∑ c : Idx,
        (gInv x e c *
          extDerivFun (I := I)
            (fun y : M =>
              lcDiffSymMetricCovComp
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe y a b c)
            x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c)
            x (frame d x) *
          lcDiffSymMetricCovComp
            (I := I) g
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe x a b c) := by
          refine Finset.sum_congr rfl fun c _hc => ?_
          simpa [Sfun, covH] using hprod c

/-- Local form of `lcDiffCompInFrame_extDeriv_eq`.

The inverse-metric identity is required only eventually near the base point,
which is the natural hypothesis for a local-frame inverse coefficient package. -/
theorem lcDiffCompInFrame_extDeriv_eq_local
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvLeftN : forall i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * extDerivFun (I := I)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
        x (frame d x) =
      ∑ c : Idx,
        (gInv x e c *
          extDerivFun (I := I)
            (fun y : M =>
              lcDiffSymMetricCovComp
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe y a b c)
            x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c)
            x (frame d x) *
          lcDiffSymMetricCovComp
            (I := I) g
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe x a b c) := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let Dfun : M -> Real := fun y =>
    lcDiffCompInFrame (I := I) g h frame hframe y a b e
  let Sfun : Idx -> M -> Real := fun c y =>
    lcDiffSymMetricCovComp (I := I) g covH frame hframe y a b c
  let F : Idx -> M -> Real := fun c y => gInv y e c * Sfun c y
  have hS_mdiff : ∀ c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (Sfun c) x := by
    intro c
    dsimp [Sfun, lcDiffSymMetricCovComp]
    exact ((hA_mdiff a b c).add (hA_mdiff b a c)).sub (hA_mdiff c a b)
  have hF_mdiff : ∀ c ∈ (Finset.univ : Finset Idx),
      MDifferentiableAt I 𝓘(Real, Real) (F c) x := by
    intro c _hc
    exact (hginv_mdiff e c).mul (hS_mdiff c)
  have hinvLeftAll :
      (∀ᶠ y in 𝓝 x, ∀ i j : Idx,
        (∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =
            (if i = j then 1 else 0)) := by
    exact Filter.eventually_all.mpr fun i =>
      Filter.eventually_all.mpr fun j => hinvLeftN i j
  have hDC_ev :
      (fun y : M => 2 * Dfun y) =ᶠ[nhds x]
        ((Finset.univ : Finset Idx).sum F) := by
    filter_upwards [hu.mem_nhds hx, hinvLeftAll] with y hy hinvy
    simpa [Dfun, F, Sfun, covH, lcDiffSymMetricCovComp] using
      lcDiffCompInFrame_eq_local
      (I := I) g h gInv frame hframe hu hy hinvy a b e
  have hleft :
      extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) =
        2 * extDerivFun (I := I) Dfun x (frame d x) := by
    have h := RicciFlower.extDerivFun_const_mul
      (I := I) (c := (2 : Real)) (f := Dfun) (x := x) hD_mdiff
    have hv := DFunLike.congr_fun h (frame d x)
    simpa [Dfun, Pi.smul_apply, smul_eq_mul] using hv
  have hcongr :
      extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) =
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) :=
    deriv_congr_nhds (I := I) (frame d x) hDC_ev
  have hsum :
      extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
        ∑ c : Idx, extDerivFun (I := I) (F c) x (frame d x) := by
    simpa using
      extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
  have hprod : ∀ c : Idx,
      extDerivFun (I := I) (F c) x (frame d x) =
        gInv x e c * extDerivFun (I := I) (Sfun c) x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c) x (frame d x) *
            Sfun c x := by
    intro c
    simpa [F, Sfun, mul_comm, mul_left_comm, mul_assoc] using
      extDerivFun_mul_real
        (I := I) (x := x) (frame d x) (hginv_mdiff e c) (hS_mdiff c)
  calc
    2 * extDerivFun (I := I) Dfun x (frame d x)
        = extDerivFun (I := I) (fun y : M => 2 * Dfun y) x (frame d x) :=
          hleft.symm
    _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) :=
          hcongr
    _ = ∑ c : Idx, extDerivFun (I := I) (F c) x (frame d x) :=
          hsum
    _ = ∑ c : Idx,
        (gInv x e c *
          extDerivFun (I := I)
            (fun y : M =>
              lcDiffSymMetricCovComp
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe y a b c)
            x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y e c)
            x (frame d x) *
          lcDiffSymMetricCovComp
            (I := I) g
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe x a b c) := by
          refine Finset.sum_congr rfl fun c _hc => ?_
          simpa [Sfun, covH] using hprod c

/-- Scalar derivative of the symmetrized `∇g` term in DC1.

This is the local-frame identity saying that differentiating
`A_{abc}+A_{bac}-A_{cab}` equals the corresponding second covariant derivative
combo plus the three lower-slot Christoffel corrections. -/
theorem lcDiffSymMetricCovComp_extDeriv_eq
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M}
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g cov frame hframe y i j k) x)
    (d a b c : Idx) :
    extDerivFun (I := I)
        (fun y : M =>
          lcDiffSymMetricCovComp (I := I) g cov frame hframe y a b c)
        x (frame d x) =
      metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a b c +
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d b a c -
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d c a b +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d a p *
            lcDiffSymMetricCovComp (I := I) g cov frame hframe x p b c) +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d b p *
            lcDiffSymMetricCovComp (I := I) g cov frame hframe x a p c) +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d c p *
            lcDiffSymMetricCovComp (I := I) g cov frame hframe x a b p) := by
  classical
  let A : Idx -> Idx -> Idx -> M -> Real := fun i j k y =>
    metricCovDerivForMetricCompInFrame (I := I) g cov frame hframe y i j k
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => A a b c y + A b a c y - A c a b y)
          x (frame d x) =
        extDerivFun (I := I) (A a b c) x (frame d x) +
          extDerivFun (I := I) (A b a c) x (frame d x) -
          extDerivFun (I := I) (A c a b) x (frame d x) := by
    have hadd := extDerivFun_add_real
      (I := I) (x := x) (frame d x) (hA_mdiff a b c) (hA_mdiff b a c)
    have hsum_mdiff : MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => A a b c y + A b a c y) x :=
      (hA_mdiff a b c).add (hA_mdiff b a c)
    have hsub := extDerivFun_sub_real
      (I := I) (x := x) (frame d x) hsum_mdiff (hA_mdiff c a b)
    calc
      extDerivFun (I := I)
          (fun y : M => A a b c y + A b a c y - A c a b y)
          x (frame d x)
          = extDerivFun (I := I) (fun y : M => A a b c y + A b a c y)
              x (frame d x) -
            extDerivFun (I := I) (A c a b) x (frame d x) := by
              simpa [sub_eq_add_neg] using hsub
      _ = extDerivFun (I := I) (A a b c) x (frame d x) +
            extDerivFun (I := I) (A b a c) x (frame d x) -
            extDerivFun (I := I) (A c a b) x (frame d x) := by
              rw [hadd]
  simp only [lcDiffSymMetricCovComp]
  change
    extDerivFun (I := I)
        (fun y : M => A a b c y + A b a c y - A c a b y)
        x (frame d x) =
      metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a b c +
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d b a c -
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d c a b +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d a p *
            (A p b c x + A b p c x - A c p b x)) +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d b p *
            (A a p c x + A p a c x - A c a p x)) +
        (∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x d c p *
            (A a b p x + A b a p x - A p a b x))
  rw [hderiv]
  unfold metricCovDeriv2ForMetricCompInFrame
  simp only [A]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]
  ring_nf

/-- First covariant derivative of the Christoffel-difference equation.

This reassembles the scalar derivative of DC1 with the local-frame correction
terms in the `(1,2)` Christoffel-difference tensor.  The result is still in
the coordinate layer: it expresses `∇_h (Γ_g - Γ_h)` through `∇_h g^{-1}` and
the second covariant derivatives of `g`, before substituting the inverse-metric
derivative formula. -/
theorem lcDiffCovDerivCompInFrame_eq
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
      lcDiffCovDerivRHS
        (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    lcDiffCompInFrame (I := I) g h frame hframe x i j k
  let S : Idx -> Idx -> Idx -> Real := fun i j k =>
    lcDiffSymMetricCovComp (I := I) g covH frame hframe x i j k
  let U : Idx -> Idx -> Real := fun i j => gInv x i j
  let DU : Idx -> Idx -> Real := fun i j =>
    inverseMetricCovDerivForMetricCompInFrame
      (I := I) gInv covH frame hframe x d i j
  let A2 : Idx -> Idx -> Idx -> Real := fun i j k =>
    metricCovDeriv2ForMetricCompInFrame (I := I) g covH frame hframe x d i j k
  let Γ : Idx -> Idx -> Real := fun i j =>
    christoffelSymbolInFrame covH frame hframe x d i j
  let extD : Real :=
    extDerivFun (I := I)
      (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
      x (frame d x)
  let extS : Idx -> Real := fun c =>
    extDerivFun (I := I)
      (fun y : M => lcDiffSymMetricCovComp (I := I) g covH frame hframe y a b c)
      x (frame d x)
  let extU : Idx -> Real := fun c =>
    extDerivFun (I := I) (fun y : M => gInv y e c) x (frame d x)
  have hDformula : ∀ i j k : Idx,
      2 * D i j k = ∑ c : Idx, U k c * S i j c := by
    intro i j k
    simpa [D, S, U, covH] using
      lcDiffCompInFrame_eq
        (I := I) g h gInv frame hframe hu hx hinv i j k
  have hscalar :
      2 * extD =
        ∑ c : Idx, (U e c * extS c + extU c * S a b c) := by
    simpa [extD, extS, extU, S, U, covH] using
      lcDiffCompInFrame_extDeriv_eq
        (I := I) g h gInv frame hframe hu hx hinv d a b e
        hD_mdiff hginv_mdiff hA_mdiff
  have hSderiv : ∀ c : Idx,
      extS c =
        A2 a b c + A2 b a c - A2 c a b +
          (∑ p : Idx, Γ a p * S p b c) +
          (∑ p : Idx, Γ b p * S a p c) +
          (∑ p : Idx, Γ c p * S a b p) := by
    intro c
    simpa [extS, A2, S, Γ, covH] using
      lcDiffSymMetricCovComp_extDeriv_eq
        (I := I) g covH frame hframe hA_mdiff d a b c
  have hDU : ∀ c : Idx,
      DU e c = extU c + (∑ p : Idx, Γ p e * U p c) +
        (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simp [DU, extU, U, Γ, inverseMetricCovDerivForMetricCompInFrame, covH]
  have hDUactual : ∀ c : Idx,
      inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv covH frame hframe x d e c =
        extU c + (∑ p : Idx, Γ p e * U p c) +
          (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simpa [DU] using hDU c
  have hDUactualFull : ∀ c : Idx,
      inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d e c =
        extU c + (∑ p : Idx, Γ p e * U p c) +
          (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simpa [covH] using hDUactual c
  have hswapA :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ a p * S p b c)) =
        (∑ p : Idx, ∑ c : Idx, Γ a p * (U e c * S p b c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapB :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ b p * S a p c)) =
        (∑ p : Idx, ∑ c : Idx, Γ b p * (U e c * S a p c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapC :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ c p * S a b p)) =
        (∑ c : Idx, ∑ p : Idx, Γ p c * (U e p * S a b c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapE :
      (∑ p : Idx, ∑ c : Idx, Γ p e * (U p c * S a b c)) =
        (∑ c : Idx, ∑ p : Idx, Γ p e * (U p c * S a b c)) := by
    rw [Finset.sum_comm]
  have hleft :
      2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
        2 * extD +
          (∑ p : Idx, Γ p e * (2 * D a b p)) -
          (∑ p : Idx, Γ a p * (2 * D p b e)) -
          (∑ p : Idx, Γ b p * (2 * D a p e)) := by
    simp [lcDiffCovDerivCompInFrame, extD, D, Γ, covH, Finset.mul_sum,
      mul_add, mul_sub]
    ring_nf
  rw [hleft]
  rw [hscalar]
  unfold lcDiffCovDerivRHS
  simp only [hDformula]
  simp only [hSderiv, hDUactualFull]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub,
    add_mul, Finset.mul_sum, Finset.sum_mul]
  rw [hswapA, hswapB, hswapC, hswapE]
  simp only [S, U, A2, Γ, covH]
  ring_nf

/-- Local form of `lcDiffCovDerivCompInFrame_eq`.

This is the reassembly step for the first covariant derivative of DC1 with
only local inverse-metric data. -/
theorem lcDiffCovDerivCompInFrame_eq_local
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvLeftX : forall i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
      lcDiffCovDerivRHS
        (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    lcDiffCompInFrame (I := I) g h frame hframe x i j k
  let S : Idx -> Idx -> Idx -> Real := fun i j k =>
    lcDiffSymMetricCovComp (I := I) g covH frame hframe x i j k
  let U : Idx -> Idx -> Real := fun i j => gInv x i j
  let DU : Idx -> Idx -> Real := fun i j =>
    inverseMetricCovDerivForMetricCompInFrame
      (I := I) gInv covH frame hframe x d i j
  let A2 : Idx -> Idx -> Idx -> Real := fun i j k =>
    metricCovDeriv2ForMetricCompInFrame (I := I) g covH frame hframe x d i j k
  let Γ : Idx -> Idx -> Real := fun i j =>
    christoffelSymbolInFrame covH frame hframe x d i j
  let extD : Real :=
    extDerivFun (I := I)
      (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e)
      x (frame d x)
  let extS : Idx -> Real := fun c =>
    extDerivFun (I := I)
      (fun y : M => lcDiffSymMetricCovComp (I := I) g covH frame hframe y a b c)
      x (frame d x)
  let extU : Idx -> Real := fun c =>
    extDerivFun (I := I) (fun y : M => gInv y e c) x (frame d x)
  have hDformula : ∀ i j k : Idx,
      2 * D i j k = ∑ c : Idx, U k c * S i j c := by
    intro i j k
    simpa [D, S, U, covH] using
      lcDiffCompInFrame_eq_local
        (I := I) g h gInv frame hframe hu hx hinvLeftX i j k
  have hscalar :
      2 * extD =
        ∑ c : Idx, (U e c * extS c + extU c * S a b c) := by
    simpa [extD, extS, extU, S, U, covH] using
      lcDiffCompInFrame_extDeriv_eq_local
        (I := I) g h gInv frame hframe hu hx hinvLeftN d a b e
        hD_mdiff hginv_mdiff hA_mdiff
  have hSderiv : ∀ c : Idx,
      extS c =
        A2 a b c + A2 b a c - A2 c a b +
          (∑ p : Idx, Γ a p * S p b c) +
          (∑ p : Idx, Γ b p * S a p c) +
          (∑ p : Idx, Γ c p * S a b p) := by
    intro c
    simpa [extS, A2, S, Γ, covH] using
      lcDiffSymMetricCovComp_extDeriv_eq
        (I := I) g covH frame hframe hA_mdiff d a b c
  have hDU : ∀ c : Idx,
      DU e c = extU c + (∑ p : Idx, Γ p e * U p c) +
        (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simp [DU, extU, U, Γ, inverseMetricCovDerivForMetricCompInFrame, covH]
  have hDUactual : ∀ c : Idx,
      inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv covH frame hframe x d e c =
        extU c + (∑ p : Idx, Γ p e * U p c) +
          (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simpa [DU] using hDU c
  have hDUactualFull : ∀ c : Idx,
      inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d e c =
        extU c + (∑ p : Idx, Γ p e * U p c) +
          (∑ p : Idx, Γ p c * U e p) := by
    intro c
    simpa [covH] using hDUactual c
  have hswapA :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ a p * S p b c)) =
        (∑ p : Idx, ∑ c : Idx, Γ a p * (U e c * S p b c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapB :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ b p * S a p c)) =
        (∑ p : Idx, ∑ c : Idx, Γ b p * (U e c * S a p c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapC :
      (∑ c : Idx, ∑ p : Idx, U e c * (Γ c p * S a b p)) =
        (∑ c : Idx, ∑ p : Idx, Γ p c * (U e p * S a b c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _hp => ?_
    refine Finset.sum_congr rfl fun c _hc => ?_
    ring
  have hswapE :
      (∑ p : Idx, ∑ c : Idx, Γ p e * (U p c * S a b c)) =
        (∑ c : Idx, ∑ p : Idx, Γ p e * (U p c * S a b c)) := by
    rw [Finset.sum_comm]
  have hleft :
      2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
        2 * extD +
          (∑ p : Idx, Γ p e * (2 * D a b p)) -
          (∑ p : Idx, Γ a p * (2 * D p b e)) -
          (∑ p : Idx, Γ b p * (2 * D a p e)) := by
    simp [lcDiffCovDerivCompInFrame, extD, D, Γ, covH, Finset.mul_sum,
      mul_add, mul_sub]
    ring_nf
  rw [hleft]
  rw [hscalar]
  unfold lcDiffCovDerivRHS
  simp only [hDformula]
  simp only [hSderiv, hDUactualFull]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub,
    add_mul, Finset.mul_sum, Finset.sum_mul]
  rw [hswapA, hswapB, hswapC, hswapE]
  simp only [S, U, A2, Γ, covH]
  ring_nf

/-- Substitute the inverse-metric derivative formula into the first-derivative
DC1 RHS. -/
theorem lcDiffRHS_eq_quad
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    {x : M}
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x)
    (d a b e : Idx) :
    lcDiffCovDerivRHS (I := I) g gInv cov frame hframe x d a b e =
      lcDiffQuadRHS (I := I) g gInv cov frame hframe x d a b e := by
  classical
  unfold lcDiffCovDerivRHS lcDiffQuadRHS
  congr 1
  refine Finset.sum_congr rfl fun c _hc => ?_
  have hderiv :=
    invMetricCovDeriv_eq
      (I := I) (g := g) (gInv := gInv) (cov := cov)
      (frame := frame) (hframe := hframe) (hinv := hinv)
      (x := x) hginv_mdiff hmetric_mdiff d e c
  rw [hderiv]

/-- Local form of `lcDiffRHS_eq_quad`, using only pointwise inverse identities
at `x` and the row inverse identity eventually near `x`. -/
theorem lcDiffRHS_eq_quad_local
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M}
    (hinvX : forall i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
          (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x)
    (d a b e : Idx) :
    lcDiffCovDerivRHS (I := I) g gInv cov frame hframe x d a b e =
      lcDiffQuadRHS (I := I) g gInv cov frame hframe x d a b e := by
  classical
  unfold lcDiffCovDerivRHS lcDiffQuadRHS
  congr 1
  refine Finset.sum_congr rfl fun c _hc => ?_
  have hderiv :=
    invMetricCovDeriv_eq_local
      (I := I) (g := g) (gInv := gInv) (cov := cov)
      (frame := frame) (hframe := hframe)
      (x := x) hinvX hinvLeftN hginv_mdiff hmetric_mdiff d e c
  rw [hderiv]

/-- First covariant derivative of DC1 after substituting the inverse-metric
derivative formula.  This is the coordinate-level producer whose terms are
only `nabla_h^2 g` and quadratic products of `nabla_h g`. -/
theorem lcDiffDeriv_eq_quad
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
      lcDiffQuadRHS
        (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  calc
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
        lcDiffCovDerivRHS
          (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d a b e := by
          exact
            lcDiffCovDerivCompInFrame_eq
              (I := I) g h gInv frame hframe hu hx hinv d a b e
              hD_mdiff hginv_mdiff hA_mdiff
    _ = lcDiffQuadRHS
          (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d a b e := by
          exact
            lcDiffRHS_eq_quad
              (I := I) g gInv
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe hinv hginv_mdiff hmetric_mdiff d a b e

/-- Local form of `lcDiffDeriv_eq_quad`.

This is the coordinate producer needed by local-frame HCG estimates: the
inverse-metric package is only required at and near the point where the
component is evaluated. -/
theorem lcDiffDeriv_eq_quad_local
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinvX : forall i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
          (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (d a b e : Idx)
    (hD_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => lcDiffCompInFrame (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : ∀ i j : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x)
    (hA_mdiff : ∀ i j k : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
      lcDiffQuadRHS
        (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  calc
    2 * lcDiffCovDerivCompInFrame (I := I) g h frame hframe x d a b e =
        lcDiffCovDerivRHS
          (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d a b e := by
          exact
            lcDiffCovDerivCompInFrame_eq_local
              (I := I) g h gInv frame hframe hu hx
              (fun i j => (hinvX i j).1) hinvLeftN d a b e
              hD_mdiff hginv_mdiff hA_mdiff
    _ = lcDiffQuadRHS
          (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x d a b e := by
          exact
            lcDiffRHS_eq_quad_local
              (I := I) g gInv
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe hinvX hinvLeftN hginv_mdiff hmetric_mdiff d a b e

end

end Coordinates
end RicciFlower
