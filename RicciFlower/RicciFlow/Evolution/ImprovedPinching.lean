import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.Scalar
import RicciFlower.RicciFlow.Evolution.ScalarGradient
import RicciFlower.Bochner
import RicciFlower.DimensionThree.RicciControlsRm
import RicciFlower.DimensionThree.PinchingAlgebra
import RicciFlower.Tensor.RSTensor.Metric
import RicciFlower.Tensor.RSTensor.MetricCompatibility

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved Ricci pinching quantities

This file contains the native RicciFlower definitions for Hamilton Section 10:
the trace-free Ricci tensor, the improved pinching quotient, and the cubic
reaction scalar.  The old `LocalPinching` file remains a compatibility/scaffold
layer for eigenvalue pinching statements.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A time-dependent `(0,2)` tensor family, represented pointwise. -/
abbrev Tensor02Fam : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

/-- The metric family, viewed as a `(0,2)` tensor family. -/
def metric02
    (G : Real -> SmoothRiemannianMetric I M) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x => Tensor0SBundle.metricTensorField (I := I) (G t) x

@[simp]
theorem metric02_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    metric02 (I := I) G t x v = (G t).inner x (v 0) (v 1) := by
  simp [metric02]

/-- Definition 10.1: the trace-free Ricci tensor `Ric° = Ric - (1/3) R g`. -/
def tfRic
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x =>
    Ric t x -
      (((1 : Real) / 3) * scalar t x) •
        metric02 (I := I) G t x

@[simp]
theorem tfRic_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    tfRic (I := I) G Ric scalar t x v =
      Ric t x v - (((1 : Real) / 3) * scalar t x) *
        (G t).inner x (v 0) (v 1) := by
  simp [tfRic, mul_assoc]

/-- Pointwise trace-free Ricci norm square from Definition 10.1:
`|Ric°|² = |Ric|² - R²/3`. -/
def tfRicNormSqAt (scalar ricciNormSq : Real) : Real :=
  ricciNormSq - scalar ^ 2 / 3

/-- Time-space trace-free Ricci norm square. -/
def tfRicNormSq
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) : Real :=
  tfRicNormSqAt (scalar t x) (ricciNormSq t x)

/-- Compatibility with the older scalar-gradient interface. -/
theorem tfRicNormSq_compat
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) :
    tfRicNormSq scalar ricciNormSq t x =
      tracefreeRicciNormSqOf scalar ricciNormSq t x := rfl

/-- Definition 10.2: Hamilton's improved pinching quotient
`P = |Ric°|² / R^(2 - epsilon)`. -/
def pinchP
    (scalar ricciNormSq : Real -> M -> Real) (epsilon : Real)
    (t : Real) (x : M) : Real :=
  tfRicNormSq scalar ricciNormSq t x / Real.rpow (scalar t x) (2 - epsilon)

/-- Pointwise form of Definition 10.3.  The first argument is scalar curvature,
the second is `|Ric|²`, and the third is `tr(Ric³)`. -/
def cubicQAt (scalar ricciNormSq ricciTraceCube : Real) : Real :=
  2 * ricciNormSq ^ 2 + scalar ^ 4 -
    5 * scalar ^ 2 * ricciNormSq + 4 * scalar * ricciTraceCube

/-- Definition 10.3 as a scalar field. -/
def cubicQ
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (t : Real) (x : M) : Real :=
  cubicQAt (scalar t x) (ricciNormSq t x) (ricciTraceCube t x)

/-- The component/eigenvalue version of `cubicQ` agrees with the existing
three-dimensional polynomial `hamiltonCubicQ3`. -/
theorem cubicQ_eigen (l1 l2 l3 : Real) :
    cubicQAt
        (DimensionThree.ricciEigenScalar3 l1 l2 l3)
        (DimensionThree.ricciEigenNormSq3 l1 l2 l3)
        (DimensionThree.ricciEigenTraceCube3 l1 l2 l3) =
      DimensionThree.hamiltonCubicQ3 l1 l2 l3 := by
  unfold cubicQAt DimensionThree.hamiltonCubicQ3
  ring

/-- The Ricci-norm curvature reaction in a three-dimensional orthonormal Ricci
eigenbasis.  This is the scalar `R_ikjl Ric^{ij} Ric^{kl}`. -/
def ricciReact3 (l1 l2 l3 : Real) : Real :=
  l1 * l2 * (l1 + l2 - l3) +
    l1 * l3 * (l1 + l3 - l2) +
      l2 * l3 * (l2 + l3 - l1)

/-- The diagonal three-dimensional curvature model contracts with diagonal
Ricci to the reaction scalar used in Lemma 10.4. -/
theorem react3_diag (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DimensionThree.stdRmDiag3 l1 l2 l3 i k j l *
        DimensionThree.ricciDiag3 l1 l2 l3 i j *
          DimensionThree.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DimensionThree.stdRmDiag3 DimensionThree.ricciDiag3
    DimensionThree.ricciEigenScalar3 DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- The same diagonal contraction in the `curvRicciRicciInFrame` slot order. -/
theorem curv3_diag_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DimensionThree.stdRmDiag3 l1 l2 l3 k j l i *
        DimensionThree.ricciDiag3 l1 l2 l3 i j *
          DimensionThree.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DimensionThree.stdRmDiag3 DimensionThree.ricciDiag3
    DimensionThree.ricciEigenScalar3 DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- The same contraction when the standard Riemann-from-Ricci data is supplied
with the project trace sign.  The actual geometric bridge uses
`stdRmDiag3 (-l1) (-l2) (-l3)` when the realized Ricci eigenvalues are
`l1,l2,l3`. -/
theorem curv3_neg_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) k j l i *
        DimensionThree.ricciDiag3 l1 l2 l3 i j *
          DimensionThree.ricciDiag3 l1 l2 l3 k l) =
      -ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DimensionThree.stdRmDiag3 DimensionThree.ricciDiag3
    DimensionThree.ricciEigenScalar3 DimensionThree.delta3
  simp [Fin.sum_univ_three]
  ring

/-- Field version of the diagonal reaction contraction in a Ricci eigenframe. -/
def diagReact3
    (l1 l2 l3 : Real -> M -> Real) : Real -> M -> Real :=
  fun t x =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DimensionThree.stdRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
        DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
          DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l

@[simp]
theorem diagReact3_apply
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        DimensionThree.stdRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
          DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
            DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l := by
  rfl

theorem diagReact3_eq
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ricciReact3 (l1 t x) (l2 t x) (l3 t x) := by
  exact react3_diag (l1 t x) (l2 t x) (l3 t x)

/-- The pointwise eigenvalue algebra behind Lemma 10.4's reaction term. -/
theorem tfRel_eigen (l1 l2 l3 : Real)
    (hR : DimensionThree.ricciEigenScalar3 l1 l2 l3 ≠ 0) :
    4 * ricciReact3 l1 l2 l3 -
        ((4 : Real) / 3) *
          DimensionThree.ricciEigenScalar3 l1 l2 l3 *
            DimensionThree.ricciEigenNormSq3 l1 l2 l3 =
      (4 * DimensionThree.ricciEigenNormSq3 l1 l2 l3 *
          tfRicNormSqAt
            (DimensionThree.ricciEigenScalar3 l1 l2 l3)
            (DimensionThree.ricciEigenNormSq3 l1 l2 l3) -
        2 * cubicQAt
          (DimensionThree.ricciEigenScalar3 l1 l2 l3)
          (DimensionThree.ricciEigenNormSq3 l1 l2 l3)
          (DimensionThree.ricciEigenTraceCube3 l1 l2 l3)) /
        DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
  unfold ricciReact3 tfRicNormSqAt cubicQAt DimensionThree.ricciEigenScalar3
    DimensionThree.ricciEigenNormSq3 DimensionThree.ricciEigenTraceCube3
  have hR' : l1 + l2 + l3 ≠ 0 := by
    simpa [DimensionThree.ricciEigenScalar3] using hR
  field_simp [hR']
  ring_nf

/-- Reaction relation needed to rewrite Lemma 10.4 into Hamilton's `Q` form. -/
def tfRicReactRel
    (scalar ricciNormSq tfNormSq Q reaction : Real -> M -> Real) : Prop :=
  ∀ t x, scalar t x ≠ 0 ->
    4 * reaction t x - ((4 : Real) / 3) * scalar t x * ricciNormSq t x =
      (4 * ricciNormSq t x * tfNormSq t x - 2 * Q t x) / scalar t x

/-- The field-level reaction relation produced from pointwise Ricci eigenvalue
data.  The remaining geometric bridge is to realize the eigenvalue inputs from
an actual Ricci eigenframe. -/
theorem tfRel_from_eigen
    (scalar ricciNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hreaction : ∀ t x,
      reaction t x = ricciReact3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) reaction := by
  intro t x hR
  have hR' :
      DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) ≠ 0 := by
    simpa [hscalar t x] using hR
  rw [hreaction t x, hscalar t x, hnorm t x]
  rw [tfRicNormSq, tfRicNormSqAt, cubicQ, hscalar t x, hnorm t x, hcube t x]
  exact tfRel_eigen (l1 t x) (l2 t x) (l3 t x) hR'

/-- Reaction relation produced when the reaction term is the diagonal
three-dimensional curvature contraction in a Ricci eigenframe. -/
theorem tfRel_from_diag
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) (diagReact3 l1 l2 l3) := by
  exact tfRel_from_eigen
    (M := M)
    scalar ricciNormSq ricciTraceCube (diagReact3 l1 l2 l3)
    l1 l2 l3 hscalar hnorm hcube
    (by intro t x; exact diagReact3_eq (M := M) l1 l2 l3 t x)

/-- The Section 6 curvature contraction in a diagonal three-dimensional
eigenframe, stated only in terms of the component data it needs. -/
theorem curvReact3_frame
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 l1 l2 l3 k j l i) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (Realized.vec2 (frame i x) (frame j x)) =
        DimensionThree.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DimensionThree.delta3,
        DimensionThree.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_diag_eq l1 l2 l3

/-- Formal plus-sign standard-component variant.  This is not the geometric
Riemann-from-Ricci bridge when `l1,l2,l3` are realized Ricci eigenvalues; for
that bridge use `canon3_frame_neg` below. -/
theorem canonReact3_frame
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 l1 l2 l3 k j l i) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curvReact3_frame (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]

/-- Section 6 curvature contraction in the actual 3D Riemann-from-Ricci sign
bridge: standard components are computed from `-Ric`, while the contracted
Ricci components are `Ric`. -/
theorem curv3_frame_neg
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) k j l i) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (Realized.vec2 (frame i x) (frame j x)) =
        DimensionThree.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DimensionThree.delta3,
        DimensionThree.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_neg_eq l1 l2 l3

/-- With the actual Section 6/project sign bridge, the canonical Ricci-norm
reaction matches the book/eigenvalue reaction scalar. -/
theorem canon3_frame_neg
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) k j l i) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curv3_frame_neg (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]
  ring

/-- The scalar Laplacian expected for the square of scalar curvature:
`Δ(R²) = 2 R ΔR + 2 |∇R|²`. -/
def scalarSqLap
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => 2 * scalar t x * scalarLap t x + 2 * gradScalarNormSq t x

/-- Spatial scalar-square Laplacian product rule at one time. -/
theorem sqLap_at
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      Realized.gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      Realized.gradientFun (I := I) (G.metric t) f y)) x) :
    Realized.laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * Realized.laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (Realized.gradientAt (I := I) G t f x)
          (Realized.gradientAt (I := I) G t f x) := by
  have hhalf :=
    Realized.half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold Realized.laplacianAt Realized.gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      Realized.laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * Realized.laplacian (I := I) (G.connection t) (G.metric t) f x +
          (G.metric t).inner x
            (Realized.gradientFun (I := I) (G.metric t) f x)
            (Realized.gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring

/-- The scalar-square Laplacian expression realizes the heat operator when the
scalar Laplacian and gradient-square inputs are the canonical ones. -/
theorem sqLap_realizes
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarLap : ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T scalar scalarLap)
    (hgradNorm : forall t x,
      gradScalarNormSq t x =
        (G.metric t).inner x
          (Realized.gradientAt (I := I) G t (scalar t) x)
          (Realized.gradientAt (I := I) G t (scalar t) x))
    (hdf : forall t y,
      MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hgrad : forall t x,
      MDiffAt (T% fun y : M =>
        Realized.gradientFun (I := I) (G.metric t) (scalar t) y) x)
    (hfg : forall t x,
      MDiffAt (T% ((scalar t) • fun y : M =>
        Realized.gradientFun (I := I) (G.metric t) (scalar t) y)) x) :
    ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T
      (fun t x => scalar t x ^ 2)
      (scalarSqLap scalar scalarLap gradScalarNormSq) := by
  intro t ht x
  have hlap :
      scalarLap t x = Realized.laplacianAt (I := I) G t (scalar t) x := by
    simpa [Realized.heatOperator] using hscalarLap t ht x
  have hsq :=
    sqLap_at (I := I) G t (f := scalar t) (x := x)
      (hdf t) (hdf t x) (hgrad t x) (hfg t x)
  calc
    scalarSqLap scalar scalarLap gradScalarNormSq t x =
        2 * scalar t x * Realized.laplacianAt (I := I) G t (scalar t) x +
          2 * (G.metric t).inner x
            (Realized.gradientAt (I := I) G t (scalar t) x)
            (Realized.gradientAt (I := I) G t (scalar t) x) := by
          simp [scalarSqLap, hlap, hgradNorm t x]
    _ = Realized.laplacianAt (I := I) G t
          (fun y : M => scalar t y ^ 2) x := by
          rw [hsq]
    _ = Realized.heatOperator (I := I) G t
          (fun y : M => scalar t y ^ 2) x := rfl

/-- The scalar Laplacian expected for `|Ric°|² = |Ric|² - R² / 3`. -/
def tfLap
    (scalar scalarLap gradScalarNormSq ricciNormLap : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => ricciNormLap t x -
    scalarSqLap scalar scalarLap gradScalarNormSq t x / 3

/-- Product-rule input for the heat operator applied to `R²`. -/
def scalarSqHeatOn
    {D : Realized.RealTimeInterval}
    (scalar scalarSqLap gradScalarNormSq ricciNormSq : Real -> M -> Real) :
    Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x ^ 2)
      (scalarSqLap (t : Real) x +
        (-2 * gradScalarNormSq (t : Real) x +
          4 * scalar (t : Real) x * ricciNormSq (t : Real) x))
      D.carrier
      (t : Real)

/-- The time-product-rule part of the `R²` heat equation, assuming the supplied
`scalarSqLap` is the usual Laplacian product-rule expression. -/
theorem sqHeat_of_scalar
    {D : Realized.RealTimeInterval}
    (scalar scalarLap gradScalarNormSq ricciNormSq : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq) :
    scalarSqHeatOn
      (D := D) scalar (scalarSqLap scalar scalarLap gradScalarNormSq)
      gradScalarNormSq ricciNormSq := by
  intro t x
  have h := hscalar t x
  have hmul := h.mul h
  convert hmul using 1
  · ext s
    simp [pow_two]
  · simp [scalarSqLap]
    ring

/-- Book-facing heat-equation form of Lemma 10.4. -/
def tfRicHeatOn
    {D : Realized.RealTimeInterval}
    (tfNormSq tfLap nablaRicNormSq gradScalarNormSq
      scalar ricciNormSq Q : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    scalar (t : Real) x ≠ 0 ->
    HasDerivWithinAt
      (fun s : Real => tfNormSq s x)
      (tfLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x * tfNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x))
      D.carrier
      (t : Real)

/-- Algebraic assembly of Lemma 10.4 from Lemma 6.7, the scalar-square product
rule, and the cubic reaction relation. -/
theorem tfRicHeat_alg
    {D : Realized.RealTimeInterval}
    (scalar ricciNormSq ricciNormLap scalarSqLap tfLap
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hSq : scalarSqHeatOn
      (D := D) scalar scalarSqLap gradScalarNormSq ricciNormSq)
    (hLap : ∀ t x,
      tfLap t x = ricciNormLap t x - scalarSqLap t x / 3)
    (hRel : tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq) Q reaction) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      tfLap nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  intro t x hR
  have hRic' := hRic t x
  have hSq' := hSq t x
  have hDeriv0 :
      HasDerivWithinAt
        (fun s : Real => ricciNormSq s x - ((1 : Real) / 3) * scalar s x ^ 2)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarSqLap (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    simpa [mul_assoc] using hRic'.sub (hSq'.const_mul ((1 : Real) / 3))
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real => tfRicNormSq scalar ricciNormSq s x)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarSqLap (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    simpa [tfRicNormSq, tfRicNormSqAt, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hDeriv0
  have hValue :
      ((ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
        ((1 : Real) / 3) *
          (scalarSqLap (t : Real) x +
            (-2 * gradScalarNormSq (t : Real) x +
              4 * scalar (t : Real) x * ricciNormSq (t : Real) x))) =
      tfLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x *
              tfRicNormSq scalar ricciNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x) := by
    rw [hLap (t : Real) x, ← hRel (t : Real) x hR]
    ring
  rw [hValue] at hDeriv
  exact hDeriv

/-- Lemma 10.4 assembly after the scalar-square product rule is expanded from
the scalar curvature evolution equation.  The remaining geometric input is the
reaction relation `tfRicReactRel`. -/
theorem tfHeat_base
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hRel : tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq) Q reaction) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  exact tfRicHeat_alg
    (D := D)
    scalar ricciNormSq ricciNormLap
    (scalarSqLap scalar scalarLap gradScalarNormSq)
    (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
    nablaRicNormSq gradScalarNormSq Q reaction
    hRic
    (sqHeat_of_scalar
      (D := D) scalar scalarLap gradScalarNormSq ricciNormSq hscalar)
    (by intro t x; rfl)
    hRel

/-- Eigenvalue-facing form of Lemma 10.4.  This consumes Section 6 scalar and
Ricci-norm heat equations plus pointwise Ricci eigenvalue data for the scalar,
norm, cubic trace, and reaction term. -/
theorem tfHeat_eigen
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hreaction : ∀ t x,
      reaction t x = ricciReact3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube) reaction
    hscalarHeat hRicHeat
    (tfRel_from_eigen
      scalar ricciNormSq ricciTraceCube reaction
      l1 l2 l3 hscalar hnorm hcube hreaction)

/-- Diagonal-eigenframe form of Lemma 10.4, using the standard 3D diagonal
curvature contraction for the reaction term. -/
theorem tfHeat_diag
    {D : Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq
        (diagReact3 l1 l2 l3))
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube)
    (diagReact3 l1 l2 l3)
    hscalarHeat hRicHeat
    (tfRel_from_diag
      (M := M)
      scalar ricciNormSq ricciTraceCube l1 l2 l3 hscalar hnorm hcube)

/-- Section 6 consumer for Lemma 10.4.  It uses the canonical Ricci-norm heat
equation route; the remaining geometric input is exactly the reaction relation
for the chosen three-dimensional convention. -/
theorem tfHeat_sec6
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (scalar scalarLap gradScalarNormSq Q : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : Realized.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hRel : tfRicReactRel
      scalar (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      Q (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame) Q := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap
    (ricciNormSqInFrame (I := I) S gInv frame)
    ricciNormLap
    (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
    gradScalarNormSq Q
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    hscalar
    (ricciNormHeatEquationOn_of_solution_canonical_laplacian
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
      h_inv h_ricci hInvSym hRicSym h_lap)
    hRel

end RicciFlow
end RicciFlower
