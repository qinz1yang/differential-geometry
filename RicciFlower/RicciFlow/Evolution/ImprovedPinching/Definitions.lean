import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.Scalar
import RicciFlower.RicciFlow.Evolution.RicciNorm
import RicciFlower.RicciFlow.Evolution.ScalarGradient
import RicciFlower.RicciFlow.Regularity
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
abbrev tfRicNormSqAt (scalar ricciNormSq : Real) : Real :=
  tracefreeRicciNormSqAtOf scalar ricciNormSq

/-- Time-space trace-free Ricci norm square.

This is a readability wrapper for the canonical scalar-gradient formula, not a
separate formula definition. -/
abbrev tfRicNormSq
    (scalar ricciNormSq : Real -> M -> Real) : Real -> M -> Real :=
  tracefreeRicciNormSqOf scalar ricciNormSq

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

/-- The trace-free Ricci norm used by the flow files matches the eigenvalue-gap
formula used in the dimension-three algebra layer. -/
theorem tfRic_eigen (l1 l2 l3 : Real) :
    tfRicNormSqAt
        (DimensionThree.ricciEigenScalar3 l1 l2 l3)
        (DimensionThree.ricciEigenNormSq3 l1 l2 l3) =
      DimensionThree.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  unfold tfRicNormSqAt tracefreeRicciNormSqAtOf
    DimensionThree.tracefreeRicciEigenNormSq3
    DimensionThree.ricciEigenPairwiseGapSq3
    DimensionThree.ricciEigenScalar3
    DimensionThree.ricciEigenNormSq3
  ring

/-- Fieldwise eigenvalue context for the later Hamilton pinching estimate.
This is deliberately only an eigenvalue algebra package; producing the
eigenvalue fields from a concrete Ricci-flow solution belongs to the
geometric/maximum-principle layer. -/
def EigenPinchCtxOn
    (l1 l2 l3 : Real -> M -> Real) (delta : Real) : Prop :=
  forall t x, DimensionThree.PinchEigen3 (l1 t x) (l2 t x) (l3 t x) delta

/-- Hamilton-ready cubic reaction bracket in the `cubicQAt` notation used by
Lemma 10.6. -/
theorem cubicQ_pinch
    {l1 l2 l3 delta epsilon : Real}
    (hctx : DimensionThree.PinchEigen3 l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    0 <=
      cubicQAt
          (DimensionThree.ricciEigenScalar3 l1 l2 l3)
          (DimensionThree.ricciEigenNormSq3 l1 l2 l3)
          (DimensionThree.ricciEigenTraceCube3 l1 l2 l3) -
        epsilon * DimensionThree.ricciEigenNormSq3 l1 l2 l3 *
          tfRicNormSqAt
            (DimensionThree.ricciEigenScalar3 l1 l2 l3)
            (DimensionThree.ricciEigenNormSq3 l1 l2 l3) := by
  simpa [cubicQ_eigen, tfRic_eigen] using
    DimensionThree.PinchEigen3.q_sub_nonneg hctx hepsilon

/-- Fieldwise version of `cubicQ_pinch`, ready to be consumed pointwise by the
post-10.6 pinching estimate setup. -/
theorem cubicQ_pinchOn
    (l1 l2 l3 : Real -> M -> Real) {delta epsilon : Real}
    (hctx : EigenPinchCtxOn (M := M) l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    forall t x,
      0 <=
        cubicQAt
            (DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
            (DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
            (DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) -
          epsilon * DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x) *
            tfRicNormSqAt
              (DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
              (DimensionThree.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x)) := by
  intro t x
  exact cubicQ_pinch (hctx t x) hepsilon

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
      DimensionThree.stdRmDiag3 l1 l2 l3 i k j l *
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
      DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l *
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
  unfold ricciReact3 tfRicNormSqAt tracefreeRicciNormSqAtOf cubicQAt
    DimensionThree.ricciEigenScalar3 DimensionThree.ricciEigenNormSq3
    DimensionThree.ricciEigenTraceCube3
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
  rw [tfRicNormSq, tracefreeRicciNormSqOf, cubicQ, hscalar t x, hnorm t x,
    hcube t x]
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
        DimensionThree.stdRmDiag3 l1 l2 l3 i k j l) :
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
        DimensionThree.stdRmDiag3 l1 l2 l3 i k j l) :
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
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
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
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curv3_frame_neg (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]
  ring

/-- Pointwise Ricci norm square in a `Fin 3` basis. -/
def ricciNormAt {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    Realized.ricciCompAt (I := I) basis Ric i j *
      Realized.ricciCompAt (I := I) basis Ric i j

/-- Pointwise curvature-Ricci-Ricci contraction in a `Fin 3` basis, before the
canonical Section 6 sign. -/
def curvRicAt {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    Realized.rm04CompAt (I := I) basis Rm04 i k j l *
      Realized.ricciCompAt (I := I) basis Ric i j *
        Realized.ricciCompAt (I := I) basis Ric k l

/-- Pointwise canonical Ricci-norm reaction scalar in a `Fin 3` basis. -/
def reactAt {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  -curvRicAt (I := I) Ric Rm04 basis

/-- Pointwise component trace `tr(Ric^3)` in a `Fin 3` basis. -/
def ricciCubeAt {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    Realized.ricciCompAt (I := I) basis Ric i j *
      Realized.ricciCompAt (I := I) basis Ric j k *
      Realized.ricciCompAt (I := I) basis Ric k i

theorem ricciCubeAt_diag {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeAt (I := I) Ric basis =
      DimensionThree.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  unfold ricciCubeAt DimensionThree.ricciEigenTraceCube3
  simp_rw [hdiag.2]
  unfold DimensionThree.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

theorem ricciEnd_diagVec {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    DimensionThree.ricciEndAt (I := I) g Ric (basis 0) = l1 • basis 0 /\
      DimensionThree.ricciEndAt (I := I) g Ric (basis 1) = l2 • basis 1 /\
      DimensionThree.ricciEndAt (I := I) g Ric (basis 2) = l3 • basis 2 := by
  classical
  let T := DimensionThree.ricciEndAt (I := I) g Ric
  have hdiagComp := hdiag.2
  have h0 : T (basis 0) = l1 • basis 0 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 0)) (basis j) =
          Ric (Curvature.vec2 (I := I) (basis 0) (basis j)) := by
            exact DimensionThree.ricciEnd_inner (I := I) g Ric (basis 0) (basis j)
      _ = DimensionThree.ricciDiag3 l1 l2 l3 0 j := by
            simpa [Realized.ricciCompAt_apply] using hdiagComp 0 j
      _ = g.inner x (l1 • basis 0) (basis j) := by
            fin_cases j <;> simp [DimensionThree.ricciDiag3,
              DimensionThree.delta3, horth 0 0, horth 0 1, horth 0 2]
  have h1 : T (basis 1) = l2 • basis 1 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 1)) (basis j) =
          Ric (Curvature.vec2 (I := I) (basis 1) (basis j)) := by
            exact DimensionThree.ricciEnd_inner (I := I) g Ric (basis 1) (basis j)
      _ = DimensionThree.ricciDiag3 l1 l2 l3 1 j := by
            simpa [Realized.ricciCompAt_apply] using hdiagComp 1 j
      _ = g.inner x (l2 • basis 1) (basis j) := by
            fin_cases j <;> simp [DimensionThree.ricciDiag3,
              DimensionThree.delta3, horth 1 0, horth 1 1, horth 1 2]
  have h2 : T (basis 2) = l3 • basis 2 := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 2)) (basis j) =
          Ric (Curvature.vec2 (I := I) (basis 2) (basis j)) := by
            exact DimensionThree.ricciEnd_inner (I := I) g Ric (basis 2) (basis j)
      _ = DimensionThree.ricciDiag3 l1 l2 l3 2 j := by
            simpa [Realized.ricciCompAt_apply] using hdiagComp 2 j
      _ = g.inner x (l3 • basis 2) (basis j) := by
            fin_cases j <;> simp [DimensionThree.ricciDiag3,
              DimensionThree.delta3, horth 2 0, horth 2 1, horth 2 2]
  exact ⟨h0, h1, h2⟩

/-- Intrinsic pointwise trace `tr(Ric^3)`, using the Ricci endomorphism obtained
by raising one index with the metric. -/
def ricciCubeInvAt {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x) : Real :=
  let T := DimensionThree.ricciEndAt (I := I) g Ric
  LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T))

theorem ricciCubeInv_diag {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeInvAt (I := I) g Ric =
      DimensionThree.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  let T := DimensionThree.ricciEndAt (I := I) g Ric
  rcases ricciEnd_diagVec (I := I) g horth hdiag with ⟨hT0, hT1, hT2⟩
  have hT0c : (T.comp (T.comp T)) (basis 0) = (l1 ^ 3) • basis 0 := by
    simp [T, LinearMap.comp_apply, hT0, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT1c : (T.comp (T.comp T)) (basis 1) = (l2 ^ 3) • basis 1 := by
    simp [T, LinearMap.comp_apply, hT1, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT2c : (T.comp (T.comp T)) (basis 2) = (l3 ^ 3) • basis 2 := by
    simp [T, LinearMap.comp_apply, hT2, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hinv :
      MetricInverseInBasis (I := I) g x basis DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  unfold ricciCubeInvAt
  change LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T)) =
    DimensionThree.ricciEigenTraceCube3 l1 l2 l3
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis
    DimensionThree.delta3 hinv]
  unfold DimensionThree.ricciEigenTraceCube3
  simp only [Fin.sum_univ_three, DimensionThree.delta3, LinearMap.coe_comp,
    Function.comp_apply]
  rw [show T (T (T (basis 0))) = (l1 ^ 3) • basis 0 by
        simpa [LinearMap.comp_apply] using hT0c,
      show T (T (T (basis 1))) = (l2 ^ 3) • basis 1 by
        simpa [LinearMap.comp_apply] using hT1c,
      show T (T (T (basis 2))) = (l3 ^ 3) • basis 2 by
        simpa [LinearMap.comp_apply] using hT2c]
  simp [DimensionThree.delta3, horth 0 0, horth 1 1, horth 2 2]

/-- Canonical spacetime scalar `tr((Ric^#)^3)` for a solution. -/
def ricciCube
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => ricciCubeInvAt (I := I) (S.base.metric t) (S.ricciAt t x)

@[simp]
theorem ricciPair04_apply {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (v : Fin 4 -> TangentSpace I x) :
    ricciPair04 (I := I) Ric v =
      Ric (fun a : Fin 2 => if a = 0 then v 0 else v 2) *
        Ric (fun a : Fin 2 => if a = 0 then v 1 else v 3) := by
  unfold ricciPair04
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hswap0 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 0 = 0 := by decide
  have hswap1 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 1 = 2 := by decide
  have hswap2 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 2 = 1 := by decide
  have hswap3 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 3 = 3 := by decide
  congr 2 <;> funext a <;> fin_cases a <;> simp [hswap0, hswap1, hswap2, hswap3]

private theorem prod_delta4
    (I0 J0 : Fin 4 -> Fin 3) :
    (∏ a : Fin 4, DimensionThree.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_four]
  by_cases h : I0 = J0
  · subst J0
    simp [DimensionThree.delta3]
  · have hne :
        I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 ∨ I0 2 ≠ J0 2 ∨ I0 3 ≠ J0 3 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1 | h2 | h3
    · simp [DimensionThree.delta3, h, h0]
    · simp [DimensionThree.delta3, h, h1]
    · simp [DimensionThree.delta3, h, h2]
    · simp [DimensionThree.delta3, h, h3]

private theorem sum_delta4
    (F G : (Fin 4 -> Fin 3) -> Real) :
    (∑ I0 : Fin 4 -> Fin 3, ∑ J0 : Fin 4 -> Fin 3,
        (∏ a : Fin 4, DimensionThree.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
      ∑ I0 : Fin 4 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  simp [prod_delta4]

private def fin4ikjl :
    (Fin 4 -> Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 2), f 1), f 3)
  invFun p := Realized.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [Realized.slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [Realized.slots4]

private theorem sum4ikjl {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 -> Fin 3) -> α) :
    (∑ I0 : Fin 4 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (Realized.slots4 i k j l) := by
  classical
  rw [Fintype.sum_equiv fin4ikjl F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (Realized.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        Realized.slots4 (fin4ikjl I0).1.1.1 (fin4ikjl I0).1.2
            (fin4ikjl I0).1.1.2 (fin4ikjl I0).2 = I0 := by
      change fin4ikjl.symm (fin4ikjl I0) = I0
      exact fin4ikjl.left_inv I0
    rw [hslot]

private theorem coordPair04 {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 4 DimensionThree.delta3
        Rm04 (ricciPair04 (I := I) Ric) basis =
      curvRicAt (I := I) Ric Rm04 basis := by
  classical
  unfold coordInner0S curvRicAt
  rw [sum_delta4]
  rw [sum4ikjl]
  simp [tensor0SComponent, Realized.rm04CompAt, Realized.ricciCompAt,
    Realized.slots4, Realized.slots2, ricciPair04_apply, mul_assoc]

theorem curvRic_inner {x : M}
    (g : SmoothMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3) :
    curvRicAt (I := I) Ric Rm04 basis =
      inner0S (I := I) g x 4 Rm04 (ricciPair04 (I := I) Ric) := by
  rw [inner0S_eq_coord (I := I) g x 4 basis DimensionThree.delta3 hinv]
  exact (coordPair04 (I := I) Ric Rm04 basis).symm

/-- The basis reaction agrees with the intrinsic reaction in any orthonormal
`Fin 3` basis. -/
theorem reactAt_eq_react
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    reactAt (I := I) (S.ricciAt t x) (S.base.rm04 t x) basis =
      ricciReact (I := I) S t x := by
  have hinv :
      MetricInverseInBasis (I := I) (S.base.metric t) x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) (S.base.metric t) basis horth
  unfold reactAt ricciReact
  rw [curvRic_inner (I := I) (S.base.metric t) (S.ricciAt t x)
    (S.base.rm04 t x) basis hinv]

/-- The zero-order Ricci reaction scalar is independent of the orthonormal
`Fin 3` basis used to compute it. -/
theorem react_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DimensionThree.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DimensionThree.OrthonormalBasisAt (I := I) g x basis₂) :
    reactAt (I := I) Ric Rm04 basis₁ =
      reactAt (I := I) Ric Rm04 basis₂ := by
  have hinv₁ : MetricInverseInBasis (I := I) g x basis₁ DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis (I := I) g x basis₂ DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis₂ h₂
  unfold reactAt
  rw [curvRic_inner (I := I) g Ric Rm04 basis₁ hinv₁,
    curvRic_inner (I := I) g Ric Rm04 basis₂ hinv₂]

private theorem prod_delta2
    (I0 J0 : Fin 2 -> Fin 3) :
    (∏ a : Fin 2, DimensionThree.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_two]
  by_cases h : I0 = J0
  · subst J0
    simp [DimensionThree.delta3]
  · have hne : I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1
    · simp [DimensionThree.delta3, h, h0]
    · simp [DimensionThree.delta3, h, h1]

private theorem sum_delta2
    (F G : (Fin 2 -> Fin 3) -> Real) :
    (∑ I0 : Fin 2 -> Fin 3, ∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DimensionThree.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
      ∑ I0 : Fin 2 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  calc
    (∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DimensionThree.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
        ∑ J0 : Fin 2 -> Fin 3, (if I0 = J0 then 1 else 0) * F I0 * G J0 := by
          apply Finset.sum_congr rfl
          intro J0 _
          rw [prod_delta2]
    _ = F I0 * G I0 := by
          simp

private def fin2ij :
    (Fin 2 -> Fin 3) ≃ (Fin 3 × Fin 3) where
  toFun f := (f 0, f 1)
  invFun p := Realized.slots2 p.1 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [Realized.slots2]
  right_inv p := by
    rcases p with ⟨i, j⟩
    simp [Realized.slots2]

private theorem sum2ij {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Fin 3) -> α) :
    (∑ I0 : Fin 2 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, F (Realized.slots2 i j) := by
  classical
  rw [Fintype.sum_equiv fin2ij F
    (fun p : Fin 3 × Fin 3 => F (Realized.slots2 p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        Realized.slots2 (fin2ij I0).1 (fin2ij I0).2 = I0 := by
      change fin2ij.symm (fin2ij I0) = I0
      exact fin2ij.left_inv I0
    rw [hslot]

private theorem coordRic02 {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 2 DimensionThree.delta3 Ric Ric basis =
      ricciNormAt (I := I) Ric basis := by
  classical
  unfold coordInner0S ricciNormAt
  rw [sum_delta2]
  rw [sum2ij]
  simp [tensor0SComponent, Realized.ricciCompAt, Realized.slots2]

theorem ricciNorm_inner {x : M}
    (g : SmoothMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis DimensionThree.delta3) :
    ricciNormAt (I := I) Ric basis =
      normSq0S (I := I) g x 2 Ric := by
  rw [normSq0S_eq_coord (I := I) g x 2 basis DimensionThree.delta3 hinv Ric]
  exact (coordRic02 (I := I) Ric basis).symm

theorem ricciNorm_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DimensionThree.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DimensionThree.OrthonormalBasisAt (I := I) g x basis₂) :
    ricciNormAt (I := I) Ric basis₁ =
      ricciNormAt (I := I) Ric basis₂ := by
  have hinv₁ : MetricInverseInBasis (I := I) g x basis₁ DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis (I := I) g x basis₂ DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis₂ h₂
  rw [ricciNorm_inner (I := I) g Ric basis₁ hinv₁,
    ricciNorm_inner (I := I) g Ric basis₂ hinv₂]

theorem ricciNormAt_diag {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    ricciNormAt (I := I) Ric basis =
      DimensionThree.ricciEigenNormSq3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold ricciNormAt DimensionThree.ricciEigenNormSq3
  simp_rw [hric]
  unfold DimensionThree.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

theorem reactAt_diag {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {Rm04 : Realized.Tensor04At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04CompAt (I := I) basis Rm04 i k j l =
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    reactAt (I := I) Ric Rm04 basis = ricciReact3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold reactAt curvRicAt
  simp_rw [hRm]
  simp_rw [hric]
  rw [curv3_neg_eq]
  ring

/-- Pointwise reaction relation from a convention-correct diagonal Ricci
eigenbasis.  This is the honest local producer behind the frame-level
`tfRel_frame` theorem. -/
theorem tfRel_basis {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {Rm04 : Realized.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hcube :
      ricciTraceCube = DimensionThree.ricciEigenTraceCube3 l1 l2 l3)
    (hRm : ∀ i j k l : Fin 3,
      Realized.rm04CompAt (I := I) basis Rm04 i k j l =
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hscalar :
      scalar = DimensionThree.ricciEigenScalar3 l1 l2 l3 := hdiag.1
  have hR' :
      DimensionThree.ricciEigenScalar3 l1 l2 l3 ≠ 0 := by
    simpa [hscalar] using hR
  rw [reactAt_diag (I := I) hdiag hRm, ricciNormAt_diag (I := I) hdiag,
    hscalar, hcube]
  exact tfRel_eigen l1 l2 l3 hR'

/-- Negating a diagonal Ricci tensor negates the displayed eigenvalues and
trace. -/
theorem diag_neg {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 : Real}
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    DimensionThree.RicciDiagAt (I := I) (-Ric) (-scalar)
      (-l1) (-l2) (-l3) basis := by
  rcases hdiag with ⟨hscalar, hric⟩
  constructor
  · unfold DimensionThree.ricciEigenScalar3 at hscalar ⊢
    linarith
  · intro i j
    have hij := hric i j
    fin_cases i <;> fin_cases j <;>
      simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using
        congrArg Neg.neg hij

/-- Reaction relation from the convention-correct 3D Riemann-from-Ricci trace
data and a diagonal Ricci eigenbasis. -/
theorem tfRel_trace {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {Rm04 : Realized.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (htrace :
      DimensionThree.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 basis)
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hcube :
      ricciTraceCube = DimensionThree.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hneg := diag_neg (I := I) hdiag
  have hcomp :=
    DimensionThree.stdRmComp_eq_diag (I := I) htrace hneg
  have hRm : ∀ i j k l : Fin 3,
      Realized.rm04CompAt (I := I) basis Rm04 i k j l =
        DimensionThree.stdRmDiag3 (-l1) (-l2) (-l3) i k j l := by
    intro i j k l
    have h := hcomp i k j l
    simpa [DimensionThree.standardRmCompAt_apply] using h
  exact tfRel_basis (I := I) (Ric := Ric) (Rm04 := Rm04)
    (basis := basis) hdiag hcube hRm hR

/-- Pointwise trace-free Ricci reaction relation in an arbitrary orthonormal
heat frame.  The diagonalization happens only in the separate eigenbasis used
inside the proof. -/
theorem tfRel_point {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {Rm04 : Realized.Tensor04At (I := I) (M := M) x}
    {heatBasis eigBasis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hheat : DimensionThree.OrthonormalBasisAt (I := I) g x heatBasis)
    (heig : DimensionThree.OrthonormalBasisAt (I := I) g x eigBasis)
    (htrace :
      DimensionThree.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 eigBasis)
    (hdiag : DimensionThree.RicciDiagAt (I := I) Ric scalar l1 l2 l3 eigBasis)
    (hcube :
      ricciTraceCube = DimensionThree.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 heatBasis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric heatBasis =
      (4 * ricciNormAt (I := I) Ric heatBasis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric heatBasis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric heatBasis)
          ricciTraceCube) / scalar := by
  have hrel :=
    tfRel_trace (I := I) (g := g) (Ric := Ric) (Rm04 := Rm04)
      (basis := eigBasis) htrace hdiag hcube hR
  have hreact :
      reactAt (I := I) Ric Rm04 heatBasis =
        reactAt (I := I) Ric Rm04 eigBasis :=
    react_frame (I := I) g Ric Rm04 heatBasis eigBasis hheat heig
  have hnorm :
      ricciNormAt (I := I) Ric heatBasis =
        ricciNormAt (I := I) Ric eigBasis :=
    ricciNorm_frame (I := I) g Ric heatBasis eigBasis hheat heig
  simpa [hreact, hnorm] using hrel

private theorem raiseRicci_delta
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hInv : ∀ i j : Idx, gInv t x i j = if i = j then 1 else 0)
    (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j := by
  classical
  unfold raisedRicciCompInFrame
  simp [hInv]

theorem sec6_norm_at
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DimensionThree.delta3 i j) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ricciNormAt (I := I) (S.ricciAt t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        Realized.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    simp [ricciCompInFrame, Realized.ricciCompAt_apply, hbasis i, hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DimensionThree.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        Realized.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  rw [ricciNormSqInFrame_apply]
  unfold ricciNormAt
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hRicAt i j, hraised i j]

theorem sec6_react_at
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DimensionThree.delta3 i j) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      reactAt (I := I) (S.ricciAt t x) (Rm04 t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        Realized.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    simp [ricciCompInFrame, Realized.ricciCompAt_apply, hbasis i, hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DimensionThree.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        Realized.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  have hRmAt : ∀ i j k l : Fin 3,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        Realized.rm04CompAt (I := I) basis (Rm04 t x) i k j l := by
    intro i j k l
    simp [Realized.rm04Comp, RicciFlower.Curvature.rm04Comp,
      Realized.rm04CompAt_apply, Realized.vec4,
      hbasis i, hbasis k, hbasis j, hbasis l]
  unfold ricciNormCurvatureReactionInFrame reactAt
  congr 1
  unfold curvRicciRicciInFrame curvRicAt
  simp_rw [hraised, hRmAt]

theorem tfRel_point_sec6
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (htrace : ∀ (t : Real) (x : M),
      DimensionThree.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  intro t x hR
  have hnorm := sec6_norm_at (I := I) S gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hreact := sec6_react_at (I := I) S Rm04 gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hpoint := tfRel_point (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := Rm04 t x)
    (heatBasis := heatBasis t x) (eigBasis := eigBasis t x)
    (scalar := scalar t x) (l1 := l1 t x) (l2 := l2 t x) (l3 := l3 t x)
    (ricciTraceCube := ricciTraceCube t x)
    (hheat t x) (heig t x) (htrace t x) (hdiag t x) (hcube t x) hR
  rw [hreact, hnorm]
  unfold tfRicNormSq tracefreeRicciNormSqOf cubicQ
  rw [hnorm]
  exact hpoint

/-- Pointwise relation in an arbitrary heat frame, with the signed trace-data
package produced from first-trace Ricci and scalar realizations at the separate
Ricci eigenbasis. -/
theorem tfRel_pfirst
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DimensionThree.AlgebraicCurvatureSymmetries3
        (DimensionThree.standardRmCompAt (I := I) (eigBasis t x) (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (Rm04 t x) DimensionThree.delta3 (eigBasis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      Realized.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
        (S.ricciAt t x) DimensionThree.delta3 (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DimensionThree.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine tfRel_point_sec6 (I := I) S Rm04 gInv frame heatBasis eigBasis
    scalar ricciTraceCube l1 l2 l3 hheatBasis hheat heig ?_ hdiag hcube hInv
  intro t x
  exact DimensionThree.traceDataOfFirst (I := I) (M := M) (heig t x)
    (hcurv t x) (hRicFirst t x) (hScalarTrace t x)

theorem scalar_eq_diag {x : M}
    {Ric : Realized.Tensor02At (I := I) (M := M) x}
    {scalar scalar0 l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hScalar : Realized.ScalarRealizesRicciTraceAt
      (I := I) scalar Ric DimensionThree.delta3 basis)
    (hdiag : DimensionThree.RicciDiagAt
      (I := I) Ric scalar0 l1 l2 l3 basis) :
    scalar = scalar0 := by
  classical
  rcases hdiag with ⟨hscalar0, hric⟩
  have h00 :
      Ric (Realized.vec2 (basis 0) (basis 0)) = l1 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using hric 0 0
  have h11 :
      Ric (Realized.vec2 (basis 1) (basis 1)) = l2 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using hric 1 1
  have h22 :
      Ric (Realized.vec2 (basis 2) (basis 2)) = l3 := by
    simpa [Realized.ricciCompAt_apply, DimensionThree.ricciDiag3] using hric 2 2
  rw [hScalar, hscalar0]
  rw [Fin.sum_univ_three]
  simp [DimensionThree.delta3, h00, h11, h22,
    DimensionThree.ricciEigenScalar3]

/-- In an orthonormal `Fin 3` basis, the intrinsic metric trace realizes the
scalar trace with `delta3` inverse metric components. -/
theorem scalarTrace_delta {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis) :
    Realized.ScalarRealizesRicciTraceAt (I := I)
      (Realized.metricTracePair0SAt (I := I) g Ric)
      Ric DimensionThree.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  unfold Realized.ScalarRealizesRicciTraceAt
  rw [Realized.metricTracePair0SAt_eq_sum_basis
    (I := I) g basis DimensionThree.delta3 hinv Ric]

/-- In an orthonormal `Fin 3` basis, intrinsic `Rm13` trace plus metric
lowering realizes the convention-correct first trace of `Rm04`. -/
theorem firstTrace_delta
    [SigmaCompactSpace M] [T2Space M]
    {x : M} (g : SmoothRiemannianMetric I M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DimensionThree.OrthonormalBasisAt (I := I) g x basis)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm13 : Realized.Tensor13At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (hRic : Ric = Realized.ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Realized.Rm04LowersRm13At (I := I) g x Rm13 Rm04) :
    Realized.RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04
      DimensionThree.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) g basis horth
  have hInvSym :
      ∀ i j : Fin 3,
        DimensionThree.delta3 i j = DimensionThree.delta3 j i := by
    intro i j
    unfold DimensionThree.delta3
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  exact Realized.ricciFirstTraceAt_of_rm13 (I := I) g basis
    DimensionThree.delta3 hinv Ric Rm13 Rm04 hRic hLower hInvSym

theorem delta3_symm (i j : Fin 3) :
    DimensionThree.delta3 i j = DimensionThree.delta3 j i := by
  unfold DimensionThree.delta3
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

private theorem sum_fin_two_fun_local {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

private theorem vec2_update_zero {x : M}
    (X Y X' : TangentSpace I x) :
    Function.update (RicciFlower.Curvature.vec2 (I := I) X Y)
        (0 : Fin 2) X' =
      RicciFlower.Curvature.vec2 (I := I) X' Y := by
  funext a
  fin_cases a <;> simp [RicciFlower.Curvature.vec2, Function.update]

private theorem vec2_update_one {x : M}
    (X Y Y' : TangentSpace I x) :
    Function.update (RicciFlower.Curvature.vec2 (I := I) X Y)
        (1 : Fin 2) Y' =
      RicciFlower.Curvature.vec2 (I := I) X Y' := by
  funext a
  fin_cases a <;> simp [RicciFlower.Curvature.vec2, Function.update]

/-- A `(0,2)` tensor symmetric on a basis is symmetric on all tangent
vectors. -/
theorem ricciSym_of_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Realized.Tensor02At (I := I) (M := M) x)
    (hsym : ∀ i j : Idx,
      A (Realized.vec2 (I := I) (basis i) (basis j)) =
        A (Realized.vec2 (I := I) (basis j) (basis i))) :
    DimensionThree.RicciSymAt (I := I) A := by
  classical
  intro X Y
  let cx : Idx -> Real := fun i => basis.repr X i
  let cy : Idx -> Real := fun i => basis.repr Y i
  have hX : X = ∑ i : Idx, cx i • basis i := by
    simp [cx]
  have hY : Y = ∑ i : Idx, cy i • basis i := by
    simp [cy]
  have hXY :
      A (Realized.vec2 (I := I) X Y) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cx j else cy j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cx j else cy j) • basis j))
    simpa [Realized.vec2] using hsum
  have hYX :
      A (Realized.vec2 (I := I) Y X) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cy j else cx j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cy j else cx j) • basis j))
    simpa [Realized.vec2] using hsum
  rw [hXY, hYX]
  rw [sum_fin_two_fun_local, sum_fin_two_fun_local]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hleft :
      (fun a : Fin 2 =>
        (if a = 0
          then cx ((fun a : Fin 2 => if a = 0 then j else i) a)
          else cy ((fun a : Fin 2 => if a = 0 then j else i) a)) •
            basis ((fun a : Fin 2 => if a = 0 then j else i) a)) =
        Realized.vec2 (I := I) (cx j • basis j) (cy i • basis i) := by
    funext a
    fin_cases a <;> simp [Realized.vec2, RicciFlower.Curvature.vec2]
  have hright :
      (fun a : Fin 2 =>
        (if a = 0
          then cy ((fun a : Fin 2 => if a = 0 then i else j) a)
          else cx ((fun a : Fin 2 => if a = 0 then i else j) a)) •
            basis ((fun a : Fin 2 => if a = 0 then i else j) a)) =
        Realized.vec2 (I := I) (cy i • basis i) (cx j • basis j) := by
    funext a
    fin_cases a <;> simp [Realized.vec2, RicciFlower.Curvature.vec2]
  rw [hleft, hright]
  have hL :
      A (Realized.vec2 (I := I) (cx j • basis j) (cy i • basis i)) =
        (cx j) * (cy i) *
          A (Realized.vec2 (I := I) (basis j) (basis i)) := by
    have h0 := A.map_update_smul
      (Realized.vec2 (I := I) (basis j) (cy i • basis i))
      (0 : Fin 2) (cx j) (basis j)
    have h1 := A.map_update_smul
      (Realized.vec2 (I := I) (basis j) (basis i))
      (1 : Fin 2) (cy i) (basis i)
    calc
      A (Realized.vec2 (I := I) (cx j • basis j) (cy i • basis i))
          = (cx j) *
              A (Realized.vec2 (I := I) (basis j) (cy i • basis i)) := by
              simpa only [Realized.vec2, RicciFlower.Curvature.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cx j) * ((cy i) *
              A (Realized.vec2 (I := I) (basis j) (basis i))) := by
              congr 1
              simpa only [Realized.vec2, RicciFlower.Curvature.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cx j) * (cy i) *
              A (Realized.vec2 (I := I) (basis j) (basis i)) := by ring
  have hR :
      A (Realized.vec2 (I := I) (cy i • basis i) (cx j • basis j)) =
        (cy i) * (cx j) *
          A (Realized.vec2 (I := I) (basis i) (basis j)) := by
    have h0 := A.map_update_smul
      (Realized.vec2 (I := I) (basis i) (cx j • basis j))
      (0 : Fin 2) (cy i) (basis i)
    have h1 := A.map_update_smul
      (Realized.vec2 (I := I) (basis i) (basis j))
      (1 : Fin 2) (cx j) (basis j)
    calc
      A (Realized.vec2 (I := I) (cy i • basis i) (cx j • basis j))
          = (cy i) *
              A (Realized.vec2 (I := I) (basis i) (cx j • basis j)) := by
              simpa only [Realized.vec2, RicciFlower.Curvature.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cy i) * ((cx j) *
              A (Realized.vec2 (I := I) (basis i) (basis j))) := by
              congr 1
              simpa only [Realized.vec2, RicciFlower.Curvature.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cy i) * (cx j) *
              A (Realized.vec2 (I := I) (basis i) (basis j)) := by ring
  rw [hL, hR, hsym j i]
  ring

/-- Ricci symmetry from a first-trace realization and the algebraic symmetries
of the lowered curvature tensor. -/
theorem ricciSym_rm04
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (Rm04 : Realized.Tensor04At (I := I) (M := M) x)
    (hTrace : Realized.RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04
      gInv basis)
    (hPair : ∀ W X Y Z : TangentSpace I x,
      Rm04 (Realized.vec4 (I := I) W X Y Z) =
        Rm04 (Realized.vec4 (I := I) Y Z W X))
    (hOutput : Realized.Rm04OutputSkewAt (I := I) Rm04)
    (hInput : ∀ X Y Z W : TangentSpace I x,
      Rm04 (Realized.vec4 (I := I) Y X Z W) =
        -Rm04 (Realized.vec4 (I := I) X Y Z W))
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    DimensionThree.RicciSymAt (I := I) Ric := by
  exact ricciSym_of_basis (I := I) basis Ric
    (fun i j =>
      Realized.ricciSymm_of_rm04 (I := I) basis gInv Ric Rm04 hTrace
        hPair hOutput hInput hInv i j)

/-- Reaction relation from a convention-correct diagonal Ricci eigenframe.

This is the Section 10 bridge from the canonical Section 6 reaction term to
the eigenvalue algebra `tfRel_eigen`. -/
theorem tfRel_frame
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j)
    (hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  refine tfRel_from_eigen
    (M := M)
    scalar (ricciNormSqInFrame (I := I) S gInv frame) ricciTraceCube
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    l1 l2 l3 hscalar ?_ hcube ?_
  · intro t x
    have hRicAt : ∀ i j : Fin 3,
        S.base.ricciAt t x (Realized.vec2 (frame i x) (frame j x)) =
          DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      simpa [ricciCompInFrame] using hRic t x i j
    have hraised : ∀ i j : Fin 3,
        raisedRicciCompInFrame (I := I) S gInv frame t x i j =
          DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      unfold raisedRicciCompInFrame
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_three, hInv t x, hRicAt, DimensionThree.delta3,
          DimensionThree.ricciDiag3]
    rw [ricciNormSqInFrame_apply]
    simp only [hraised]
    unfold DimensionThree.ricciEigenNormSq3 DimensionThree.ricciDiag3
    simp only [Fin.sum_univ_three]
    rw [hRic t x 0 0, hRic t x 1 1, hRic t x 2 2]
    simp [DimensionThree.ricciDiag3]
    ring
  · intro t x
    exact canon3_frame_neg (I := I) S Rm04 gInv frame t x
      (l1 t x) (l2 t x) (l3 t x)
      (hInv t x) (hRic t x) (hRm t x)

/-- Reaction relation from signed 3D trace data in a diagonal frame.

This removes the raw `Rm04` component hypothesis from `tfRel_frame`; callers
only need the convention-correct `RiemannFromRicci3DTraceDataAt` package and a
pointwise basis matching the frame. -/
theorem tfRel_data
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (htrace : ∀ (t : Real) (x : M),
      DimensionThree.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  have hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DimensionThree.stdRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l := by
    intro t x i j k l
    have hdiag : DimensionThree.RicciDiagAt (I := I)
        (S.ricciAt t x) (scalar t x)
        (l1 t x) (l2 t x) (l3 t x) (basis t x) := by
      constructor
      · exact hscalar t x
      · intro a b
        have h := hRic t x a b
        simpa [ricciCompInFrame, Realized.ricciCompAt_apply,
          hbasis t x a, hbasis t x b] using h
    have hneg := diag_neg (I := I) hdiag
    have hcomp :=
      DimensionThree.stdRmComp_eq_diag (I := I) (htrace t x) hneg
    have h := hcomp i k j l
    simpa [DimensionThree.standardRmCompAt_apply, Realized.rm04Comp,
      RicciFlower.Curvature.rm04Comp, Realized.rm04CompAt_apply,
      hbasis t x i, hbasis t x k, hbasis t x j, hbasis t x l] using h
  exact tfRel_frame (I := I) S Rm04 gInv frame scalar ricciTraceCube
    l1 l2 l3 hscalar hcube hInv hRic hRm

/-- Reaction relation from convention-correct first-trace data in a diagonal
frame. -/
theorem tfRel_first
    {D : Realized.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (horth : ∀ (t : Real) (x : M),
      DimensionThree.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (basis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DimensionThree.AlgebraicCurvatureSymmetries3
        (DimensionThree.standardRmCompAt (I := I) (basis t x) (Rm04 t x)))
    (hRicTrace : ∀ (t : Real) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt
        (I := I) (S.ricciAt t x) (Rm04 t x) DimensionThree.delta3
        (basis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      Realized.ScalarRealizesRicciTraceAt
        (I := I) (scalar t x) (S.ricciAt t x) DimensionThree.delta3
        (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DimensionThree.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DimensionThree.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DimensionThree.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DimensionThree.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine tfRel_data (I := I) S Rm04 gInv frame basis scalar
    ricciTraceCube l1 l2 l3 hbasis ?_ hscalar hcube hInv hRic
  intro t x
  exact DimensionThree.traceDataOfFirst
    (I := I) (horth t x) (hcurv t x) (hRicTrace t x) (hScalarTrace t x)

end RicciFlow
end RicciFlower
