/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.Curvature.Contractions
import RicciFlower.Operators.HessianTrace
import RicciFlower.Realized.Operators
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.Metric
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Curvature Evolution

This file records the scalar-curvature simplification in MSM110 Chapter 6,
Section 1.  The full geometric inputs are kept explicit: one hypothesis is the
pre-Bianchi Ricci-flow scalar evolution, and the second is the contracted
Bianchi reduction that turns it into the heat-type scalar equation.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- MSM110 Chapter 6, Section 1, equation
`eq:scalar_curvature_ricci_flow_one`.

This is the scalar-curvature evolution immediately after substituting
`∂t g = -2 Ric`, before applying the contracted Bianchi identity:
`∂t R = 2 ΔR - 2 Q + 2 |Ric|²`, where `Q` denotes the contracted second
derivative term `g^{jk} g^{pq} ∇_q ∇_j R_{kp}`. -/
def ScalarPreBianchiEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x +
        2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-- The contracted-Bianchi simplification used in MSM110 Chapter 6, Section 1:
`2 ΔR - 2 Q = ΔR`. -/
def ScalarContractedBianchiReductionOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x =
      scalarLap (t : Real) x

/-- Contracted second-Bianchi identity in the scalar-curvature calculation:
the twice-contracted Ricci Hessian term is half the scalar Laplacian. -/
def ScalarSecondDerivativeContractedBianchiOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    contractedRicciHessian (t : Real) x =
      (1 / 2 : Real) * scalarLap (t : Real) x

/-- The scalar contracted-Bianchi identity supplies the algebraic reduction
`2 ΔR - 2 Q = ΔR` used in MSM110 Chapter 6.1. -/
theorem scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian := by
  intro t x
  rw [hbianchi t x]
  ring

/-- MSM110 Chapter 6, Section 1, equation `eq:scalar_curv_evolu`.

The scalar curvature heat equation follows from the pre-Bianchi scalar
evolution and the contracted-Bianchi reduction. -/
theorem scalarEvolutionEquationOn_of_contractedBianchi
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq := by
  intro t x
  exact (hpre t x).congr_deriv (by
    rw [hbianchi t x])

/-- Book-facing name for MSM110 Chapter 6, Section 1,
`eq:scalar_curv_evolu`. -/
theorem msm110_ch6_1_scalar_curvature_evolution
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  scalarEvolutionEquationOn_of_contractedBianchi
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi

/-! ## Heat-operator realization interface -/

/-- The scalar Laplacian realization needed to turn scalar evolution into the
parabolic WMP inequality with zero drift. -/
def ScalarLaplacianRealizesHeatOperatorOn
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap : Real -> M -> Real) : Prop :=
  forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
    scalarLap t x =
      Realized.heatOperator (I := I) G t (scalar t) x

namespace ScalarLaplacianRealizesHeatOperatorOn

theorem zero_drift
    {G : Realized.RealizedMetricFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x =
        Realized.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
  intro t ht x
  calc
    scalarLap t x = Realized.heatOperator (I := I) G t (scalar t) x := h t ht x
    _ = Realized.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
        rw [Realized.heatOperatorWithDrift_zero_drift]

theorem of_laplacianAt
    {G : Realized.RealizedMetricFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x = Realized.laplacianAt (I := I) G t (scalar t) x) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap := by
  intro t ht x
  simpa [Realized.heatOperator] using h t ht x

end ScalarLaplacianRealizesHeatOperatorOn

section TraceRoute

variable {Idx : Type*} [Fintype Idx]

/-- Scalar curvature as the metric trace of the Ricci tensor in a fixed frame:
`R = g^{ij} Ric_ij`. -/
def scalarTraceInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      gInv t x i j * ricciCompInFrame (I := I) S frame t x i j

@[simp] theorem scalarTraceInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        gInv t x i j * ricciCompInFrame (I := I) S frame t x i j := by
  rfl

/-! ## Trace/norm Cauchy-Schwarz interface -/

/-- Finite-sum Cauchy-Schwarz in the form needed for the trace of a two-index
component family. -/
theorem trace_sq_le_card_mul_sum_sq_two
    (A : Idx -> Idx -> Real) :
    (∑ i : Idx, A i i) ^ 2 <=
      (Fintype.card Idx : Real) * (∑ i : Idx, ∑ j : Idx, A i j ^ 2) := by
  classical
  have hcs :
      (∑ i : Idx, A i i) ^ 2 <=
        (Fintype.card Idx : Real) * (∑ i : Idx, A i i ^ 2) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Idx)) (f := fun i => A i i))
  have hdiag :
      (∑ i : Idx, A i i ^ 2) <=
        (∑ i : Idx, ∑ j : Idx, A i j ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact Finset.single_le_sum
      (fun j _hj => sq_nonneg (A i j)) (Finset.mem_univ i)
  exact hcs.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _))

/-- Divide the finite-sum trace Cauchy-Schwarz inequality by the nonzero
rank. -/
theorem trace_sq_div_rank_le_sum_sq_two
    [Nonempty Idx] (A : Idx -> Idx -> Real) :
    (1 / (Fintype.card Idx : Real)) * (∑ i : Idx, A i i) ^ 2 <=
      ∑ i : Idx, ∑ j : Idx, A i j ^ 2 := by
  classical
  have hcard : 0 < (Fintype.card Idx : Real) := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have h :=
    trace_sq_le_card_mul_sum_sq_two (Idx := Idx) A
  have hdiv :
      (∑ i : Idx, A i i) ^ 2 / (Fintype.card Idx : Real) <=
        ∑ i : Idx, ∑ j : Idx, A i j ^ 2 := by
    rw [div_le_iff₀ hcard]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Product-rule RHS for differentiating the scalar trace
`g^{ij} Ric_ij`. -/
def scalarTraceDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j +
      gInv t x i j *
        ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)

/-- The supplied scalar Laplacian is the metric trace of the rough Laplacian
of Ricci in the chosen frame. -/
def ScalarLaplacianTraceInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real) : Prop :=
  ∀ t x,
    scalarLap t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j

/-- The canonical scalar Laplacian trace used by the scalar-curvature
evolution theorem once the rough Laplacian of Ricci has been supplied. -/
def scalarLaplacianTraceInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) :
    Real -> M -> Real :=
  fun t x => ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j

@[simp] theorem scalarLaplacianTraceInFrame_apply
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) :
    scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j := by
  rfl

/-- The canonical scalar Laplacian trace satisfies the realization predicate
by definition. -/
theorem scalarLaplacianTraceInFrame_realizes
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) :
    ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) := by
  intro t x
  rfl

/-- Exact heat-operator hook for the canonical scalar Laplacian trace.  The
remaining geometric producer is the displayed `laplacianAt` equality, normally
proved through the Hessian-trace API. -/
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
        Realized.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) :=
  ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
    (I := I) (G := G) (T := T)
    (scalar := scalarTraceInFrame (I := I) S gInv frame)
    (scalarLap := scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) h

/-- Producer from the Hessian-trace API to the heat-operator realization for
the canonical scalar Laplacian trace.

The remaining geometric input is the pointwise component realization
`hcomp`: the scalar Hessian whose metric trace realizes `Delta R` has
components `roughLapRic` in the chosen frame. -/
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_hessianTrace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame Set.univ)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarHess : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Realized.ScalarLaplacianRealizesTraceAtInBasis (I := I)
        (G.connection t) (G.metric t)
        (hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M)))
        (gInv t x) (scalarTraceInFrame (I := I) S gInv frame t)
        (scalarHess t x))
    (hcomp : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      forall i j : Idx,
        scalarHess t x (Realized.vec2 (I := I) (frame i x) (frame j x)) =
          roughLapRic t x i j) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) := by
  refine scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    (I := I) S G T gInv frame roughLapRic ?_
  intro t ht x
  let basis := hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M))
  have hmetric :
      Realized.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 =
        scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x := by
    unfold Realized.metricTrace0S2InBasis scalarLaplacianTraceInFrame
    refine Finset.sum_congr rfl fun i _hi => ?_
    refine Finset.sum_congr rfl fun j _hj => ?_
    congr 1
    have hinput :
        Realized.metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
          Realized.vec2 (I := I) (frame i x) (frame j x) := by
      have hbi : basis i = frame i x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      have hbj : basis j = frame j x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      rw [hbi, hbj]
      funext q
      fin_cases q
      · simp [Realized.metricTraceInput, Realized.vec2, RicciFlower.Curvature.vec2]
      · rfl
    rw [hinput, hcomp t ht x i j]
  have htrace_tx := htrace t ht x
  unfold Realized.ScalarLaplacianRealizesTraceAtInBasis at htrace_tx
  calc
    scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
        Realized.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 := hmetric.symm
    _ = Realized.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x := by
        unfold Realized.laplacianAt
        exact htrace_tx.symm

/-- Trace/norm Cauchy-Schwarz for a chosen frame.  This is the explicit
arbitrary-frame frontier consumed by Corollary 7.3. -/
def RicciTraceNormCauchySchwarzInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (n : Real) : Prop :=
  forall t : Real, forall x : M,
    (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
      ricciNormSqInFrame (I := I) S gInv frame t x

/-- A local frame turns the scalar-file inverse-component predicate into the
basis-level inverse predicate used by pointwise tensor contraction lemmas. -/
private theorem metricInverseInBasis_of_solution_frame
    {D : Realized.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u) :
    MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x i j).2

/-- The coordinate scalar trace is the intrinsic metric trace of the bundled
Ricci tensor. -/
theorem scalarTraceInFrame_eq_metricTracePair
    {D : Realized.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      Realized.metricTracePair0SAt (I := I) (S.family.metric t) (S.ricci t x) := by
  classical
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  rw [Realized.metricTracePair0SAt_eq_sum_basis
    (I := I) (S.family.metric t) basis (fun i j : Idx => gInv t x i j) hinvAt]
  simp [scalarTraceInFrame, ricciCompInFrame, basis, IsLocalFrameOn.toBasisAt_coe]

/-- The coordinate Ricci norm is the intrinsic squared norm of the bundled
Ricci tensor. -/
theorem ricciNormSqInFrame_eq_normSq0S
    {D : Realized.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) := by
  classical
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  rw [normSq0S_eq_inner]
  rw [inner0S_two_eq_coord
    (I := I) (S.family.metric t) x basis
    (fun i j : Idx => gInv t x i j) hinvAt (S.ricci t x) (S.ricci t x)]
  simp [ricciNormSqInFrame, raisedRicciCompInFrame, ricciCompInFrame,
    Realized.vec2, basis, IsLocalFrameOn.toBasisAt_coe,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hij :
      RicciFlower.Curvature.vec2 (I := I) (frame i x) (frame j x) =
        (fun a : Fin 2 => if a = 0 then frame i x else frame j x) := by
    funext a
    fin_cases a <;> simp [RicciFlower.Curvature.vec2]
  have hkl :
      RicciFlower.Curvature.vec2 (I := I) (frame k x) (frame l x) =
        (fun a : Fin 2 => if a = 0 then frame k x else frame l x) := by
    funext a
    fin_cases a <;> simp [RicciFlower.Curvature.vec2]
  rw [hij, hkl]

/-- In an orthonormal frame, raising both Ricci indices leaves components
unchanged. -/
theorem raisedRicciCompInFrame_eq_of_orthonormal_inv
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j := by
  classical
  unfold raisedRicciCompInFrame
  simp [hInvDelta]

/-- In an orthonormal frame, the scalar trace is the sum of diagonal Ricci
components. -/
theorem scalarTraceInFrame_eq_trace_of_orthonormal_inv
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ricciCompInFrame (I := I) S frame t x i i := by
  classical
  unfold scalarTraceInFrame
  simp [hInvDelta]

/-- In an orthonormal frame, the Ricci norm is the sum of squared components. -/
theorem ricciNormSqInFrame_eq_sum_sq_of_orthonormal_inv
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j ^ 2 := by
  classical
  unfold ricciNormSqInFrame
  refine Finset.sum_congr rfl fun i _hi => ?_
  refine Finset.sum_congr rfl fun j _hj => ?_
  rw [raisedRicciCompInFrame_eq_of_orthonormal_inv
    (I := I) S gInv frame hInvDelta t x i j]
  ring

/-- Orthonormal-frame version of `|Ric|^2 >= R^2 / n`. -/
theorem ricciNormSqInFrame_ge_scalarTrace_sq_div_rank_of_orthonormal_inv
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    (1 / (Fintype.card Idx : Real)) *
        (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  rw [scalarTraceInFrame_eq_trace_of_orthonormal_inv
      (I := I) S gInv frame hInvDelta t x,
    ricciNormSqInFrame_eq_sum_sq_of_orthonormal_inv
      (I := I) S gInv frame hInvDelta t x]
  exact trace_sq_div_rank_le_sum_sq_two
    (Idx := Idx) (fun i j => ricciCompInFrame (I := I) S frame t x i j)

namespace RicciTraceNormCauchySchwarzInFrame

/-- The arbitrary-frame trace/norm predicate is realized immediately in an
orthonormal frame with `n = card Idx`. -/
theorem of_orthonormal_inv
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (n : Real)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (hn : n = (Fintype.card Idx : Real)) :
    RicciTraceNormCauchySchwarzInFrame (I := I) S gInv frame n := by
  subst n
  intro t x
  exact ricciNormSqInFrame_ge_scalarTrace_sq_div_rank_of_orthonormal_inv
    (I := I) S gInv frame hInvDelta t x

/-- A local-frame inverse metric realization gives the full arbitrary-frame
trace/norm Cauchy-Schwarz inequality. -/
theorem of_metric_inverse_frame
    {D : Realized.RealTimeInterval}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame Set.univ)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (n : Real)
    (hn : n = (Fintype.card Idx : Real)) :
    RicciTraceNormCauchySchwarzInFrame (I := I) S gInv frame n := by
  subst n
  intro t x
  have hx : x ∈ (Set.univ : Set M) := Set.mem_univ x
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  rw [scalarTraceInFrame_eq_metricTracePair
      (I := I) S gInv frame hframe hinv t hx,
    ricciNormSqInFrame_eq_normSq0S
      (I := I) S gInv frame hframe hinv t hx]
  exact Realized.metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := I) (S.family.metric t) basis (fun i j : Idx => gInv t x i j)
    hinvAt (S.ricci t x)

end RicciTraceNormCauchySchwarzInFrame

/-- The remaining convention-sensitive curvature trace after substituting
Lemma 6.3 into the derivative of `R = g^{ij} Ric_ij`. -/
def ScalarRmRicciTraceInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    (∑ i : Idx, ∑ j : Idx,
      gInv (t : Real) x i j *
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j) =
      -ricciNormSqInFrame (I := I) S gInv frame (t : Real) x

/-- Produce the remaining scalar-trace curvature contraction from the
convention-correct first trace of `Rm04`. -/
theorem scalarRmRicciTraceInFrame_of_rm04_first_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame Set.univ)
    (hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M))))
    (hOutput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame := by
  classical
  intro t x
  let basis := hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M))
  have hRicAt : forall i j : Idx,
      (S.ricci (t : Real) x) (Realized.vec2 (basis i) (basis j)) =
        (S.ricci (t : Real) x) (Realized.vec2 (basis j) (basis i)) := by
    intro i j
    simpa [basis, ricciCompInFrame, Realized.ricciComp,
      RicciFlower.Curvature.ricciComp, IsLocalFrameOn.toBasisAt_coe] using
      hRicSym (t : Real) x i j
  have hmain :=
    Realized.metricTrace_rm04RicciContractionAt_eq_neg_inner
      (I := I) basis (Rm04 (t : Real) x) (gInv (t : Real) x)
      (S.ricci (t : Real) x) (hTrace t x) (hOutput t x) (hFirst t x)
      hRicAt (hInvSym (t : Real) x)
  simpa [basis, Realized.rm04RicciContractionAt, Realized.raised02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame,
    ricciNormSqInFrame, Realized.rm04Comp, RicciFlower.Curvature.rm04Comp,
    ricciCompInFrame, Realized.ricciComp, RicciFlower.Curvature.ricciComp,
    IsLocalFrameOn.toBasisAt_coe] using hmain

/-- The inverse-metric evolution term in `∂ₜ(g^{ij} Ric_ij)` is
`2 |Ric|^2`. -/
theorem scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j) =
      2 * ricciNormSqInFrame (I := I) S gInv frame t x := by
  unfold inverseMetricEvolutionRHSInFrame ricciNormSqInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j)
        =
      ∑ i : Idx, ∑ j : Idx,
        2 * (ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          simp [Finset.mul_sum]

/-- The metric trace of the Ricci-quadratic term `Ric_i^k Ric_kj` is
`|Ric|^2`. -/
theorem scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j) =
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  unfold ricciQuadraticCompInFrame ricciOneUpCompInFrame
    ricciNormSqInFrame raisedRicciCompInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx,
          (∑ a : Idx,
            gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
              gInv t x i j * gInv t x k a *
                ricciCompInFrame (I := I) S frame t x i a *
                ricciCompInFrame (I := I) S frame t x k j)
                =
              ∑ j : Idx, ∑ a : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          gInv t x i j * gInv t x a k *
          ricciCompInFrame (I := I) S frame t x j k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInvSym t x k a, hRicSym t x k j]
          ring
    _ =
      ∑ i : Idx, ∑ a : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          (∑ j : Idx, ∑ k : Idx,
            gInv t x i j * gInv t x a k *
              ricciCompInFrame (I := I) S frame t x j k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The trace algebra and scalar-Laplacian trace identify the derivative RHS
of `g^{ij} Ric_ij` with `Delta R + 2 |Ric|^2`. -/
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x
  have hrm := hRmTrace t x
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
      (I := I) S gInv frame hInvSym hRicSym (t : Real) x
  unfold scalarTraceDerivRHSInFrame
  rw [h_lap (t : Real) x]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j +
          gInv (t : Real) x i j *
            ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
              (t : Real) x i j)) =
        (∑ i : Idx, ∑ j : Idx,
          inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j) +
        (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j * roughLapRic (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
              (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) := by
    simp [ricciEvolutionRHSInFrame, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_mul]
    ring_nf
  rw [hsplit, hdt, hrm, hquad]
  ring

/-- Product-rule derivative of the scalar trace `g^{ij} Ric_ij`. -/
theorem scalarTraceInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x)
      (scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [scalarTraceInFrame, scalarTraceDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i j *
              ricciCompInFrame (I := I) S frame (t : Real) x i j +
            gInv (t : Real) x i j *
              ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
              (A' := fun j =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i j *
                    ricciCompInFrame (I := I) S frame (t : Real) x i j +
                  gInv (t : Real) x i j *
                    ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hInv := h_inv t x i j
                  have hRic := h_ricci t x i j
                  exact hInv.mul hRic))))

/-- Lemma 6.6 from Lemma 6.3 by tracing the Ricci equation. -/
theorem scalarEvolutionEquationOn_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hframe : IsLocalFrameOn I E 1 frame Set.univ)
    (hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M))))
    (hOutput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame) := by
  intro t x
  have htrace :=
    scalarTraceInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  have hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame :=
    scalarRmRicciTraceInFrame_of_rm04_first_trace
      (I := I) S Rm04 gInv frame hframe hTrace hOutput hFirst hInvSym hRicSym
  exact htrace.congr_deriv
    (scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
      (I := I) S Rm04 gInv frame roughLapRic
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (scalarLaplacianTraceInFrame_realizes (M := M) gInv roughLapRic)
      hInvSym hRicSym hRmTrace t x)

end TraceRoute

end RicciFlow
end RicciFlower
