import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Covariant

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}







theorem inverseMetricEvolutionEquationInFrame_of_inverse_components
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u := by
  intro t x hx i j
  have hrow : forall m : Idx,
      (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a m +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a m))) =
        0 := by
    intro m
    exact inverseMetric_derivative_row_eq
      (I := I) S hS gInv gInvDt frame hdt hinv hunique t x hx i m
  have hsolve :
      gInvDt (t : Real) x i j =
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j := by
    unfold inverseMetricEvolutionRHSInFrame raisedRicciCompInFrame
    exact inverseMetric_derivative_solve
      (metric := fun a b => metricCompInFrame (I := I) S frame (t : Real) x a b)
      (ric := fun a b => ricciCompInFrame (I := I) S frame (t : Real) x a b)
      (gInv := fun a b => gInv (t : Real) x a b)
      (gInvDt := fun a b => gInvDt (t : Real) x a b)
      i
      hrow
      (fun a b => (hinv (t : Real) x hx a b).1)
      (fun a b => (hinv (t : Real) x hx a b).2)
      (fun a b => by
        simpa [metricCompInFrame] using
          (S.family.metric (t : Real)).symm x (frame a x) (frame b x))
      j
  exact (hdt t x i j).congr_deriv hsolve






theorem inverseMetricEvolution_of_metricFrameTimeRegularity
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) S hS gInv gInvDt frame
    hreg.inverseMetricDerivative
    hreg.nondegenerateGram
    hreg.uniqueTimeDerivatives



theorem coordInvLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) :
    InvMetricLocal (I := I) S (coordInv (I := I) S x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  intro t x hx i j
  have hbasis :=
    DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) (S.family.metric t) x0 hx
  constructor
  · simpa [coordInv, metricCompInFrame,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using (hbasis i j).1
  · simpa [coordInv, metricCompInFrame,
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using (hbasis i j).2






theorem coordInvEvol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    InverseMetricEvolutionEquationInFrame
      (I := I) S (coordInv (I := I) S x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  intro t x hx i j
  let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0
  let gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E) :=
    coordInv (I := I) S x0
  let G : Real -> ((DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real)) :=
    fun s => frameGramCLM (I := I) S frame (s, x)
  let Gdot : (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) :=
    matrixCLM (Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E)
      (fun a b => (-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a b)
  let InvG : (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) :=
    ContinuousLinearMap.inverse (G (t : Real))
  let dInv : (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) :=
    -(InvG * Gdot * InvG)
  have hG :
      HasDerivWithinAt G Gdot D.carrier (t : Real) := by
    simpa [G, Gdot, frame] using
      frameGramCLM_hasDerivWithinAt (I := I) S hS frame t x
  have hbasis :=
    DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) (S.family.metric (t : Real)) x0 hx
  have hGinv : (G (t : Real)).IsInvertible := by
    dsimp [G]
    exact
      frameGramCLM_isInvertible_at
        (I := I) S gInv frame ((t : Real), x)
        (by
          intro a b
          simpa [gInv, coordInv, frame, metricCompInFrame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).1)
        (by
          intro a b
          simpa [gInv, coordInv, frame, metricCompInFrame,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).2)
  have hInv :
      HasDerivWithinAt
        (fun s : Real => ContinuousLinearMap.inverse (G s))
        dInv
        D.carrier
        (t : Real) := by
    have hF :=
      (hasFDerivAt_clmInv
        (G (t : Real)) hGinv).comp_hasFDerivWithinAt
        (t : Real) hG.hasFDerivWithinAt
    simpa [dInv, InvG, ContinuousLinearMap.mulLeftRight_apply] using hF.hasDerivWithinAt
  have hApp :
      HasDerivWithinAt
        (fun s : Real =>
          ContinuousLinearMap.inverse (G s)
            (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real)))
        (dInv
          (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real)))
        D.carrier
        (t : Real) := by
    simpa using
      hInv.clm_apply
        (hasDerivWithinAt_const
          (x := (t : Real)) (s := D.carrier)
          (c := Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real)))
  have hProj :
      HasDerivWithinAt
        (fun s : Real =>
          (ContinuousLinearMap.proj i :
            (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real)
            (ContinuousLinearMap.inverse (G s)
              (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real))))
        ((ContinuousLinearMap.proj i :
            (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real)
          (dInv
            (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real))))
        D.carrier
        (t : Real) := by
    simpa using
      (hasDerivWithinAt_const
        (x := (t : Real)) (s := D.carrier)
        (c := (ContinuousLinearMap.proj i :
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real))).clm_apply hApp
  have hsymm :
      forall a b : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E,
        gInv (t : Real) x a b = gInv (t : Real) x b a := by
    intro a b
    simpa [gInv, coordInv] using
      DifferentialGeometry.Tensor.Coordinates.gInvChart_symm (I := I) (S.family.metric (t : Real)) x0 hx a b
  have hDerivEq :
      (ContinuousLinearMap.proj i :
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real)
          (dInv
            (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real))) =
        inverseMetricEvolutionRHSInFrame
          (I := I) S gInv frame (t : Real) x i j := by
    have hEq := coordInvCLM_eq (I := I) S x0 hx (t : Real)
    have hentry :=
      matrixInvDerivEntry
        (Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E)
        (gInv := fun a b => gInv (t : Real) x a b)
        (ric := fun a b => ricciCompInFrame (I := I) S frame (t : Real) x a b)
        hsymm i j
    simpa [G, Gdot, InvG, dInv, gInv, frame, hEq, frameGInvCLM, matrixCLM,
      ContinuousLinearMap.mulLeftRight_apply, inverseMetricEvolutionRHSInFrame,
      raisedRicciCompInFrame] using hentry
  refine (hProj.congr_deriv hDerivEq).congr ?_ ?_
  · intro s _hs
    have hEq := coordInvCLM_eq (I := I) S x0 hx s
    simpa [G, gInv, frame, sum_mul_pi_single] using congrArg
      (fun A : (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) =>
        (ContinuousLinearMap.proj i :
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real)
          (A (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real))))
      hEq |>.symm
  · have hEq := coordInvCLM_eq (I := I) S x0 hx (t : Real)
    simpa [G, gInv, frame, sum_mul_pi_single] using congrArg
      (fun A : (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real]
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) =>
        (ContinuousLinearMap.proj i :
          (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E -> Real) →L[Real] Real)
          (A (Pi.single (M := fun _ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx E => Real) j (1 : Real))))
      hEq |>.symm



theorem evol_inverse_metric_inFrame
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (2 * raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have hEq : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u :=
    inverseMetricEvolution_of_metricFrameTimeRegularity
      (I := I) S hS gInv gInvDt frame hreg
  have h :=
    inverseMetricEvolutionEquationInFrame_apply
      (I := I) (S := S) (gInv := gInv) (frame := frame) hEq t x hx i j
  simpa [inverseMetricEvolutionRHSInFrame] using h




def metricCompInFrameData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (S.family.metric t).inner x (frame i x) (frame j x)

@[simp] theorem metricCompInFrameData_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrameData (I := I) S frame t x i j =
      (S.family.metric t).inner x (frame i x) (frame j x) := by
  rfl


def ricciCompInFrameData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  S.ricci t x (frame i x) (frame j x)

@[simp] theorem ricciCompInFrameData_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrameData (I := I) S frame t x i j =
      S.ricci t x (frame i x) (frame j x) := by
  rfl


def raisedRicciCompInFrameData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x i a * gInv t x j b *
      ricciCompInFrameData (I := I) S frame t x a b

@[simp] theorem raisedRicciCompInFrameData_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrameData (I := I) S gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b *
          ricciCompInFrameData (I := I) S frame t x a b := by
  rfl


theorem metricCompInFrameData_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.Integral.Connection.IsRealizedRicciFlowSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrameData (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrameData (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [metricCompInFrameData, ricciCompInFrameData] using
    DifferentialGeometry.Integral.Connection.metric_derivWithin_eq_neg_two_ricci_of_isRealizedRicciFlowSolutionOn
      (I := I) S hS t x (frame i x) (frame j x)


def InvMetricLocalData [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop :=
  forall t x, x ∈ u -> forall i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrameData (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrameData (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)


theorem inverseMetric_derivative_row_eq_data
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.Integral.Connection.IsRealizedRicciFlowSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InvMetricLocalData (I := I) S gInv frame u)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    (∑ a : Idx,
        (gInvDt (t : Real) x i a *
          metricCompInFrameData (I := I) S frame (t : Real) x a j +
        gInv (t : Real) x i a *
          ((-2 : Real) * ricciCompInFrameData (I := I) S frame (t : Real) x a j))) =
      0 := by
  let lhs : Real -> Real :=
    fun s => ∑ a : Idx,
      gInv s x i a * metricCompInFrameData (I := I) S frame s x a j
  have hlhs :
      HasDerivWithinAt lhs
        (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrameData (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrameData (I := I) S frame (t : Real) x a j)))
        D.carrier
        (t : Real) := by
    dsimp [lhs]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          gInv s x i a * metricCompInFrameData (I := I) S frame s x a j)
        (A' := fun a =>
          (gInvDt (t : Real) x i a *
            metricCompInFrameData (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrameData (I := I) S frame (t : Real) x a j)))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha =>
          by
            exact (hdt t x i a).mul
              (metricCompInFrameData_hasDerivWithinAt (I := I) S hS frame t x a j)))
  have hconst :
      HasDerivWithinAt lhs 0 D.carrier (t : Real) := by
    dsimp [lhs]
    exact
      (hasDerivWithinAt_const
        (x := (t : Real)) (s := D.carrier)
        (c := (if i = j then 1 else 0 : Real))).congr
        (fun s _hs => by
          exact (hinv s x hx i j).1)
        (by
          exact (hinv (t : Real) x hx i j).1)
  have h1 := hlhs.derivWithin (hunique t)
  have h0 := hconst.derivWithin (hunique t)
  exact h1.symm.trans h0


theorem evol_inverse_metric_inFrame_data
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.Integral.Connection.RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : DifferentialGeometry.Integral.Connection.IsRealizedRicciFlowSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InvMetricLocalData (I := I) S gInv frame u)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (2 * raisedRicciCompInFrameData (I := I) S gInv frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have hrow : forall m : Idx,
      (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrameData (I := I) S frame (t : Real) x a m +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrameData (I := I) S frame (t : Real) x a m))) =
        0 := by
    intro m
    exact inverseMetric_derivative_row_eq_data
      (I := I) S hS gInv gInvDt frame hdt hinv hunique t x hx i m
  have hsolve :
      gInvDt (t : Real) x i j =
        2 * raisedRicciCompInFrameData (I := I) S gInv frame (t : Real) x i j := by
    unfold raisedRicciCompInFrameData
    exact inverseMetric_derivative_solve
      (metric := fun a b => metricCompInFrameData (I := I) S frame (t : Real) x a b)
      (ric := fun a b => ricciCompInFrameData (I := I) S frame (t : Real) x a b)
      (gInv := fun a b => gInv (t : Real) x a b)
      (gInvDt := fun a b => gInvDt (t : Real) x a b)
      i
      hrow
      (fun a b => (hinv (t : Real) x hx a b).1)
      (fun a b => (hinv (t : Real) x hx a b).2)
      (fun a b => by
        simpa [metricCompInFrameData] using
          (S.family.metric (t : Real)).symm x (frame a x) (frame b x))
      j
  exact (hdt t x i j).congr_deriv hsolve


end Components

end DifferentialGeometry.PDE.RicciFlow
