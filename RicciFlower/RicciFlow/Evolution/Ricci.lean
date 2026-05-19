import RicciFlower.RicciFlow.Evolution.Connection
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.VectorBundle.PartialMfderiv
import RicciFlower.Curvature.Contractions
import RicciFlower.LeviCivita.Curvature
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Ricci Evolution by Tracing Riemann Evolution

This file contains the realized interval trace step for Lemma 6.3.  The
Riemann evolution calculation itself is represented by the component predicate
`RiemannEvolutionEquationInFrameOn`; once that is supplied, this file proves
that tracing through the inverse metric gives the existing
`RicciEvolutionEquationInFrame` predicate from `RicciFlow.Basic`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open RicciFlower.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- A time-indexed Ricci tensor realizes the lowered Riemann trace in a fixed
frame at every time. -/
def RicciTensorRealizesRm04TraceInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    Realized.RicciTensorRealizesRm04TraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame

/-- A time-indexed Ricci tensor realizes the convention-correct lowered Riemann
first trace in a fixed frame at every time:
`Ric_ij = g^{kl} Rm04(e_k,e_l,e_i,e_j)`. -/
def RicciTensorRealizesRm04FirstTraceInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    Realized.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame

/-- Regular-time version of the convention-correct lowered Riemann first
trace.  Lemma 6.3 only differentiates at regular times, so this is the natural
producer target for Ricci evolution. -/
def RicciTensorRealizesRm04FirstTraceInFrameOnRegular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Realized.RealTimeInterval.RegularTime D,
    Realized.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci (t : Real)) (Rm04 (t : Real)) (gInv (t : Real)) frame

theorem ricciCompInFrame_eq_rm04_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (htrace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Realized.rm04Comp (I := I) (Rm04 t) frame x k i j l := by
  simpa [ricciCompInFrame] using
    Realized.ricciComp_eq_trace (I := I)
      (S.ricci t) (Rm04 t) (gInv t) frame (htrace t) x i j

/-- A local frame turns the Ricci-flow inverse-component predicate into the
basis-level inverse predicate used by pointwise tensor contraction lemmas. -/
private theorem metricInverseInBasis_of_solution_frame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x i j).2

/-- Produce the convention-correct lowered Riemann first-trace realization of
the bundled Ricci tensor from the intrinsic `(1,3)` Ricci trace and lowering.

This is the separate trace-realization bridge used by the Ricci-evolution
commutator proof. -/
theorem ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hRicTrace13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    :
    RicciTensorRealizesRm04FirstTraceInFrameOnRegular
      (I := I) S Rm04 gInv frame := by
  intro t x i j
  have hx : x ∈ u := hcover x
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx)
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv (t : Real) hx
  have hAt :=
    Realized.ricciFirstTraceAt_of_rm13_section
      (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx)
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (S.ricci (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
      (hRicTrace13 t) (hLower t x)
      (Tensor0SBundle.invMetric_symm
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx) (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
  simpa [Realized.RicciTensorRealizesRm04FirstTraceInFrame,
    IsLocalFrameOn.toBasisAt_coe] using hAt i j

/-- Local smoothness of the time-slice connection at regular times, in the
form needed by the curvature Bianchi/skew producers. -/
def ConnectionLocallySmoothOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  forall t : Realized.RealTimeInterval.RegularTime D,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection (t : Real)) (1 : WithTop ℕ∞)

/-- Ricci symmetry in a fixed frame, only at regular flow times. -/
def RicciSymmetricInFrameOnRegular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) x i j,
    ricciCompInFrame (I := I) S frame (t : Real) x i j =
      ricciCompInFrame (I := I) S frame (t : Real) x j i

private theorem lcAt_regular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D) :
    RicciFlower.LeviCivita.IsLeviCivita (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) := by
  constructor
  · simpa [Realized.RealizedMetricFamilyOn.connectionAt,
      Realized.RealizedMetricFamilyOn.metricAt] using
      hS.leviCivita.1 (Realized.RealTimeInterval.regularToFlow t)
  · simpa [Realized.RealizedMetricFamilyOn.connectionAt] using
      hS.leviCivita.2 (Realized.RealTimeInterval.regularToFlow t)

private theorem rm04Realizes_regular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (t : Realized.RealTimeInterval.RegularTime D) :
    Realized.Rm04RealizesConnection (I := I) (S.family.metric (t : Real))
      (S.family.connection (t : Real)) (Rm04 (t : Real)) :=
  Realized.rm04RealizesLower (I := I) (S.family.metric (t : Real))
    (S.family.connection (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
    (hRm13 t) (hLower t)

/-- Output-skew producer for regular Ricci-flow time slices. -/
theorem rm04OutputSkew_regular
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact RicciFlower.LeviCivita.rm04OutputSkew_ofMC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (hcov t) (RicciFlower.LeviCivita.metricCompatible_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S hS t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

/-- First-Bianchi producer for regular Ricci-flow time slices. -/
theorem rm04FirstBianchi_regular
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact RicciFlower.LeviCivita.firstBianchi_ofTF
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (hcov t) (RicciFlower.LeviCivita.torsionFree_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S hS t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

/-- Pair-symmetry producer for regular Ricci-flow time slices. -/
theorem rm04PairSymm_regular
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W X Y Z) =
          Rm04 (t : Real) x (Realized.vec4 Y Z W X) := by
  intro t x
  exact RicciFlower.LeviCivita.rm04PairSymm_ofLC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (hcov t) (lcAt_regular (I := I) S hS t) (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

/-- Input-skew producer for regular Ricci-flow time slices. -/
theorem rm04InputSkew_regular
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W Y X Z) =
          -Rm04 (t : Real) x (Realized.vec4 W X Y Z) := by
  intro t x
  exact RicciFlower.LeviCivita.rm04InputSkew_ofRealizes
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

/-- Ricci symmetry in a fixed frame from the regular-time lowered Riemann
trace and Levi-Civita curvature symmetries. -/
theorem ricciSymm_regular
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hPair : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W X Y Z) =
          Rm04 (t : Real) x (Realized.vec4 Y Z W X))
    (hOutput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hInput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W Y X Z) =
          -Rm04 (t : Real) x (Realized.vec4 W X Y Z)) :
    RicciSymmetricInFrameOnRegular (I := I) S frame := by
  intro t x i j
  let basis := hframe.toBasisAt (hcover x)
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric (t : Real)) x
        basis (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv (t : Real)
      (hcover x)
  have hsym :=
    Realized.ricciSymm_of_rm04 (I := I) basis
      (fun a b : Idx => gInv (t : Real) x a b)
      (S.ricci (t : Real) x) (Rm04 (t : Real) x)
      (hTrace t x) (hPair t x) (hOutput t x) (hInput t x)
      (Tensor0SBundle.invMetric_symm
        (I := I) (M := M) (S.family.metric (t : Real)) x basis
        (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
      i j
  simpa [basis, ricciCompInFrame, Realized.ricciComp,
    RicciFlower.Curvature.ricciComp, IsLocalFrameOn.toBasisAt_coe] using hsym

/-- Component form of a lowered Riemann evolution equation.  The future
producer is the realized analogue of synthetic `RiemannVariation.lean` plus
`RiemannEvolution.lean`. -/
def RiemannEvolutionEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (a i j l : Idx),
    HasDerivWithinAt
      (fun s : Real => Realized.rm04Comp (I := I) (Rm04 s) frame x a i j l)
      (rm04Dt (t : Real) x a i j l)
      D.carrier
      (t : Real)

/-! ## Ricci variation route for Lemma 6.3 -/

/-- Trace of the covariant derivative of the infinitesimal connection
variation:
`∇_k A^k_ij - ∇_i A^k_kj`.

Here `nablaGammaDt t x d k i j` denotes the fixed-frame component
`(∇_d A)^k_ij`, where `A^k_ij = ∂_t Γ^k_ij`. -/
def ricciVariationFromConnectionRHSInFrame
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, nablaGammaDt t x k k i j) -
    (∑ k : Idx, nablaGammaDt t x i k k j)

/-- Ricci variation formula in a fixed frame:
`∂_t Ric_ij = ∇_k A^k_ij - ∇_i A^k_kj`.

This is the realized component target obtained by differentiating the
curvature trace of the connection using the current `(1,3)` convention
`Ric(e_i,e_j) = trace (e_k ↦ R(e_k,e_i)e_j)`. -/
def RicciVariationFormulaInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Local version of the Ricci variation formula in a fixed frame domain. -/
def RicciVariationFormulaInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
          (t : Real) x i j)
        D.carrier
        (t : Real)

/-- Local version of Lemma 6.3's Ricci evolution equation in a fixed frame
domain. -/
def RicciEvolutionEquationInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)

theorem ricciVariationFormulaInFrameOn_of_local_cover
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcover : forall x : M, x ∈ u)
    (hlocal : RicciVariationFormulaInFrameOnLocal
      (I := I) S frame u nablaGammaDt) :
    RicciVariationFormulaInFrameOn (I := I) S frame nablaGammaDt := by
  intro t x i j
  exact hlocal t x (hcover x) i j

/-- The covariant derivative of the Ricci-flow connection variation after
substituting
`A^k_ij = -g^{kl} nabla_i Ric_jl - g^{kl} nabla_j Ric_il
  + g^{kl} nabla_l Ric_ij`.

Here `nabla2Ric t x d a i j` denotes `(nabla_d nabla_a Ric)_ij`.  Metric
compatibility is already reflected in this component expression: no derivative
falls on `gInv`. -/
def nablaGammaDtFromNabla2RicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d k i j : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x d i j l -
        nabla2Ric t x d j i l +
        nabla2Ric t x d l i j)

section CoordinateConnectionVariation

open RicciFlower.Coordinates

section RaisedContractAlgebra

variable {ι : Type*} [Fintype ι]

private def lowerRHS
    (N : ι -> ι -> ι -> Real) (i j l : ι) : Real :=
  -N i j l - N j i l + N l i j

private def covD3
    (Γ : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (i j l : ι) : Real :=
  dB i j l -
    (∑ p : ι, Γ p i * B p j l) -
    (∑ p : ι, Γ p j * B i p l) -
    (∑ p : ι, Γ p l * B i j p)

private def covDInv
    (Γ G dG : ι -> ι -> Real) (k l : ι) : Real :=
  dG k l +
    (∑ a : ι, Γ k a * G a l) +
    (∑ a : ι, Γ l a * G k a)

private def covDChristoffelVariation
    (Γ : ι -> ι -> ι -> Real) (A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (dir k i j : ι) : Real :=
  dA dir i j k +
    (∑ a : ι, Γ dir a k * A i j a) -
    (∑ a : ι, Γ dir i a * A a j k) -
    (∑ a : ι, Γ dir j a * A i a k)

private theorem christoffel_curv_variation_algebra
    (Γ : ι -> ι -> ι -> Real) (A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (hΓsymm : ∀ a b c : ι, Γ a b c = Γ b a c)
    (i k j m : ι) :
    dA i k j m - dA k i j m +
        (∑ a : ι, (A k j a * Γ i a m + Γ k j a * A i a m)) -
        (∑ a : ι, (A i j a * Γ k a m + Γ i j a * A k a m)) =
      covDChristoffelVariation Γ A dA i m k j -
        covDChristoffelVariation Γ A dA k m i j := by
  classical
  unfold covDChristoffelVariation
  have hmid :
      (∑ a : ι, Γ i k a * A a j m) =
        ∑ a : ι, Γ k i a * A a j m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hΓsymm i k a]
  have hleft :
      (∑ a : ι, A k j a * Γ i a m) =
        ∑ a : ι, Γ i a m * A k j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hright :
      (∑ a : ι, A i j a * Γ k a m) =
        ∑ a : ι, Γ k a m * A i j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleft, hright, hmid]
  ring

private theorem sum_swap_inverse_metric_third_slot
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l) =
      ∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a) := by
  classical
  calc
    (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l)
        = ∑ l : ι, ∑ a : ι, (Γ l a * G k a) * B i j l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ a : ι, ∑ l : ι, (Γ l a * G k a) * B i j l := by
            rw [Finset.sum_comm]
    _ = ∑ l : ι, ∑ a : ι, (Γ a l * G k l) * B i j a := by
            rfl
    _ = ∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring

private theorem sum_upper_contract
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l) =
      ∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l) := by
  classical
  calc
    (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l)
        = ∑ l : ι, ∑ a : ι, (Γ k a * G a l) * B i j l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ a : ι, ∑ l : ι, (Γ k a * G a l) * B i j l := by
            rw [Finset.sum_comm]
    _ = ∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring

private theorem sum_lower_contract
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k j q : ι) :
    (∑ l : ι, G k l * (∑ a : ι, Γ a q * B a j l)) =
      ∑ a : ι, Γ a q * (∑ l : ι, G k l * B a j l) := by
  classical
  calc
    (∑ l : ι, G k l * (∑ a : ι, Γ a q * B a j l))
        = ∑ l : ι, ∑ a : ι, G k l * (Γ a q * B a j l) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ a : ι, ∑ l : ι, G k l * (Γ a q * B a j l) := by
            rw [Finset.sum_comm]
    _ = ∑ a : ι, Γ a q * (∑ l : ι, G k l * B a j l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring

private theorem raised_contract_covD_algebra
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (dG k l * B i j l + G k l * dB i j l)) +
        (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) -
        (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
        (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) =
      (∑ l : ι, covDInv Γ G dG k l * B i j l) +
        ∑ l : ι, G k l * covD3 Γ B dB i j l := by
  classical
  symm
  unfold covDInv covD3
  have hfirst :
      (∑ l : ι,
          (dG k l + (∑ a : ι, Γ k a * G a l) +
            (∑ a : ι, Γ l a * G k a)) * B i j l) =
        (∑ l : ι, dG k l * B i j l) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) +
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
    calc
      (∑ l : ι,
          (dG k l + (∑ a : ι, Γ k a * G a l) +
            (∑ a : ι, Γ l a * G k a)) * B i j l)
          =
        (∑ l : ι, dG k l * B i j l) +
          (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l) +
          (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l) := by
            simp [add_mul, Finset.sum_add_distrib, add_assoc]
      _ =
        (∑ l : ι, dG k l * B i j l) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) +
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
            rw [sum_upper_contract (Γ := Γ) (G := G) (B := B)
              (k := k) (i := i) (j := j)]
            rw [sum_swap_inverse_metric_third_slot (Γ := Γ) (G := G) (B := B)
              (k := k) (i := i) (j := j)]
  have hsecond :
      (∑ l : ι,
          G k l *
            (dB i j l - (∑ p : ι, Γ p i * B p j l) -
              (∑ p : ι, Γ p j * B i p l) -
              (∑ p : ι, Γ p l * B i j p))) =
        (∑ l : ι, G k l * dB i j l) -
          (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) -
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
    calc
      (∑ l : ι,
          G k l *
            (dB i j l - (∑ p : ι, Γ p i * B p j l) -
              (∑ p : ι, Γ p j * B i p l) -
              (∑ p : ι, Γ p l * B i j p)))
          =
        (∑ l : ι, G k l * dB i j l) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p i * B p j l)) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p j * B i p l)) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p l * B i j p)) := by
            simp only [mul_sub]
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_sub_distrib]
      _ =
        (∑ l : ι, G k l * dB i j l) -
          (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) -
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
            rw [sum_lower_contract (Γ := Γ) (G := G) (B := B)
              (k := k) (j := j) (q := i)]
            rw [sum_lower_contract (Γ := Γ) (G := G)
              (B := fun a q l => B q a l) (k := k) (j := i) (q := j)]
  rw [hfirst, hsecond]
  rw [Finset.sum_add_distrib]
  ring

private theorem raised_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (k i j : ι) (hzero : ∀ l : ι, covDInv Γ G dG k l = 0) :
    (∑ l : ι, (dG k l * B i j l + G k l * dB i j l)) +
        (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) -
        (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
        (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) =
      ∑ l : ι, G k l * covD3 Γ B dB i j l := by
  rw [raised_contract_covD_algebra (Γ := Γ) (G := G) (dG := dG)
    (B := B) (dB := dB) (k := k) (i := i) (j := j)]
  simp [hzero]

private theorem covD3_lowerRHS
    (Γ : ι -> ι -> Real) (N dN : ι -> ι -> ι -> Real)
    (i j l : ι) :
    covD3 Γ (lowerRHS N) (lowerRHS dN) i j l =
      -covD3 Γ N dN i j l -
        covD3 Γ N dN j i l +
        covD3 Γ N dN l i j := by
  classical
  unfold covD3 lowerRHS
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_add, mul_sub, mul_neg]
  ring

private theorem trace13_connection_terms_cancel
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l)) =
      ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l) := by
  classical
  calc
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l))
        = ∑ a : ι, ∑ k : ι, Γ k a * (∑ l : ι, G a l * B k j l) := by
            rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l) := by
            rfl

private theorem trace23_connection_terms_cancel
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l)) =
      ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l) := by
  classical
  calc
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l))
        = ∑ a : ι, ∑ k : ι, Γ k a * (∑ l : ι, G a l * B j k l) := by
            rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l) := by
            rfl

private theorem trace13_lower_slot_sum
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l)) =
      ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
  classical
  calc
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l))
        = ∑ a : ι, ∑ k : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
            rw [Finset.sum_comm]

private theorem trace23_lower_slot_sum
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l)) =
      ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
  classical
  calc
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l))
        = ∑ a : ι, ∑ k : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
            rw [Finset.sum_comm]

private theorem trace13_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (j : ι) (hzero : ∀ k l : ι, covDInv Γ G dG k l = 0) :
    (∑ k : ι, ∑ l : ι, (dG k l * B k j l + G k l * dB k j l)) -
        (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l)) =
      ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB k j l := by
  classical
  have hsum :
      (∑ k : ι,
        ((∑ l : ι, (dG k l * B k j l + G k l * dB k j l)) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l)) -
          (∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l)))) =
        ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB k j l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact raised_contract_covD_of_inv_zero
      (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
      (k := k) (i := k) (j := j) (hzero k)
  have hcancel := trace13_connection_terms_cancel (Γ := Γ) (G := G) (B := B) (j := j)
  rw [← hsum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcancel]
  rw [trace13_lower_slot_sum (Γ := Γ) (G := G) (B := B) (j := j)]
  ring

private theorem trace23_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (j : ι) (hzero : ∀ k l : ι, covDInv Γ G dG k l = 0) :
    (∑ k : ι, ∑ l : ι, (dG k l * B j k l + G k l * dB j k l)) -
        (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l)) =
      ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB j k l := by
  classical
  have hsum :
      (∑ k : ι,
        ((∑ l : ι, (dG k l * B j k l + G k l * dB j k l)) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l)) -
          (∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l)))) =
        ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB j k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact raised_contract_covD_of_inv_zero
      (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
      (k := k) (i := j) (j := k) (hzero k)
  have hcancel := trace23_connection_terms_cancel (Γ := Γ) (G := G) (B := B) (j := j)
  rw [← hsum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcancel]
  rw [trace23_lower_slot_sum (Γ := Γ) (G := G) (B := B) (j := j)]
  ring

end RaisedContractAlgebra

private theorem ricci_mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem ricci_extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
        exact ricci_mdiffAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

private theorem ricci_extDerivFun_mul
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

private theorem ricci_extDerivFun_add
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y + g y) x v =
      extDerivFun (I := I) f x v + extDerivFun (I := I) g x v := by
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := g) (x := x) hf hg) v)
  simpa [Pi.add_apply] using hadd

private theorem ricci_extDerivFun_neg
    {f : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    extDerivFun (I := I) (fun y : M => -f y) x v =
      -extDerivFun (I := I) f x v := by
  have hfun : (fun y : M => -f y) = ((fun _ : M => (-1 : Real)) • f) := by
    ext y
    simp
  rw [hfun]
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => (-1 : Real)) (g := f)
    (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (-1 : Real)) (x := x))
    hf v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul] using hprod

private theorem ricci_extDerivFun_sub
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y - g y) x v =
      extDerivFun (I := I) f x v - extDerivFun (I := I) g x v := by
  have hneg := ricci_extDerivFun_neg (I := I) (f := g) (x := x) v hg
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := fun y : M => -g y)
    (x := x) hf hg.neg) v)
  simpa [Pi.add_apply, sub_eq_add_neg, hneg] using hadd

private theorem ricci_extDerivFun_congr_eventually
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

private theorem contractedTrace13CovDeriv_eq_nabla2RicTrace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x k a l)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d k j l := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    RicciFlower.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y k j l)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * N k j l + G k l * dN k j l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y k j l)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y k j l)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y k j l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y k j l)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y k j l)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y k j l)
          (hginv_mdiff k l) (hN_mdiff k j l)]
        simp [G, dG, N, dN]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff k j l)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y k j l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y k j l)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y k j l)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff k j l))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x k a l))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * N k j l + G k l * dN k j l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * N k a l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ N dN k j l := by
          exact trace13_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := N) (dB := dN)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d k j l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, ricciSecondCovDerivCompInFrame]

private theorem contractedTrace23CovDeriv_eq_nabla2RicTrace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x a k l)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d j k l := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    RicciFlower.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y j k l)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * N j k l + G k l * dN j k l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y j k l)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y j k l)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y j k l)
          (hginv_mdiff k l) (hN_mdiff j k l)]
        simp [G, dG, N, dN]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff j k l)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y j k l)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y j k l)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff j k l))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x a k l))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * N j k l + G k l * dN j k l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * N a k l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ N dN j k l := by
          exact trace23_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := N) (dB := dN)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d j k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, ricciSecondCovDerivCompInFrame]

private theorem contractedTraceBianchiCovDeriv_eq_nabla2RicTrace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l k a)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d l k j := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    RicciFlower.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  let B : Idx -> Idx -> Idx -> Real := fun a b c => N c b a
  let dB : Idx -> Idx -> Idx -> Real := fun a b c => dN c b a
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y l k j)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * B j k l + G k l * dB j k l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y l k j)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y l k j)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y l k j) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y l k j)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y l k j)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y l k j)
          (hginv_mdiff k l) (hN_mdiff l k j)]
        simp [G, dG, N, dN, B, dB]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff l k j)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y l k j) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y l k j)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y l k j)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff l k j))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j)
        x (frame d x) -
      (∑ a : Idx,
        RicciFlower.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l k a))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * B j k l + G k l * dB j k l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * B a k l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ B dB j k l := by
          exact trace23_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d l k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, B, dB, ricciSecondCovDerivCompInFrame]
          ring

private theorem contractedTrace23_mdiffAt
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) {x : M} (j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => ∑ k : Idx, ∑ l : Idx,
        gInv t y k l * nablaRic t y j k l) x := by
  classical
  have hsumfun :
      (fun y : M => ∑ k : Idx, ∑ l : Idx,
        gInv t y k l * nablaRic t y j k l) =
        ((Finset.univ : Finset Idx).sum
          (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)) := by
    ext y
    simp
  rw [hsumfun]
  refine ricci_mdiffAt_finset_sum (I := I)
    (t := (Finset.univ : Finset Idx))
    (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) ?_
  intro k _hk
  change MDifferentiableAt I 𝓘(Real, Real)
    (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) x
  have hsumfun_l :
      (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
        ((Finset.univ : Finset Idx).sum
          (fun l y => gInv t y k l * nablaRic t y j k l)) := by
    ext y
    simp
  rw [hsumfun_l]
  exact ricci_mdiffAt_finset_sum (I := I)
    (t := (Finset.univ : Finset Idx))
    (f := fun l y => gInv t y k l * nablaRic t y j k l)
    (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff j k l))

/-- Coordinate covariant derivative of a Christoffel-variation tensor
`A^k_ij` in the chart-induced coordinate frame.

This is kept only as the algebraic target for the `∇A` substitution below;
the old Christoffel-evolution-to-Riemann13 producer chain was removed from this
file because downstream Lemma 6.3 now consumes the Ricci variation formula
through the cleaner `RicciVariationFormulaInFrameOn` interface. -/
def christoffelVariationCovDerivCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (dir k i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (fun x : M => gammaDt t x i j k) x₀
      (coordinateFrameAt (I := I) x₀ dir x₀) +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir a k *
        gammaDt t x₀ i j a) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir i a *
        gammaDt t x₀ a j k) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir j a *
        gammaDt t x₀ i a k)

/-- Torsion-freeness of a Ricci-flow solution makes coordinate Christoffel
symbols symmetric in the two lower slots at regular times. -/
private theorem christoffelCoordAt_symm_of_isSolutionOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : Realized.RealTimeInterval.RegularTime D) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ i j k =
      Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ j i k := by
  have htf : RicciFlower.LeviCivita.IsTorsionFree (I := I)
      (S.family.connection (t : Real)) := by
    simpa [Realized.RealizedMetricFamilyOn.connectionAt] using
      hS.leviCivita.2 (Realized.RealTimeInterval.regularToFlow t)
  have hzero :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k x₀
          ((S.family.connection (t : Real)).torsion x₀
            (coordinateFrameAt (I := I) x₀ i x₀)
            (coordinateFrameAt (I := I) x₀ j x₀)) = 0 := by
    rw [htf x₀]
    simp
  have hskew := RicciFlower.LeviCivita.coordinate_torsion_coeff_eq_christoffel_skew
    (I := I) (S.family.connection (t : Real)) x₀ i j k
  rw [hzero] at hskew
  exact sub_eq_zero.mp hskew.symm

/-- Time derivative of a spatial coordinate derivative of a Christoffel
component, supplied by the mixed derivative regularity predicate. -/
private theorem christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : Realized.RealTimeInterval.RegularTime D)
    (dir i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCoordDerivAt (I := I) (S.family.connection s)
          x₀ dir i j k)
      (extDerivFun (I := I) (fun y : M => rhs (t : Real) y i j k) x₀
        (coordinateFrameAt (I := I) x₀ dir x₀))
      D.carrier
      (t : Real) := by
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  simpa [Realized.christoffelCoordDerivAt, Realized.christoffelCoordFun] using
    fixedBaseExtDerivTimeDerivativeOn_apply (I := I) (h := hmix i j k)
      (x := x₀) hx₀ (coordinateFrameAt (I := I) x₀ dir x₀)

/-- Time derivative of a coordinate Christoffel coefficient from a supplied
Christoffel variation formula. -/
private theorem christoffelCoordAt_hasDerivWithinAt_of_christoffelVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : Realized.RealTimeInterval.RegularTime D)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ i j k)
      (rhs (t : Real) x₀ i j k)
      D.carrier
      (t : Real) := by
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  simpa [Realized.christoffelCoordAt] using hvar t x₀ hx₀ i j k

/-- Differentiate the coordinate Christoffel curvature coefficient in time.

This is the full-coordinate version of the usual calculation
`∂ₜ R = ∇(∂ₜ Γ) - ∇(∂ₜ Γ)`: the `Γ A` product terms are kept and then
regrouped into the covariant derivative of the Christoffel variation tensor. -/
theorem christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : Realized.RealTimeInterval.RegularTime D)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCurvCoeffAt (I := I) (S.family.connection s)
          x₀ i k j m)
      (christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real)) rhs (t : Real) x₀ i m k j -
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real)) rhs (t : Real) x₀ k m i j)
      D.carrier
      (t : Real) := by
  classical
  have hD_i := christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    (I := I) S rhs x₀ hmix t i k j m
  have hD_k := christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    (I := I) S rhs x₀ hmix t k i j m
  have hΓ :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real =>
            Realized.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ a b c)
          (rhs (t : Real) x₀ a b c) D.carrier (t : Real) := by
    intro a b c
    exact christoffelCoordAt_hasDerivWithinAt_of_christoffelVariation
      (I := I) S rhs x₀ hvar t a b c
  have hprod_left :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ k j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ i a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (rhs (t : Real) x₀ k j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ i a m +
          Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ k j a *
            rhs (t : Real) x₀ i a m))
        D.carrier
        (t : Real) := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hΓ k j a).mul (hΓ i a m)))
  have hprod_right :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ i j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ k a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (rhs (t : Real) x₀ i j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ k a m +
          Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ i j a *
            rhs (t : Real) x₀ k a m))
        D.carrier
        (t : Real) := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hΓ i j a).mul (hΓ k a m)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          Realized.christoffelCurvCoeffAt (I := I) (S.family.connection s)
            x₀ i k j m)
        ((extDerivFun (I := I) (fun y : M => rhs (t : Real) y k j m) x₀
            (coordinateFrameAt (I := I) x₀ i x₀) -
          extDerivFun (I := I) (fun y : M => rhs (t : Real) y i j m) x₀
            (coordinateFrameAt (I := I) x₀ k x₀)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (rhs (t : Real) x₀ k j a *
              Realized.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ i a m +
            Realized.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ k j a *
              rhs (t : Real) x₀ i a m)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (rhs (t : Real) x₀ i j a *
              Realized.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ k a m +
            Realized.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ i j a *
              rhs (t : Real) x₀ k a m)))
        D.carrier
        (t : Real) := by
    simpa [Realized.christoffelCurvCoeffAt, sub_eq_add_neg, add_assoc,
      Finset.sum_add_distrib] using
      (((hD_i.sub hD_k).add hprod_left).sub hprod_right)
  refine hraw.congr_deriv ?_
  have hsymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ a b c =
          Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ b a c := by
    intro a b c
    exact christoffelCoordAt_symm_of_isSolutionOn (I := I) S hS t x₀ a b c
  let Γ : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c =>
      Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ a b c
  let A : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c => rhs (t : Real) x₀ a b c
  let dA : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun dir a b c =>
      extDerivFun (I := I) (fun y : M => rhs (t : Real) y a b c) x₀
        (coordinateFrameAt (I := I) x₀ dir x₀)
  have hΓsymm : ∀ a b c : CoordinateIdx (𝕜 := Real) E, Γ a b c = Γ b a c := by
    intro a b c
    exact hsymm a b c
  simpa [Γ, A, dA, christoffelVariationCovDerivCoordAt,
    covDChristoffelVariation] using
    (christoffel_curv_variation_algebra Γ A dA hΓsymm i k j m)

/-- Differentiate the coordinate Christoffel trace formula for Ricci in time. -/
theorem christoffelRicciCoeffAt_hasDerivWithinAt_of_christoffelVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : Realized.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelRicciCoeffAt (I := I) (S.family.connection s)
          x₀ i j)
      (ricciVariationFromConnectionRHSInFrame (M := M)
        (fun τ x d k i j =>
          christoffelVariationCovDerivCoordAt (I := I)
            (S.family.connection τ) rhs τ x d k i j)
        (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCurvCoeffAt (I := I)
              (S.family.connection s) x₀ k i j k)
        (∑ k : CoordinateIdx (𝕜 := Real) E,
          (christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection (t : Real)) rhs (t : Real) x₀ k k i j -
            christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection (t : Real)) rhs (t : Real) x₀ i k k j))
        D.carrier
        (t : Real) := by
    exact HasDerivWithinAt.fun_sum fun k _ =>
      christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
        (I := I) S hS rhs x₀ hvar hmix t k i j k
  refine hsum.congr_deriv ?_
  simp [ricciVariationFromConnectionRHSInFrame, Finset.sum_sub_distrib]

/-- Coordinate-frame Ricci variation formula from differentiating the
Christoffel Ricci trace formula. -/
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelVariation
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hRicTrace : ∀ s : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      Realized.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs) :
    RicciVariationFormulaInFrameOnLocal (I := I) S
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (fun τ x d k i j =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ) rhs τ x d k i j) := by
  intro t x hx i j
  have hx_eq : x = x₀ := by
    simpa using hx
  subst x
  have hderiv :=
    christoffelRicciCoeffAt_hasDerivWithinAt_of_christoffelVariation
      (I := I) S hS rhs x₀ hvar hmix t i j
  have hricci :
      ∀ s : Real,
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j =
          Realized.christoffelRicciCoeffAt (I := I) (S.family.connection s) x₀ i j := by
    intro s
    unfold ricciCompInFrame
    change (S.ricci s x₀)
        (Realized.vec2 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
        Realized.christoffelRicciCoeffAt (I := I) (S.family.connection s) x₀ i j
    rw [hRicTrace s x₀]
    exact Realized.ricciFromRm13At_coordFrame_eq_christoffelRicciCoeffAt
      (I := I) (S.family.connection s) (Rm13 s) x₀ (hRm s) (hcurv s) i j
  exact hderiv.congr
    (fun s _hs => hricci s)
    (hricci (t : Real))

/-- Covariantly differentiating the Ricci-flow Christoffel variation and using
`nabla g^{-1} = 0` turns the actual Christoffel-variation tensor into the
book expression with second Ricci derivatives.

This is the precise component product-rule calculation for
`nabla_d (g^{kl} B_ijl) = g^{kl} nabla_d B_ijl`. -/
theorem christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D)
    (d k i j : CoordinateIdx (𝕜 := Real) E) :
    christoffelVariationCovDerivCoordAt (I := I)
        (S.family.connection (t : Real))
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ d k i j =
      nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x₀ d k i j := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hu : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hmc : RicciFlower.Connection.IsMetricCompatible (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) :=
    Realized.RealizedMetricFamilyOn.metricCompatibleAt_regular
      (I := I) S.family t
  have hginv_mdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gInv (t : Real) y a b) x₀ := by
    intro a b
    exact hmetricReg.gInv_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hmetric_mdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => metricCompInFrame (I := I) S frame (t : Real) y a b) x₀ := by
    intro a b
    exact hmetricReg.metricComp_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hginv_zero :
      ∀ k l : CoordinateIdx (𝕜 := Real) E,
        inverseMetricCovDerivCompInFrame (I := I) gInv
          (S.family.connection (t : Real)) frame hframe
          (t : Real) x₀ d k l = 0 := by
    intro k l
    exact inverseMetricCovDerivCompInFrame_eq_zero
      (I := I) S gInv (S.family.connection (t : Real)) frame hframe
      hmetricReg.nondegenerateGram (t : Real)
      hmc hu hx₀ hginv_mdiff hmetric_mdiff d k l
  have hcalc :
      christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ d k i j =
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ k l *
            (-ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d i j l -
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d j i l +
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d l i j) := by
    /-
    This is the only remaining local calculus step in this theorem.  It is the
    finite-sum/product rule for
    `gammaDt^k_ij = ∑ l, gInv^{kl} B_ijl`, followed by the already-proved
    metric-layer identity
    `inverseMetricCovDerivCompInFrame_eq_zero` to cancel the `∂_d gInv`
    terms.  The theorem now receives that regularity through `hmetricReg` and
    `hnablaReg`; the remaining work is the finite-sum algebraic normalization.
    -/
    let Γ : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun up low => Realized.christoffelCoordAt (I := I)
        (S.family.connection (t : Real)) x₀ d low up
    let G : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a l => gInv (t : Real) x₀ a l
    let dG : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a l => extDerivFun (I := I) (fun y : M => gInv (t : Real) y a l)
        x₀ (frame d x₀)
    let N :
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
          CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a b c => nablaRic (t : Real) x₀ a b c
    let dN :
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
          CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a b c => extDerivFun (I := I)
        (fun y : M => nablaRic (t : Real) y a b c) x₀ (frame d x₀)
    have hN_mdiff :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x₀ := by
      intro a b c
      exact hnablaReg.first.mdiffAt (t : Real) x₀ hx₀ a b c
    have hlower_mdiff :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M =>
              christoffelVariationLoweredRHSInFrame nablaRic
                (t : Real) y a b c) x₀ := by
      intro a b c
      simpa [christoffelVariationLoweredRHSInFrame] using
        (((hN_mdiff a b c).neg.sub (hN_mdiff b a c)).add (hN_mdiff c a b))
    have hlower_deriv :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I)
              (fun y : M =>
                christoffelVariationLoweredRHSInFrame nablaRic
                  (t : Real) y a b c) x₀ (frame d x₀) =
            lowerRHS dN a b c := by
      intro a b c
      unfold christoffelVariationLoweredRHSInFrame lowerRHS dN
      rw [ricci_extDerivFun_add (I := I) (v := frame d x₀)
        (f := fun y : M => -nablaRic (t : Real) y a b c -
          nablaRic (t : Real) y b a c)
        (g := fun y : M => nablaRic (t : Real) y c a b)
        ((hN_mdiff a b c).neg.sub (hN_mdiff b a c)) (hN_mdiff c a b)]
      rw [ricci_extDerivFun_sub (I := I) (v := frame d x₀)
        (f := fun y : M => -nablaRic (t : Real) y a b c)
        (g := fun y : M => nablaRic (t : Real) y b a c)
        (hN_mdiff a b c).neg (hN_mdiff b a c)]
      rw [ricci_extDerivFun_neg (I := I) (v := frame d x₀)
        (f := fun y : M => nablaRic (t : Real) y a b c) (hN_mdiff a b c)]
    have hgamma_eval :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
              (t : Real) x₀ a b c =
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              G c l * lowerRHS N a b l := by
      intro a b c
      simp [christoffelEvolutionRHSInFrame,
        christoffelVariationLoweredRHSInFrame, lowerRHS, G, N]
    have hgamma_deriv :
        extDerivFun (I := I)
            (fun y : M =>
              christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
                (t : Real) y i j k) x₀ (frame d x₀) =
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            (dG k l * lowerRHS N i j l + G k l * lowerRHS dN i j l) := by
      unfold christoffelEvolutionRHSInFrame
      have hsumfun :
          (fun y : M =>
              ∑ l : CoordinateIdx (𝕜 := Real) E,
                gInv (t : Real) y k l *
                  christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l) =
            ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum
              (fun l y =>
                gInv (t : Real) y k l *
                  christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)) := by
        ext y
        simp
      rw [hsumfun]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (f := fun l y =>
          gInv (t : Real) y k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)
        (x := x₀) (v := frame d x₀)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x₀)
          (f := fun y : M => gInv (t : Real) y k l)
          (g := fun y : M =>
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)
          (hginv_mdiff k l) (hlower_mdiff i j l)]
        rw [hlower_deriv i j l]
        simp [G, dG, N, lowerRHS, christoffelVariationLoweredRHSInFrame]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hlower_mdiff i j l)
    have hInv :
        ∀ l : CoordinateIdx (𝕜 := Real) E, covDInv Γ G dG k l = 0 := by
      intro l
      have hz := hginv_zero k l
      simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame,
        Realized.christoffelCoordAt, frame, hframe] using hz
    calc
      christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ d k i j
          =
        (∑ l : CoordinateIdx (𝕜 := Real) E,
          (dG k l * lowerRHS N i j l + G k l * lowerRHS dN i j l)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ k a * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G a l * lowerRHS N i j l)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ a i * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G k l * lowerRHS N a j l)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ a j * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G k l * lowerRHS N i a l)) := by
            unfold christoffelVariationCovDerivCoordAt
            rw [hgamma_deriv]
            simp [hgamma_eval, Γ, G]
      _ = ∑ l : CoordinateIdx (𝕜 := Real) E,
            G k l * covD3 Γ (lowerRHS N) (lowerRHS dN) i j l := by
            exact raised_contract_covD_of_inv_zero
              (Γ := Γ) (G := G) (dG := dG)
              (B := lowerRHS N) (dB := lowerRHS dN)
              (k := k) (i := i) (j := j) hInv
      _ = ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ k l *
            (-ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d i j l -
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d j i l +
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d l i j) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [covD3_lowerRHS (Γ := Γ) (N := N) (dN := dN)
              (i := i) (j := j) (l := l)]
            unfold covD3 Γ G N dN ricciSecondCovDerivCompInFrame
            simp [Realized.christoffelCoordAt, frame]
  rw [hcalc]
  unfold nablaGammaDtFromNabla2RicInFrame
  have hnabla2_at := hnablaReg.second (t : Real) x₀ hx₀
  refine Finset.sum_congr rfl fun l _hl => ?_
  rw [hnabla2_at d i j l, hnabla2_at d j i l, hnabla2_at d l i j]

/-- Ricci-flow specialization of the coordinate-frame Ricci variation formula:
differentiate the Christoffel Ricci trace formula, use the Ricci-flow
Christoffel evolution, then substitute `nabla A = nabla^2 Ric`.  The only
regularity input left explicit is the honest mixed derivative
`partial_t partial_x Gamma = partial_x partial_t Gamma`. -/
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      Realized.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)) :
    RicciVariationFormulaInFrameOnLocal (I := I) S
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric) := by
  classical
  have hvar :
      ChristoffelVariationEquationInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic) := by
    have hGamma :
        ChristoffelEvolutionEquationInFrameOn (I := I) S gInv
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic :=
      christoffelEvolution_of_spacetimeSmoothMetric
        (I := I) S hS gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (coordinateFrameSet_open (I := I) x₀) nablaRic hmetricReg
        hnablaReg.first.realizes
    simpa [ChristoffelVariationEquationInFrameOn,
      ChristoffelEvolutionEquationInFrameOn] using hGamma
  have hlocal :=
    ricciVariationFormulaInCoordFrameAt_of_christoffelVariation
      (I := I) S hS (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
      Rm13 x₀ hRicTrace hRm hcurv hvar hmix
  intro t x hx i j
  have hx_eq : x = x₀ := by
    simpa using hx
  subst x
  have hbase := hlocal t x₀ (by simp) i j
  have hsum₁ :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ a a i j) =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ a a i j := by
    refine Finset.sum_congr rfl fun a _ha => ?_
    exact christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
      (I := I) S gInv nablaRic nabla2Ric x₀ gInvDt hmetricReg hnablaReg t a a i j
  have hsum₂ :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ i a a j) =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ i a a j := by
    refine Finset.sum_congr rfl fun a _ha => ?_
    exact christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
      (I := I) S gInv nablaRic nabla2Ric x₀ gInvDt hmetricReg hnablaReg t i a a j
  have hEq :
      ricciVariationFromConnectionRHSInFrame (M := M)
          (fun τ x d k i j =>
            christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection τ)
              (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
              τ x d k i j)
          (t : Real) x₀ i j =
        ricciVariationFromConnectionRHSInFrame (M := M)
          (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
          (t : Real) x₀ i j := by
    unfold ricciVariationFromConnectionRHSInFrame
    change
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ a a i j) -
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelVariationCovDerivCoordAt (I := I)
            (S.family.connection (t : Real))
            (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
            (t : Real) x₀ i a a j) =
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ a a i j) -
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x₀ i a a j)
    rw [hsum₁, hsum₂]
  exact hbase.congr_deriv hEq

end CoordinateConnectionVariation

/-- The rough Laplacian component `g^{ab} (nabla_a nabla_b Ric)_ij`. -/
def roughLapRicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x a b * nabla2Ric t x a b i j

/-- A component family realizes a supplied second covariant derivative tensor
of Ricci when it is obtained by evaluating a `(0,4)` tensor section on the
frame vectors.  The geometric assertion that this tensor is `∇∇Ric` is kept
separate from the component bookkeeping. -/
def Nabla2RicciTensorComponentsInFrameOn
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2RicTensor : Real -> Realized.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x d a i j,
    nabla2Ric t x d a i j =
      Realized.rm04Comp (I := I) (nabla2RicTensor t) frame x d a i j

/-- The Ricci variation RHS after substituting the Ricci-flow Christoffel
variation and expanding the trace
`nabla_k A^k_ij - nabla_i A^k_kj`.

This is the expression before the contracted-Bianchi/gauge cancellation and
the curvature-commutator simplification. -/
def ricciVariationExpandedRHSInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x k i j l -
        nabla2Ric t x k j i l +
        nabla2Ric t x k l i j)) -
    (∑ k : Idx, ∑ l : Idx,
      gInv t x k l *
        (-nabla2Ric t x i k j l -
          nabla2Ric t x i j k l +
          nabla2Ric t x i l k j))

/-- Algebraic substitution of the Ricci-flow connection variation into the
Ricci variation formula. -/
theorem ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationFromConnectionRHSInFrame (M := M)
        (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
        t x i j =
      ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j := by
  simp [ricciVariationFromConnectionRHSInFrame,
    nablaGammaDtFromNabla2RicInFrame, ricciVariationExpandedRHSInFrame]

/-- Final Lemma 6.3 reduction after expanding the Ricci variation formula.

This is exactly the textbook contracted-Bianchi plus covariant-derivative
commutator calculation: the gauge/scalar-Hessian terms cancel, and the
remaining commutator terms become
`-2 * rmRicciContractionCompInFrame - 2 Ric_i^k Ric_kj` in the project
lowered-curvature convention. -/
def RicciVariationExpandedRHS_eq_evolutionRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (t : Real) x i j

/-- The term `∇^k ∇_i Ric_jk` in the proof of Lemma 6.3. -/
def contractedNabla2RicLeftInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k i j l

/-- The term `∇^k ∇_j Ric_ik` in the proof of Lemma 6.3. -/
def contractedNabla2RicRightInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k j i l

/-- The scalar-Hessian trace `∇_i ∇_j R` as it appears before the Hessian
cancellation in the component proof. -/
def scalarHessianFromNabla2RicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i j k l

/-- The divergence trace term `∇_i ∇^k Ric_jk`. -/
def contractedNabla2RicTraceAInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i k j l

/-- The divergence trace term `∇_i ∇^l Ric_lj`. -/
def contractedNabla2RicTraceBInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i l k j

/-- The natural right trace produced directly by commuting
`∇^k ∇_j Ric_il` with the Ricci identity: `∇_j ∇^k Ric_ik`. -/
def contractedNabla2RicTraceRightNaturalInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x j k i l

/-- Pointwise contracted Bianchi in the two trace orientations used by the
differentiated Lemma 6.3 calculation.

The slot order is `nablaRic t x d a b = (∇_d Ric)_{ab}`.  The common
right-hand side is the frame trace of `∇_j Ric`, i.e. the scalar-gradient
component represented by the same component family. -/
def ContractedBianchiTraceInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall j : Idx,
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x k j l) =
        (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x j k l) ∧
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x l k j) =
        (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x j k l)

/-- Differentiated contracted Bianchi in the exact component form needed in
Lemma 6.3: both divergence-trace covariant derivatives are half the traced
second derivative of Ricci, i.e. half the scalar Hessian represented by
`nabla2Ric`. -/
def DifferentiatedContractedBianchiInFrame
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      (1 / 2 : Real) *
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j ∧
    contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j

/-- Symmetry of the scalar Hessian represented by `nabla2Ric`.  This is the
trace-level scalar Hessian symmetry needed to compare the natural right trace
with the `traceB` orientation. -/
def ScalarHessianFromNabla2RicSymmetricInFrame
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x j i

/-- Differentiated contracted Bianchi plus scalar-Hessian symmetry converts the
natural right trace to the `traceB` orientation used in the expanded Ricci
variation formula. -/
theorem contractedNabla2RicTraceRightNatural_eq_traceB
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x j i).1
  have hB := (hbianchi t x i j).2
  calc
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j
        = contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := rfl
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := hA
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by rw [← hHessSymm t x i j]
    _ = contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j := hB.symm

/-- Local differentiated contracted Bianchi, for use with local frames. -/
def DifferentiatedContractedBianchiInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall (i j : Idx),
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j ∧
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j

theorem DifferentiatedContractedBianchiInFrame.of_local_cover
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcover : forall x : M, x ∈ u)
    (h :
      DifferentiatedContractedBianchiInFrameOnLocal
        (D := D) (M := M) gInv nabla2Ric u) :
    DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric := by
  intro t x i j
  exact h t x (hcover x) i j

theorem differentiatedContractedBianchiInFrameOnLocal_of_regular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S frame u hframe nablaRic nabla2Ric)
    (hbianchi :
      ContractedBianchiTraceInFrameOnLocal
        (D := D) (M := M) gInv nablaRic u) :
    DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) gInv nabla2Ric u := by
  classical
  intro t x hx i j
  let scalarTrace : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y j k l
  let traceA : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y k j l
  let traceB : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y l k j
  let Γj : Idx -> Real := fun a =>
    RicciFlower.Coordinates.christoffelSymbolInFrame
      (S.family.connection (t : Real)) frame hframe x i j a
  have hginv_mdiff :
      ∀ a b : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gInv (t : Real) y a b) x := by
    intro a b
    exact hmetricReg.gInv_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx a b
  have hmetric_mdiff :
      ∀ a b : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => metricCompInFrame (I := I) S frame (t : Real) y a b) x := by
    intro a b
    exact hmetricReg.metricComp_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx a b
  have hN_mdiff :
      ∀ a b c : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic (t : Real) y a b c) x := by
    intro a b c
    exact hnablaReg.first.mdiffAt (t : Real) x hx a b c
  have hmc : RicciFlower.Connection.IsMetricCompatible (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) :=
    Realized.RealizedMetricFamilyOn.metricCompatibleAt_regular
      (I := I) S.family t
  have hginv_zero :
      ∀ k l : Idx,
        inverseMetricCovDerivCompInFrame (I := I) gInv
          (S.family.connection (t : Real)) frame hframe
          (t : Real) x i k l = 0 := by
    intro k l
    exact inverseMetricCovDerivCompInFrame_eq_zero
      (I := I) S gInv (S.family.connection (t : Real)) frame hframe
      hmetricReg.nondegenerateGram (t : Real)
      hmc hu hx hginv_mdiff hmetric_mdiff i k l
  have hnabla2_at := hnablaReg.second (t : Real) x hx
  have hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real) scalarTrace x := by
    dsimp [scalarTrace]
    exact contractedTrace23_mdiffAt
      (I := I) gInv nablaRic (t : Real) (x := x) j hginv_mdiff hN_mdiff
  have hhalf_deriv :
      extDerivFun (I := I) (fun y : M => (1 / 2 : Real) * scalarTrace y)
          x (frame i x) =
        (1 / 2 : Real) * extDerivFun (I := I) scalarTrace x (frame i x) := by
    rw [ricci_extDerivFun_mul (I := I) (v := frame i x)
      (f := fun _ : M => (1 / 2 : Real)) (g := scalarTrace)
      (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (1 / 2 : Real)) (x := x))
      hscalar_mdiff]
    simp
  have hscalar_cov :=
    contractedTrace23CovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have htraceA_cov :=
    contractedTrace13CovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have htraceB_cov :=
    contractedTraceBianchiCovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have hscalar_eval :
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) scalarTrace x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    calc
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i j k l := by
            unfold scalarHessianFromNabla2RicInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i j k l]
      _ =
        extDerivFun (I := I) scalarTrace x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
            dsimp [scalarTrace, Γj] at hscalar_cov ⊢
            exact hscalar_cov.symm
  have htraceA_eval :
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) traceA x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) := by
    calc
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i k j l := by
            unfold contractedNabla2RicTraceAInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i k j l]
      _ =
        extDerivFun (I := I) traceA x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) := by
            dsimp [traceA, Γj] at htraceA_cov ⊢
            exact htraceA_cov.symm
  have htraceB_eval :
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) traceB x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) := by
    calc
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i l k j := by
            unfold contractedNabla2RicTraceBInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i l k j]
      _ =
        extDerivFun (I := I) traceB x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) := by
            dsimp [traceB, Γj] at htraceB_cov ⊢
            exact htraceB_cov.symm
  have hA_event :
      traceA =ᶠ[nhds x] (fun y : M => (1 / 2 : Real) * scalarTrace y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact (hbianchi t y hy j).1
  have hB_event :
      traceB =ᶠ[nhds x] (fun y : M => (1 / 2 : Real) * scalarTrace y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact (hbianchi t y hy j).2
  have hA_deriv :=
    ricci_extDerivFun_congr_eventually (I := I) (x := x)
      (v := frame i x) hA_event
  have hB_deriv :=
    ricci_extDerivFun_congr_eventually (I := I) (x := x)
      (v := frame i x) hB_event
  have hA_corr :
      (∑ a : Idx, Γj a *
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) =
        ∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hbianchi t x hx a).1]
  have hB_corr :
      (∑ a : Idx, Γj a *
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) =
        ∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hbianchi t x hx a).2]
  have hA :
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by
    rw [htraceA_eval, hscalar_eval]
    rw [hA_deriv, hA_corr, hhalf_deriv]
    have hsum_scale :
        (∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l))) =
          (1 / 2 : Real) *
            (∑ a : Idx, Γj a *
              (∑ k : Idx, ∑ l : Idx,
                gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsum_scale]
    ring
  have hB :
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by
    rw [htraceB_eval, hscalar_eval]
    rw [hB_deriv, hB_corr, hhalf_deriv]
    have hsum_scale :
        (∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l))) =
          (1 / 2 : Real) *
            (∑ a : Idx, Γj a *
              (∑ k : Idx, ∑ l : Idx,
                gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsum_scale]
    ring
  exact ⟨hA, hB⟩

/-- The raw Ricci-identity commutator step before differentiated contracted
Bianchi replaces the traced terms by half the scalar Hessian. -/
def RicciSecondDerivativeCommutatorsInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j

/-- Curvature commutator part of Lemma 6.3, separated from the differentiated
contracted-Bianchi trace cancellation. -/
def RicciCurvatureCommutatorsInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j

/-- Differentiated contracted Bianchi upgrades the raw Ricci-identity
commutator step to the exact curvature commutator identities used in
Lemma 6.3. -/
theorem RicciCurvatureCommutatorsInFrame_of_differentiatedBianchi_and_secondCommutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hsecond : RicciSecondDerivativeCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciCurvatureCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hsecond t x i j).1
  have hright := (hsecond t x i j).2
  have hA := (hbianchi t x i j).1
  have hB := contractedNabla2RicTraceRightNatural_eq_traceB
    (M := M) gInv nabla2Ric hbianchi hHessSymm t x i j
  have hB' := (hbianchi t x i j).2
  constructor
  · rw [hleft, hA]
  · rw [hright, hB, hB']

/-- Curvature action on a two-tensor, expanded into the two affected slots.
This keeps the Ricci-evolution contraction proof from unfolding the general
slot-sum definition repeatedly. -/
private theorem curvatureAction0SAt_vec2_eq
    (Rm13 : Realized.Tensor13Section (I := I) (M := M))
    {x : M}
    (Ric : Realized.Tensor02At (I := I) (M := M) x)
    (X Y U V : TangentSpace I x) :
    Realized.curvatureAction0SAt (I := I) Rm13 Ric X Y
        (Realized.vec2 U V) =
      - (Rm13 x
            (Realized.oneFormAtSlot0S (I := I) Ric (Realized.vec2 U V) 0)
            (Realized.vec3 X Y U) +
          Rm13 x
            (Realized.oneFormAtSlot0S (I := I) Ric (Realized.vec2 U V) 1)
            (Realized.vec3 X Y V)) := by
  rw [Realized.curvatureAction0SAt]
  simp [Fin.sum_univ_two, Realized.vec2, RicciFlower.Curvature.vec2]

/-- Contract the first curvature-action identity obtained from the `(0,2)`
Ricci identity.  This is the convention-correct finite-index curvature algebra
`R_ikjl Ric^kl + Ric_i^k Ric_kj` for `Rm04(W,X,Y,Z)=g(W,R(X,Y)Z)`. -/
private theorem contractedCurvatureAction_left_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) g x basis gInvAt)
    (t : Real) (i j : Idx)
    (hLower : Realized.Rm04LowersRm13At (I := I) g x (Rm13 t x) (Rm04 t x))
    (hTraceAt : Realized.RicciRealizesRm04FirstTraceAt (I := I)
      (S.ricci t x) (Rm04 t x) gInvAt basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 t x (Realized.vec4 W X Y Z) =
        Rm04 t x (Realized.vec4 Y Z W X))
    (hOutput : Realized.Rm04OutputSkewAt (I := I) (Rm04 t x))
    (hFirst : Realized.FirstBianchiAt (I := I) (Rm04 t x))
    (hRic : forall i j : Idx,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hgInvAt : forall a b : Idx, gInvAt a b = gInv t x a b)
    (hbasis : forall a : Idx, basis a = frame a x) :
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Realized.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame i x)
            (Realized.vec2 (frame j x) (frame l x))) =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  have hRicAt :
      forall a b : Idx,
        (S.ricci t x) (Realized.vec2 (basis a) (basis b)) =
          (S.ricci t x) (Realized.vec2 (basis b) (basis a)) := by
    intro a b
    simpa [hbasis] using hRic a b
  have hInvAt : forall a b : Idx, gInvAt a b = gInvAt b a := by
    exact Tensor0SBundle.invMetric_symm (I := I) (M := M) g x basis gInvAt hinvAt
  have hmain :=
    Realized.contracted_curvatureAction0SAt_vec2_eq
      (I := I) g basis gInvAt hinvAt (Rm13 t) (Rm04 t x) (S.ricci t x)
      hLower hTraceAt hPair hOutput hFirst hRicAt hInvAt i j
  simpa [Realized.rm04RicciContractionAt, Realized.raised02CompAt,
    Realized.ricciQuadraticAt, Realized.oneUp02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame, ricciOneUpCompInFrame,
    ricciQuadraticCompInFrame, Realized.rm04Comp, RicciFlower.Curvature.rm04Comp,
    hgInvAt, hbasis] using hmain

/-- Contract the natural right curvature-action identity obtained from the
`(0,2)` Ricci identity. -/
private theorem contractedCurvatureAction_right_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) g x basis gInvAt)
    (t : Real) (i j : Idx)
    (hLower : Realized.Rm04LowersRm13At (I := I) g x (Rm13 t x) (Rm04 t x))
    (hTraceAt : Realized.RicciRealizesRm04FirstTraceAt (I := I)
      (S.ricci t x) (Rm04 t x) gInvAt basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 t x (Realized.vec4 W X Y Z) =
        Rm04 t x (Realized.vec4 Y Z W X))
    (hOutput : Realized.Rm04OutputSkewAt (I := I) (Rm04 t x))
    (hFirst : Realized.FirstBianchiAt (I := I) (Rm04 t x))
    (hRic : forall i j : Idx,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hgInvAt : forall a b : Idx, gInvAt a b = gInv t x a b)
    (hbasis : forall a : Idx, basis a = frame a x) :
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Realized.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame j x)
            (Realized.vec2 (frame i x) (frame l x))) =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  have hRicAt :
      forall a b : Idx,
        (S.ricci t x) (Realized.vec2 (basis a) (basis b)) =
          (S.ricci t x) (Realized.vec2 (basis b) (basis a)) := by
    intro a b
    simpa [hbasis] using hRic a b
  have hInvAt : forall a b : Idx, gInvAt a b = gInvAt b a := by
    exact Tensor0SBundle.invMetric_symm (I := I) (M := M) g x basis gInvAt hinvAt
  have hmain :=
    Realized.contracted_curvatureAction0SAt_vec2_eq
      (I := I) g basis gInvAt hinvAt (Rm13 t) (Rm04 t x) (S.ricci t x)
      hLower hTraceAt hPair hOutput hFirst hRicAt hInvAt j i
  have hsym :=
    Realized.curvature_ricci_rhs_symm
      (I := I) basis (Rm04 t x) gInvAt (S.ricci t x)
      hPair hRicAt hInvAt j i
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Realized.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame j x)
            (Realized.vec2 (frame i x) (frame l x)))
        =
          Realized.rm04RicciContractionAt (I := I) basis (Rm04 t x) gInvAt
              (S.ricci t x) j i +
            Realized.ricciQuadraticAt (I := I) basis gInvAt
              (S.ricci t x) j i := by
          simpa [hgInvAt, hbasis] using hmain
    _ =
          Realized.rm04RicciContractionAt (I := I) basis (Rm04 t x) gInvAt
              (S.ricci t x) i j +
            Realized.ricciQuadraticAt (I := I) basis gInvAt
              (S.ricci t x) i j := hsym
    _ =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
          simp [Realized.rm04RicciContractionAt, Realized.raised02CompAt,
            Realized.ricciQuadraticAt, Realized.oneUp02CompAt,
            rmRicciContractionCompInFrame, raisedRicciCompInFrame, ricciOneUpCompInFrame,
            ricciQuadraticCompInFrame, Realized.rm04Comp, RicciFlower.Curvature.rm04Comp,
            hgInvAt, hbasis]

/-- Produce the raw second-derivative commutator identities from the invariant
`(0,2)` tensor Ricci identity.  The curvature-action contraction is the only
nontrivial finite-index algebra left here: it converts the two slot actions on
`Ric` into `R_ikjl Ric^kl + Ric_i^k Ric_kj` in the project curvature convention. -/
theorem ricciSecondDerivativeCommutatorsInFrame_of_tensor0S_ricciIdentity
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (nabla2RicTensor : Real -> Realized.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hPair : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W X Y Z) =
          Rm04 (t : Real) x (Realized.vec4 Y Z W X))
    (hOutput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    :
    RicciSecondDerivativeCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  classical
  intro t x i j
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt (hcover x))
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv (t : Real) (hcover x)
  have hTraceReg :
      RicciTensorRealizesRm04FirstTraceInFrameOnRegular
        (I := I) S Rm04 gInv frame :=
    ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
      (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv hRicTrace13 hLower
  have hTraceFrame := hTraceReg t
  have hTraceAt :
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (fun a b : Idx => gInv (t : Real) x a b)
        (hframe.toBasisAt (hcover x)) := by
    intro a b
    have h := hTraceFrame x a b
    simpa [Realized.RicciTensorRealizesRm04FirstTraceInFrame,
      IsLocalFrameOn.toBasisAt_coe] using h
  have hIdComp :
      forall k l : Idx,
        nabla2Ric (t : Real) x k i j l -
            nabla2Ric (t : Real) x i k j l =
          Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame i x)
            (Realized.vec2 (frame j x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame i x)
      (Realized.vec2 (frame j x) (frame l x))
    have hinput₁ :
        Realized.metricTraceInput (I := I) (frame k x) (frame i x)
            (Realized.vec2 (frame j x) (frame l x)) =
          Realized.vec4 (frame k x) (frame i x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        Realized.metricTraceInput (I := I) (frame i x) (frame k x)
            (Realized.vec2 (frame j x) (frame l x)) =
          Realized.vec4 (frame i x) (frame k x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x k i j l, hNabla2 (t : Real) x i k j l]
    simpa [Realized.rm04Comp, RicciFlower.Curvature.rm04Comp] using h
  have hIdCompRight :
      forall k l : Idx,
        nabla2Ric (t : Real) x k j i l -
            nabla2Ric (t : Real) x j k i l =
          Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame j x)
            (Realized.vec2 (frame i x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame j x)
      (Realized.vec2 (frame i x) (frame l x))
    have hinput₁ :
        Realized.metricTraceInput (I := I) (frame k x) (frame j x)
            (Realized.vec2 (frame i x) (frame l x)) =
          Realized.vec4 (frame k x) (frame j x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        Realized.metricTraceInput (I := I) (frame j x) (frame k x)
            (Realized.vec2 (frame i x) (frame l x)) =
          Realized.vec4 (frame j x) (frame k x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x k j i l, hNabla2 (t : Real) x j k i l]
    simpa [Realized.rm04Comp, RicciFlower.Curvature.rm04Comp] using h
  have hleftCurv :
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (Realized.vec2 (frame j x) (frame l x))) := by
    unfold contractedNabla2RicLeftInFrame contractedNabla2RicTraceAInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k i j l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x i k j l +
              Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (Realized.vec2 (frame j x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdComp k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x i k j l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (Realized.vec2 (frame j x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hrightCurvNatural :
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (Realized.vec2 (frame i x) (frame l x))) := by
    unfold contractedNabla2RicRightInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k j i l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x j k i l +
              Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (Realized.vec2 (frame i x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdCompRight k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (Realized.vec2 (frame i x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hgInvAt :
      forall a b : Idx,
        (fun a b : Idx => gInv (t : Real) x a b) a b =
          gInv (t : Real) x a b := by
    intro a b
    rfl
  have hbasis :
      forall a : Idx,
        hframe.toBasisAt (hcover x) a =
          frame a x := by
    intro a
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hleftAction :=
    contractedCurvatureAction_left_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt (hcover x))
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x)
      hgInvAt hbasis
  have hrightAction :=
    contractedCurvatureAction_right_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt (hcover x))
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x)
      hgInvAt hbasis
  constructor
  · calc
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (Realized.vec2 (frame j x) (frame l x))) := hleftCurv
      _ =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hleftAction]
            ring
  · calc
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            Realized.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (Realized.vec2 (frame i x) (frame l x))) := hrightCurvNatural
      _ =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hrightAction]
            ring

/-- The two contracted commutator identities used in Lemma 6.3:
both second-derivative contractions equal
`1/2 Hess R + R_ikjl Ric^kl + Ric_i^k Ric_kj`, and the two divergence trace
terms in `∇_i A^k_kj` cancel for a symmetric Ricci tensor. -/
def RicciContractedCommutatorsInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j

theorem ricci_trace_terms_eq_of_differentiatedBianchi
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x i j).1
  have hB := (hbianchi t x i j).2
  rw [hA, hB]

theorem RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hcurv : RicciCurvatureCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  exact ⟨(hcurv t x i j).1, (hcurv t x i j).2,
    ricci_trace_terms_eq_of_differentiatedBianchi
      (M := M) gInv nabla2Ric hbianchi t x i j⟩

/-- Lemma 6.3 contracted commutator producer from differentiated contracted
Bianchi plus the invariant `(0,2)` Ricci identity. -/
theorem RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_tensor0S_ricciIdentity
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (nabla2RicTensor : Real -> Realized.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hPair : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (Realized.vec4 W X Y Z) =
          Rm04 (t : Real) x (Realized.vec4 Y Z W X))
    (hOutput : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric :=
  RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_commutators
    (I := I) S Rm04 gInv frame nabla2Ric hbianchi
    (RicciCurvatureCommutatorsInFrame_of_differentiatedBianchi_and_secondCommutators
      (I := I) S Rm04 gInv frame nabla2Ric hbianchi hHessSymm
      (ricciSecondDerivativeCommutatorsInFrame_of_tensor0S_ricciIdentity
        (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv
        nabla2RicTensor nabla2Ric
        hNabla2 hRicciId hRicTrace13 hLower hPair hOutput hFirst hRic))

/-- Contracted commutator producer with Rm04 and Ricci symmetries produced from
regular Levi-Civita curvature data. -/
theorem RicciContractedCommutatorsInFrame_of_tensor0S_ricciIdentity_lc
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (nabla2RicTensor : Real -> Realized.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  have hOutput :=
    rm04OutputSkew_regular (I := I) S hS Rm13 Rm04 hcov hRm13 hLower
  have hFirst :=
    rm04FirstBianchi_regular (I := I) S hS Rm13 Rm04 hcov hRm13 hLower
  have hPair :=
    rm04PairSymm_regular (I := I) S hS Rm13 Rm04 hcov hRm13 hLower
  have hInput :=
    rm04InputSkew_regular (I := I) S Rm13 Rm04 hRm13 hLower
  have hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)) := by
    have hTraceReg :
      RicciTensorRealizesRm04FirstTraceInFrameOnRegular
        (I := I) S Rm04 gInv frame :=
    ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
        (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv hRicTrace13 hLower
    intro t x
    intro i j
    have h := hTraceReg t x i j
    simpa [Realized.RicciTensorRealizesRm04FirstTraceInFrame,
      IsLocalFrameOn.toBasisAt_coe] using h
  have hRic : RicciSymmetricInFrameOnRegular (I := I) S frame :=
    ricciSymm_regular (I := I) S Rm04 gInv frame hframe
      hcover hinv
      hTrace hPair hOutput hInput
  exact
    RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_tensor0S_ricciIdentity
      (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv nabla2RicTensor nabla2Ric
      hbianchi hHessSymm hNabla2 hRicciId hRicTrace13 hLower
      hPair hOutput hFirst hRic

private theorem ricciVariationExpandedRHSInFrame_eq_decomposed
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j =
      roughLapRicInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j +
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j +
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j := by
  let left : Real :=
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j
  let right : Real :=
    contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j
  let rough : Real :=
    roughLapRicInFrame (M := M) gInv nabla2Ric t x i j
  let hess : Real :=
    scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j
  let traceA : Real :=
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j
  let traceB : Real :=
    contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j
  have hfirst :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j)) =
        -left - right + rough := by
    dsimp [left, right, rough, contractedNabla2RicLeftInFrame,
      contractedNabla2RicRightInFrame, roughLapRicInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x k i j l) -
            gInv t x k l * nabla2Ric t x k j i l +
            gInv t x k l * nabla2Ric t x k l i j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k i j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k j i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k l i j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  have hsecond :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j)) =
        -traceA - hess + traceB := by
    dsimp [hess, traceA, traceB, scalarHessianFromNabla2RicInFrame,
      contractedNabla2RicTraceAInFrame, contractedNabla2RicTraceBInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x i k j l) -
            gInv t x k l * nabla2Ric t x i j k l +
            gInv t x k l * nabla2Ric t x i l k j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i k j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i j k l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i l k j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  unfold ricciVariationExpandedRHSInFrame
  rw [hfirst, hsecond]
  dsimp [left, right, rough, hess, traceA, traceB]
  ring

/-- The Lemma 6.3 expanded Ricci-variation RHS reduces to the Hamilton RHS
once the contracted commutator identities are supplied. -/
theorem ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hcomm t x i j).1
  have hright := (hcomm t x i j).2.1
  have htrace := (hcomm t x i j).2.2
  rw [ricciVariationExpandedRHSInFrame_eq_decomposed
    (M := M) gInv nabla2Ric (t : Real) x i j]
  rw [hleft, hright, htrace]
  simp [ricciEvolutionRHSInFrame]
  ring

/-- Contracted second Bianchi in fixed-frame components:
`∇^k Ric_ik = (1/2) ∇_i R`. -/
def contractedBianchiInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gradScalar : Real -> M -> Idx -> Real) : Prop :=
  forall t x i,
    (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l i k) =
      (1 / 2 : Real) * gradScalar t x i

/-- Commutator step for the second derivatives appearing after substituting
the Ricci-flow Christoffel variation into the Ricci variation formula. -/
def ricciSecondDerivativeCommute
    (secondDerivRic commutedSecondDerivRic :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x a b i j,
    secondDerivRic t x a b i j = commutedSecondDerivRic t x a b i j

/-- Gauge cancellation after contracted Bianchi:
the Hessian/scalar-divergence terms in the Ricci variation formula cancel. -/
def ricciVariationGaugeTerms_cancel
    (gaugeTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j, gaugeTerms t x i j = 0

/-- Curvature commutator reduction in Lemma 6.3:
the remaining commutator terms are exactly
`-2 * rmRicciContractionCompInFrame - 2 Ric_i^k Ric_kj` in the project
lowered-curvature convention. -/
def ricciCurvatureTerms_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (curvatureTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j,
    curvatureTerms t x i j =
      2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

/-- Lemma 6.3 producer from the Ricci variation formula after substituting the
Ricci-flow Christoffel variation.  The remaining hypothesis is the precise
contracted-Bianchi plus commutator reduction. -/
theorem ricciEvolutionEquationInFrame_of_variation_expanded
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x i j
  exact (h_var t x i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))

/-- Local Lemma 6.3 producer from the local Ricci variation formula after
substituting the Ricci-flow Christoffel variation. -/
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x hx i j
  exact (h_var t x hx i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))

/-- Lemma 6.3 producer from the Ricci variation formula and the two contracted
commutator identities in the textbook proof. -/
theorem ricciEvolution_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrame_of_variation_expanded
    (I := I) S Rm04 gInv frame nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hcomm)

/-- Local Lemma 6.3 producer from the local Ricci variation formula and the
contracted commutator identities in the textbook proof. -/
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    (I := I) S Rm04 gInv frame u nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hcomm)

section CoordinateFrameRicciEvolution

open RicciFlower.Coordinates

/-- Local coordinate-frame Lemma 6.3 producer.

This is the current closed coordinate version of Lemma 6.3: it differentiates
the Christoffel Ricci trace formula, substitutes the Ricci-flow Christoffel
variation and `nabla A = nabla^2 Ric`, then applies the contracted commutator
reduction.  The result is local at the coordinate center because the coordinate
frame is only a local frame. -/
theorem ricciEvolutionEquationInCoordFrameAt_of_christoffelEvolution_nabla2_commutators
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      Realized.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal (I := I) S Rm04 gInv
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
    nabla2Ric
    (ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2
      (I := I) S hS gInv gInvDt nablaRic nabla2Ric Rm13 x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix)
    hcomm

/-- LaTeX Lemma 6.3, `lem:evol-ricci`, in the local coordinate-frame display
form at a coordinate center. -/
theorem evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      Realized.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x₀ i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  have h :=
    ricciEvolutionEquationInCoordFrameAt_of_christoffelEvolution_nabla2_commutators
      (I := I) S hS Rm13 Rm04 gInv gInvDt nablaRic nabla2Ric x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix hcomm
  have hAt := h t x₀ (by simp) i j
  simpa [ricciEvolutionRHSInFrame] using hAt

end CoordinateFrameRicciEvolution

/-- LaTeX Lemma 6.3, `lem:evol-ricci`, in fixed-frame component display form,
assuming the Ricci variation formula and the contracted commutator reduction. -/
theorem evol_ricci_inFrame_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have h :=
    ricciEvolutionEquationInFrame_apply
      (I := I)
      (h :=
        ricciEvolution_of_variation_commutators
          (I := I) S Rm04 gInv frame nabla2Ric h_var hcomm)
      t x i j
  simpa [ricciEvolutionRHSInFrame] using h

/-- Product-rule derivative of the Ricci trace
`Ric_ij = g^{kl} Rm04_kijl`. -/
def ricciTraceDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x k l *
      Realized.rm04Comp (I := I) (Rm04 t) frame x k i j l +
    gInv t x k l * rm04Dt t x k i j l)

/-- The finite trace simplification that turns traced Riemann evolution into
Lemma 6.3's Ricci RHS.  This is the realized counterpart of the synthetic
`RicciFromRiemann.lean` trace algebra. -/
def RicciTraceDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j

/-- Trace a supplied lowered-Riemann evolution equation to the Ricci evolution
equation in the existing Section 6.2 component API. -/
theorem ricciEvolutionEquationInFrame_of_riemann_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_trace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (h_rm : RiemannEvolutionEquationInFrameOn (I := I) (D := D) Rm04 frame rm04Dt)
    (h_simplify : RicciTraceDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapRic) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  let traceComp : Real -> Real :=
    fun s => ∑ k : Idx, ∑ l : Idx,
      gInv s x k l *
        Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l
  have htraceDeriv :
      HasDerivWithinAt traceComp
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    dsimp [traceComp, ricciTraceDerivRHSInFrame]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s =>
          ∑ l : Idx,
            gInv s x k l *
              Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l)
        (A' := fun k =>
          ∑ l : Idx,
            (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x k l *
              Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
            gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l))
        (s := D.carrier) (x := (t : Real))
        (fun k _hk =>
          by
            simpa [Finset.sum_apply] using
              (HasDerivWithinAt.fun_sum
                (u := (Finset.univ : Finset Idx))
                (A := fun l s =>
                  gInv s x k l *
                    Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l)
                (A' := fun l =>
                  inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x k l *
                    Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
                  gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l)
                (s := D.carrier) (x := (t : Real))
                (fun l _hl =>
                  by
                    exact (h_inv t x k l).mul (h_rm t x k i j l)))))
  have hricci :
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    refine htraceDeriv.congr ?_ ?_
    · intro s _hs
      exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace s x i j
    · exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace (t : Real) x i j
  exact hricci.congr_deriv (h_simplify t x i j)

/-! ## Corollary 6.5: Lichnerowicz form -/

/-- Raise the second index of a fixed-frame `(0,2)` tensor component family. -/
def tensorOneUpCompInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * h t x i a

/-- Left Ricci action on a `(0,2)` tensor: `Ric_i^k h_kj`. -/
def ricciLeftActionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      h t x k j

/-- Right Ricci action on a `(0,2)` tensor: `Ric_j^k h_ki`. -/
def ricciRightActionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x j k *
      h t x k i

/-- Ricci-specialized Lichnerowicz RHS in fixed-frame components:
`Delta h_ij - 2 * curvature-action contraction - Ric_i^k h_kj - Ric_j^k h_ki`.

For Corollary 6.5, `h` is the Ricci tensor. -/
-- Convention note: this uses the same curvature-action contraction sign as
-- `ricciEvolutionRHSInFrame`.
def lichnerowiczRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapH h hRaised : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapH t x i j -
    2 * (∑ k : Idx, ∑ l : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        hRaised t x k l) -
    ricciLeftActionCompInFrame (I := I) S gInv frame h t x i j -
    ricciRightActionCompInFrame (I := I) S gInv frame h t x i j

/-- Component equation `∂t Ric = Δ_L Ric`. -/
def RicciLichnerowiczEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- The finite component specialization of the Lichnerowicz RHS to `h = Ric`.
For a realized Levi-Civita Ricci tensor this follows from Ricci symmetry and
the frame inverse-metric identities, whose symmetry consequence is now proved
in the metric layer. -/
def RicciLichnerowiczSpecializesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j

/-- Fixed-frame symmetry of the Ricci tensor. -/
def RicciSymmetricInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    ricciCompInFrame (I := I) S frame t x i j =
      ricciCompInFrame (I := I) S frame t x j i

/-- The left Ricci action on `Ric` is definitionally the quadratic term from
Lemma 6.3. -/
theorem ricciLeftActionCompInFrame_eq_quadratic
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciLeftActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- The right Ricci action on `Ric` is the same quadratic term, using Ricci
symmetry and the frame inverse-metric identities. -/
theorem ricciRightActionCompInFrame_eq_quadratic_of_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) (x : M) (i j : Idx) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  have hInv : SymmetricInverseMetricComponentsInFrameOn gInv :=
    gInv_symm (I := I) S gInv frame hinv
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic t x j a, hRic t x k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv t x k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl

/-- Pointwise version of
`ricciRightActionCompInFrame_eq_quadratic_of_symm`. -/
theorem ricciRightActionCompInFrame_eq_quadratic_at
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real) (x : M) (i j : Idx)
    (hRic : forall a b : Idx,
      ricciCompInFrame (I := I) S frame t x a b =
        ricciCompInFrame (I := I) S frame t x b a) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  have hInv : SymmetricInverseMetricComponentsInFrameOn gInv :=
    gInv_symm (I := I) S gInv frame hinv
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic j a, hRic k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv t x k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl

/-- Constructor for the Lichnerowicz specialization from the two Ricci-action
identities `Ric_i^k Ric_kj = Ric_i^k Ric_kj` and
`Ric_j^k Ric_ki = Ric_i^k Ric_kj`. -/
theorem ricciLichnerowiczSpecializesInFrame_of_actions
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_left : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciLeftActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j)
    (h_right : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciRightActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  simp [lichnerowiczRHSInFrame,
    ricciEvolutionRHSInFrame, rmRicciContractionCompInFrame,
    h_left t x i j, h_right t x i j]
  ring

/-- Lichnerowicz specialization for `h = Ric`, produced from Ricci symmetry
and the frame inverse-metric identities. -/
theorem ricciLichnerowiczSpecializesInFrame_of_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczSpecializesInFrame_of_actions
    (I := I) S Rm04 gInv frame roughLapRic
    (fun t x i j =>
      ricciLeftActionCompInFrame_eq_quadratic
        (I := I) S gInv frame (t : Real) x i j)
    (fun t x i j =>
      ricciRightActionCompInFrame_eq_quadratic_of_symm
        (I := I) S gInv frame hRic hinv (t : Real) x i j)

/-- Regular-time version of `ricciLichnerowiczSpecializesInFrame_of_symm`.
This is the application-facing shape for Ricci-flow equations, where the
evolution identity is only asserted at regular flow times. -/
theorem ricciLichnerowiczSpecializesInFrame_regular
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  refine ricciLichnerowiczSpecializesInFrame_of_actions
    (I := I) S Rm04 gInv frame roughLapRic ?_ ?_
  · intro t x i j
    exact ricciLeftActionCompInFrame_eq_quadratic
      (I := I) S gInv frame (t : Real) x i j
  · intro t x i j
    exact ricciRightActionCompInFrame_eq_quadratic_at
      (I := I) S gInv frame hinv (t : Real) x i j (hRic t x)

/-- Lichnerowicz specialization with the Ricci symmetry produced from
Levi-Civita curvature data. -/
theorem ricciLichnerowiczSpecializesInFrame_lc
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  have hOutput :=
    rm04OutputSkew_regular (I := I) S hS Rm13 Rm04 hcov hRm13 hLower
  have hPair :=
    rm04PairSymm_regular (I := I) S hS Rm13 Rm04 hcov hRm13 hLower
  have hInput :=
    rm04InputSkew_regular (I := I) S Rm13 Rm04 hRm13 hLower
  have hRic : RicciSymmetricInFrameOnRegular (I := I) S frame :=
    ricciSymm_regular (I := I) S Rm04 gInv frame hframe
      hcover hinv
      hTrace hPair hOutput hInput
  exact ricciLichnerowiczSpecializesInFrame_regular
    (I := I) S Rm04 gInv frame roughLapRic hRic hinv

/-- Corollary 6.5: Lemma 6.3 implies the Ricci tensor evolves by the
Lichnerowicz heat equation. -/
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_spec : RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  exact (h_ricci t x i j).congr_deriv (h_spec t x i j).symm

/-- Corollary 6.5 with the standard inputs: Lemma 6.3 plus Ricci symmetry and
the frame inverse-metric identities imply the Ricci-specialized
Lichnerowicz heat equation. -/
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczEquationInFrame_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic h_ricci
    (ricciLichnerowiczSpecializesInFrame_of_symm
      (I := I) S Rm04 gInv frame roughLapRic hRic hinv)

/-- Corollary 6.5 with Ricci symmetry produced from Levi-Civita curvature
data instead of supplied as an application-layer hypothesis. -/
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution_lc
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hcov : ConnectionLocallySmoothOn (I := I) S)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hRm13 : forall t : Realized.RealTimeInterval.RegularTime D,
      Realized.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      Realized.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczEquationInFrame_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic h_ricci
    (ricciLichnerowiczSpecializesInFrame_lc
      (I := I) S hS Rm13 Rm04 gInv frame roughLapRic hcov hframe hcover
      hTrace hRm13 hLower hinv)

/-- Corollary 6.5 in the coordinate-frame display form used by the native
Lemma 6.3 producer.  This is only an exposure wrapper: the Ricci evolution
calculation comes from `evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators`,
and the Lichnerowicz rewrite comes from
`ricciLichnerowiczSpecializesInFrame_of_symm`. -/
theorem evol_ricci_lichnerowicz_coordFrameAt_of_christoffelEvolution_nabla2_commutators
    [IsManifold I (∞ + 1) M]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      Realized.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric)
    (hRic : RicciSymmetricInFrameOn (I := I) S (coordinateFrameAt (I := I) x₀))
    (t : Realized.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
        (raisedRicciCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀))
        (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  have hRicci :=
    evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators
      (I := I) S hS Rm13 Rm04 gInv gInvDt nablaRic nabla2Ric x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix hcomm t i j
  have hSpec :
      RicciLichnerowiczSpecializesInFrame
        (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
        (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
    ricciLichnerowiczSpecializesInFrame_of_symm
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
      (roughLapRicInFrame (M := M) gInv nabla2Ric) hRic hmetricReg.nondegenerateGram
  exact hRicci.congr_deriv (hSpec t x₀ i j).symm

end Components

end RicciFlow
end RicciFlower
