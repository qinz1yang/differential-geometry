import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.ProperAction.Basic
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.ImprovedPinching
import RicciFlower.RicciFlow.Evolution.LocalPinching
import RicciFlower.RicciFlow.Evolution.RicciPreservation
import RicciFlower.RicciFlow.Evolution.ScalarFiniteTime
import RicciFlower.MaximumPrinciple.ScalarStrong
import RicciFlower.RicciFlow.MaximalTime
import RicciFlower.RicciFlow.Perelman.Noncollapsing
import RicciFlower.DimensionThree.RicciControlsRm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Positive Ricci Endpoint

This file states the global endpoint of Hamilton's three-dimensional positive
Ricci theorem in RicciFlower's current structures.

The policy here is deliberate: local tensor algebra, curvature identities,
evolution equations, maximum-principle cores, and dimension-three algebra stay
in their native RicciFlower files.  The theorem-shaped `sorry`s below are only
for the remaining global analytic or topological inputs in Hamilton's Section
12 completion: maximal-flow existence, point selection and rescaling,
noncollapsing, compactness, limit extraction, and spherical space-form
classification.
-/

noncomputable section

universe u

namespace RicciFlower
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Closed, connected, smooth, boundaryless, three-dimensional manifold
package used by the statement of Hamilton's theorem. -/
def Closed3Manifold : Prop :=
  CompactSpace M /\ ConnectedSpace M /\ I.Boundaryless /\
    Module.finrank Real E = 3

/-- The initial metric has positive Ricci curvature, expressed through the
canonical pointwise Ricci tensor of the metric. -/
def PosRicciMetric (g : SmoothRiemannianMetric I M) : Prop :=
  forall x : M, forall v : TangentSpace I x, v ≠ 0 ->
    0 < RicciFlow.metricRicciAt (I := I) (M := M) g x
      (Curvature.vec2 (I := I) v v)

/-- `M` admits a smooth Riemannian metric of positive Ricci curvature. -/
def AdmitsPosRicci : Prop :=
  exists g : SmoothRiemannianMetric I M, PosRicciMetric (I := I) (M := M) g

/-- Constant positive sectional curvature, expressed in the standard lowered
curvature slot order `Rm04(X,Y,Z,W) = <R(X,Y)Z,W>`.

The sectional numerator is `Rm04(X,Y,Y,X)`. -/
def ConstPosSecMetric (g : SmoothRiemannianMetric I M) : Prop :=
  exists c : Real, 0 < c /\
    forall x : M, forall X Y : TangentSpace I x,
      Curvature.metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)

/-- `M` admits a smooth metric of constant positive sectional curvature. -/
def AdmitsConstPosSec : Prop :=
  exists g : SmoothRiemannianMetric I M, ConstPosSecMetric (I := I) (M := M) g

/-- The standard unit three-sphere in Euclidean four-space. -/
abbrev RoundSphere3 : Type :=
  {x : EuclideanSpace Real (Fin 4) // ‖x‖ = (1 : Real)}

/-- Orbit quotient of the round three-sphere by a group action. -/
abbrev SphereOrbitQuotient (Γ : Type*) [Group Γ] [MulAction Γ RoundSphere3] :
    Type :=
  Quotient (MulAction.orbitRel Γ RoundSphere3)

/-- Witness data that a smooth manifold is presented as a spherical space-form
quotient.

This is topology/global-geometry data, not analytic Ricci-flow data:
there is a finite group acting freely by isometries on the round three-sphere,
the orbit quotient carries a smooth structure modeled on `I`, and the supplied
manifold is smoothly homeomorphic to that quotient. -/
structure SphericalSpaceFormQuotientModel
    (I : ModelWithCorners Real E H) (N : Type*)
    [TopologicalSpace N] [ChartedSpace H N] : Type _ where
  Γ : Type
  [group : Group Γ]
  [finiteGroup : Fintype Γ]
  [action : MulAction Γ RoundSphere3]
  action_isometric : forall γ : Γ, Isometry (fun p : RoundSphere3 => γ • p)
  action_free : forall {γ : Γ} {p : RoundSphere3}, γ • p = p -> γ = 1
  [quotientCharted : ChartedSpace H (SphereOrbitQuotient Γ)]
  [quotientSmooth : IsManifold I ∞ (SphereOrbitQuotient Γ)]
  quotientHomeomorph : N ≃ₜ SphereOrbitQuotient Γ
  smooth_toFun : ContMDiff I I ∞ quotientHomeomorph
  smooth_invFun : ContMDiff I I ∞ quotientHomeomorph.symm

/-- Predicate that a smooth manifold is a spherical space-form quotient. -/
def IsSphericalSpaceFormQuotient
    (I : ModelWithCorners Real E H) (N : Type*)
    [TopologicalSpace N] [ChartedSpace H N] : Prop :=
  Nonempty (SphericalSpaceFormQuotientModel I N)

/-- `M` is diffeomorphic to a spherical space form. -/
def SphericalSpaceForm : Prop :=
  IsSphericalSpaceFormQuotient I M

/-- All-real metric family associated to an interval solution and a fallback
initial metric.

On the solution interval it is the solution family; outside it falls back to
`g0` and its Levi-Civita connection.  This is the family used by scalar maximum
principle statements, whose time variable is all of `Real`. -/
def ham3RealFamilyCore
    {D : Realized.RealTimeInterval}
    (S : RicciFlow.SolutionOn (I := I) (M := M) D)
    (g0 : SmoothRiemannianMetric I M) :
    Realized.RealizedMetricFamily (I := I) (M := M) Real where
  metric := fun t => by
    classical
    exact if _ht : t ∈ D.carrier then S.family.metric t else g0
  connection := fun t => by
    classical
    exact
      if _ht : t ∈ D.carrier then S.family.connection t
      else LeviCivita.leviCivitaConnectionOfMetric (I := I) g0
  metricCompatible := by
    intro t
    classical
    by_cases ht : t ∈ D.carrier
    · simpa [ht] using S.family.metricCompatible ⟨t, ht⟩
    · simpa [ht] using
        (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g0)

/-- Current RicciFlower-structured global output of Hamilton's flow argument.

This is the black-box boundary rewritten in current structures: it contains a
folder-level Ricci-flow solution `SolutionOn`, its solution predicate
`IsSolutionOn`, the initial metric relation, and the curvature blow-up property
of the maximal finite-endpoint solution.  Point selection, noncollapsing,
compactness, and the limiting constant-curvature metric are theorem endpoints
below, not fields in this data package. -/
structure Ham3FlowPackage (g0 : SmoothRiemannianMetric I M) where
  D : Realized.RealTimeInterval
  S : RicciFlower.RicciFlow.SolutionOn (I := I) (M := M) D
  isSmooth : RicciFlower.RicciFlow.IsSmoothSolutionOn (I := I) (M := M) S
  startsAt : S.family.metric D.initial = g0
  curvUnbounded : forall K : Real, exists t : Real, exists x : M,
    t ∈ D.carrier /\
      K < Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4
        (S.base.rm04 t x)

/-- Accessor for the Ricci-flow solution carried by the Section 12 package.

Keeping this as a named accessor avoids brittle parsing around the capital field
projection `P.S` inside long component theorem statements. -/
abbrev ham3Solution
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    RicciFlow.SolutionOn (I := I) (M := M) P.D :=
  P.S

/-- Intrinsic scalar curvature carried by the flow package: the metric trace
of the canonical pointwise Ricci tensor. -/
def ham3Scalar
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Real -> M -> Real :=
  RicciFlow.SolutionOn.scalar (I := I) (ham3Solution (I := I) P)

/-- Global maximal-flow setup supplies joint spacetime continuity for the
canonical scalar curvature.

This is a theorem endpoint, not stored data in `Ham3FlowPackage`: proving it
belongs to the smooth Ricci-flow existence/regularity package. -/
theorem ham3_scalarSTCont
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    RicciFlower.RicciFlow.ScalarSTContOn
      (I := I) (M := M) (ham3Solution (I := I) (M := M) P) := by
  exact P.isSmooth.scalarSTCont

/-- Canonical metric-induced squared curvature norm for a Hamilton Section 12
package. -/
def ham3RmNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I)
      ((ham3Solution (I := I) (M := M) P).family.metric t) x 4
      (((ham3Solution (I := I) (M := M) P).base.rm04 t) x)

/-! ## Section 12 blow-up and compactness data -/

/-- Data carried by Hamilton's blow-up sequence in Section 12.

The scale is not stored: in Hamilton's proof it is the scalar curvature of the
original flow at the chosen point-time, `R_i = R(x_i,t_i)`.  Curvature and volume
quantities on the rescaled flows are likewise theorem-level consequences, not
fields of this sequence data. -/
structure Ham3BlowupData (M : Type*) where
  point : Nat -> M
  time : Nat -> Real

/-- Blow-up scale for the `i`th selected parabolic rescaling. -/
def ham3BlowupScale
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (i : Nat) : Real :=
  ham3Scalar (I := I) P (Q.time i) (Q.point i)

/-- Original flow time corresponding to rescaled time `s` in the `i`th blow-up:
`t = t_i + s / R_i`. -/
def ham3RescaledTime
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (i : Nat) (s : Real) : Real :=
  Q.time i + s / ham3BlowupScale (I := I) P Q i

/-- Scalar curvature of the `i`th parabolically rescaled flow. -/
def ham3RescaledScalar
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (i : Nat) (s : Real) (x : M) : Real :=
  (ham3BlowupScale (I := I) P Q i)⁻¹ *
    ham3Scalar (I := I) P (ham3RescaledTime (I := I) P Q i s) x

/-- The fixed radius used in Hamilton's Section 12 proof. -/
def ham3_r0 : Real := (1 : Real) / 10

theorem ham3_r0_pos : 0 < ham3_r0 := by
  norm_num [ham3_r0]

theorem r0_le_one : ham3_r0 ≤ (1 : Real) := by
  norm_num [ham3_r0]

/-- The coarse constant `100` is the inverse-square scale of `r0 = 1/10`. -/
theorem ham3_hundred_eq : (100 : Real) = (ham3_r0⁻¹) ^ 2 := by
  norm_num [ham3_r0]

/-- Data for the pointed smooth limit flow produced by Hamilton compactness.

This is data-only: the Ricci-flow property, subsequence monotonicity, and
time-window coverage are theorem-level predicates below. -/
structure Ham3CGHLimitData (I : ModelWithCorners Real E H) (M : Type u) where
  N : Type u
  [topology : TopologicalSpace N]
  [charted : ChartedSpace H N]
  [smooth : IsManifold I ∞ N]
  [smooth_plus : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
  [sigmaCompact : SigmaCompactSpace N]
  [t2 : T2Space N]
  basepoint : N
  D : Realized.RealTimeInterval
  S : RicciFlow.SolutionOn (I := I) (M := N) D
  subseq : Nat -> Nat

/-- The selected subsequence along which the rescaled pointed flows converge. -/
def Ham3LimitSubseq (L : Ham3CGHLimitData (I := I) M) : Prop :=
  StrictMono L.subseq

/-- The limit flow contains the fixed backward parabolic window used in
Section 12. -/
def Ham3LimitWindow (L : Ham3CGHLimitData (I := I) M) : Prop :=
  Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ L.D.carrier

/-- The limit flow is regular on the open fixed backward parabolic window. -/
def Ham3LimitRegWin (L : Ham3CGHLimitData (I := I) M) : Prop :=
  Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ L.D.regular

/-- The CGH limit remains connected.  This is needed in the final Schur step:
`Ric = (R / 3) g` makes scalar locally constant, while a single global
constant-sectional-curvature parameter requires connectedness. -/
def Ham3LimitConnected (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  ConnectedSpace L.N

/-- The CGH limit remains boundaryless.  This is part of the smooth limit
manifold data needed by static Bianchi/Schur arguments. -/
def Ham3LimitBoundaryless (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  I.Boundaryless

/-- The limit object is itself a smooth Ricci-flow solution. -/
def Ham3LimitFlow (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  RicciFlow.IsSolutionOn (I := I) L.S

/-- Scalar convergence at the pointed basepoints of the selected rescaled
flows.  This is the narrow CGH scalar-transfer datum needed to turn
Hamilton's point-selection normalization into `R(g∞)(x∞,0)=1`. -/
def Ham3LimitBaseScalarConv
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  Filter.Tendsto
    (fun k : Nat =>
      ham3RescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k)))
    Filter.atTop (nhds (L.S.scalar 0 L.basepoint))

/-! ## Section 12 limit-flow proof interfaces -/

/-- Ricci nonnegativity inherited by the CGH limit flow. -/
def LimitRicNonneg (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall t : Real, t ∈ L.D.carrier -> forall x : L.N,
    forall v : TangentSpace I x,
      0 <= L.S.ricciAt t x (Curvature.vec2 (I := I) v v)

/-- Scalar normalization inherited at the CGH base point. -/
def LimitBaseScalarOne (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  L.S.scalar 0 L.basepoint = 1

/-- Positive scalar curvature at one regular limit-flow time. -/
def LimitScalarPosAt (L : Ham3CGHLimitData (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, 0 < L.S.scalar t x

/-- Positive scalar curvature on the noninitial part of the limit flow. -/
def LimitScalarPos (L : Ham3CGHLimitData (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitScalarPosAt (I := I) L t

/-- Nonnegative scalar curvature on the limit-flow carrier. -/
def LimitScalarNonneg (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall t : Real, t ∈ L.D.carrier -> forall x : L.N,
    0 <= L.S.scalar t x

/-- The improved pinching estimate forces the trace-free Ricci norm of the CGH
limit to vanish at one regular time. -/
def LimitTfZeroAt (L : Ham3CGHLimitData (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N,
    RicciFlow.tfRicNormSq L.S.scalar (RicciFlow.ricciNorm (I := I) L.S) t x = 0

/-- The improved pinching estimate forces the trace-free Ricci norm of the CGH
limit to vanish. -/
def LimitTfZero (L : Ham3CGHLimitData (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitTfZeroAt (I := I) L t

/-- The concrete decay conclusion obtained from passing the improved pinching
estimate through the smooth CGH convergence: at every regular limit-flow point,
the trace-free Ricci norm is bounded above by every positive number.

This is deliberately weaker than `LimitTfZero`; the remaining convergence
frontier is to produce this decay statement from pullback convergence of the
rescaled flows and the scale factor `R_i^{-ε} -> 0`. -/
def LimitTfDecayAt (L : Ham3CGHLimitData (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall η : Real, 0 < η ->
    RicciFlow.tfRicNormSq L.S.scalar (RicciFlow.ricciNorm (I := I) L.S) t x <= η

/-- The improved pinching estimate gives arbitrary small upper bounds for the
trace-free Ricci norm on the regular part of the CGH limit. -/
def LimitTfDecay (L : Ham3CGHLimitData (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitTfDecayAt (I := I) L t

/-- At a fixed limit-flow time, the Ricci tensor is Einstein with factor
`R / 3`. -/
def LimitEinsteinAt (L : Ham3CGHLimitData (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall v w : TangentSpace I x,
    L.S.ricciAt t x (Curvature.vec2 (I := I) v w) =
      (L.S.scalar t x / 3) * (L.S.base.metric t).inner x v w

/-- The limit flow carries a constant positive sectional-curvature metric. -/
def LimitConstPosSec (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  exists gInf : SmoothRiemannianMetric I L.N,
    ConstPosSecMetric (I := I) (M := L.N) gInf

/-- Global analytic black box for Hamilton's normalized maximal-flow setup.

This is only the Ricci-flow existence/setup stage: short-time existence,
maximal-time construction, normalization of the initial time to `0`, and the
verified Ricci-flow equation package. -/
theorem ham3_flow_exists_normalized
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
    exists omega : Real, exists h0ω : 0 < omega,
      exists P : Ham3FlowPackage (I := I) (M := M) g0,
        P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω := by
  sorry

/-- Compatibility nonempty form of the normalized maximal-flow setup. -/
theorem ham3_flow_exists
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
    Nonempty (Ham3FlowPackage (I := I) (M := M) g0) := by
  rcases ham3_flow_exists_normalized (I := I) (M := M) hM g0 hpos with
    ⟨_omega, _h0ω, P, _hD⟩
  exact ⟨P⟩

/-- Chosen global Ricci-flow package supplied by `ham3_flow_exists`. -/
noncomputable def ham3_flow_box
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
  Ham3FlowPackage (I := I) (M := M) g0 :=
  Classical.choice (ham3_flow_exists (I := I) (M := M) hM g0 hpos)

/-! ## Corollary 7.4 scalar package extracted from a maximal flow -/

/-- The all-real metric family used by the scalar maximum-principle package.

On the flow interval it is the metric/connection carried by `P`; outside the
interval it falls back to the initial metric and its Levi-Civita connection, so
the realized family has metric compatibility for every real time. -/
def ham3RealFamily
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Realized.RealizedMetricFamily (I := I) (M := M) Real :=
  ham3RealFamilyCore (I := I) P.S g0

/-- Intrinsic squared Ricci norm carried by the flow package. -/
def ham3RicNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (P.S.family.metric t) x 2 (P.S.ricciAt t x)

/-- The scalar Laplacian used by the WMP package, defined through the realized
heat-operator metric family. -/
def ham3ScalarLap
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Realized.laplacianAt (I := I) (ham3RealFamily (I := I) P) t
      (ham3Scalar (I := I) P t) x

/-- Global maximal-flow setup supplies the scalar regularity package required
by the scalar weak maximum principle on every compact subinterval of the
normalized time domain.

This is kept as a theorem endpoint rather than a field of `Ham3FlowPackage`;
the proof belongs to the smooth Ricci-flow regularity layer. -/
theorem ham3_scalarRegular
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (c0 : Real) (K : Real -> NNReal) (T : Real)
    (hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / (3 : Real)) * c0 * t ≠ 0) :
    RicciFlow.ScalarLowerBoundWMPRegularity
      (I := I) (ham3RealFamily (I := I) P) T 3 c0
      (ham3Scalar (I := I) P) (K T) := by
  simpa [ham3Scalar, ham3Solution] using
    (RicciFlow.scalarRegOfSmooth (I := I) (M := M)
      P.S P.isSmooth (ham3RealFamily (I := I) P) T 3 c0 (K T)
      hsubset
      (by
        intro t ht
        have htD : t ∈ P.D.carrier := hsubset t ht
        simp [ham3RealFamily, ham3RealFamilyCore, htD])
      hden)

/-- Scalar curvature is unbounded above on the maximal flow interval.

This is the honest input for Lemma 11.6 point selection.  It is produced from
maximal-endpoint curvature blow-up plus Section 9 Ricci nonnegativity and
Corollary 11.4; finite endpoint alone is not enough. -/
def Ham3ScalarBlowup
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) : Prop :=
  forall A : Real, exists t : Real, exists x : M,
    t ∈ P.D.carrier /\ A < ham3Scalar (I := I) P t x

/-- Point-selection and parabolic-rescaling normalization:
`R_i > 0`, `R_i t_i -> infinity`,
`R(g^{R_i})(x_i,0) = 1`, and scalar curvature is bounded above by `1`
on the rescaled backward time slab. -/
def Ham3PointSel
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) : Prop :=
  (forall i : Nat, 0 < ham3BlowupScale (I := I) P Q i) /\
    (forall i : Nat, 0 < Q.time i) /\
    (forall i : Nat, Q.time i ∈ P.D.carrier) /\
    (forall A : Real, exists N : Nat,
      forall i : Nat, N <= i ->
        A <= ham3BlowupScale (I := I) P Q i * Q.time i) /\
    (forall i : Nat, ham3RescaledScalar (I := I) P Q i 0 (Q.point i) = 1) /\
    (forall (i : Nat) (s : Real) (x : M),
      -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
        ham3RescaledScalar (I := I) P Q i s x <= 1)

/-- Lemma 9.1-style nonnegative Ricci on the selected rescaled flow slabs.

Since constant parabolic metric scaling preserves the `(0,2)` Ricci tensor, this
is stated on the original flow at the original time corresponding to the
rescaled slab point. -/
def Ham3RescaledRicNonneg
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) : Prop :=
  forall (i : Nat) (s : Real) (x : M) (v : TangentSpace I x),
    -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
      0 <= P.S.ricciAt (ham3RescaledTime (I := I) P Q i s) x
        (Curvature.vec2 (I := I) v v)

/-- Section 9 shifted pinching preservation available on every compact
subinterval of the normalized maximal flow. -/
def Ham3Section9Pinch
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) (omega : Real) : Prop :=
  forall T : Real, 0 <= T -> T < omega ->
    exists delta : Real,
      0 < delta /\ delta < (1 : Real) / 3 /\
        RicciFlow.PinchPres (I := I) (M := M)
          (fun t : Real => P.S.base.metric t)
          (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
          P.S.scalar T delta

/-- Section 9 shifted pinching preservation with one fixed pinching constant
valid on every compact subinterval of the maximal flow. -/
def Ham3Section9PinchFixed
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) (omega : Real) : Prop :=
  exists delta : Real,
    0 < delta /\ delta < (1 : Real) / 3 /\
      forall T : Real, 0 <= T -> T < omega ->
        RicciFlow.PinchPres (I := I) (M := M)
          (fun t : Real => P.S.base.metric t)
          (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
          P.S.scalar T delta

theorem Ham3Section9PinchFixed.toVarying
    {g0 : SmoothRiemannianMetric I M}
    {P : Ham3FlowPackage (I := I) (M := M) g0} {omega : Real}
    (h : Ham3Section9PinchFixed (I := I) P omega) :
    Ham3Section9Pinch (I := I) P omega := by
  rcases h with ⟨delta, hdelta0, hdelta13, hpres⟩
  intro T hT hTω
  exact ⟨delta, hdelta0, hdelta13, hpres T hT hTω⟩

/-- Section 9 Ricci nonnegativity preservation on every compact subinterval of
the normalized maximal flow. -/
def Ham3Section9RicNonneg
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) (omega : Real) : Prop :=
  forall T : Real, 0 <= T -> T < omega ->
    Realized.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      (Set.Icc 0 T)

/-- The CGH transfer datum saying that nonnegative Ricci on the selected
rescaled slabs passes to the smooth limit. -/
def Ham3RicNonnegTransfer
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (L : Ham3CGHLimitData (I := I) M) : Prop :=
  Ham3RescaledRicNonneg (I := I) P Q ->
    LimitRicNonneg (I := I) L

/-- Native Section 10 pinching estimate for the canonical fields of the chosen
Hamilton flow.  This is the domain-aware estimate on the maximal-flow carrier,
before the all-real display extension forgets which fields are canonical. -/
def Ham3PinchEstimate
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) : Prop :=
  exists epsilon C : Real,
    0 < epsilon /\ epsilon < 1 /\ 0 <= C /\
      RicciFlow.PinchEstimateOn (M := M)
        (RicciFlow.tfRicNormSq P.S.scalar (RicciFlow.ricciNorm (I := I) P.S))
        P.S.scalar
        (RicciFlow.pinchWeight (M := M) P.S.scalar epsilon)
        C P.D.carrier

/-- The CGH transfer datum needed by the Section 12 pinching paragraph:
smooth convergence of the selected rescalings, combined with the original
Section 10 estimate and scalar positivity on the limit, gives arbitrary-small
upper bounds for the limit trace-free Ricci norm. -/
def Ham3PinchTransfer
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (_Q : Ham3BlowupData M) (L : Ham3CGHLimitData (I := I) M) : Prop :=
  Ham3PinchEstimate (I := I) P ->
    LimitScalarPos (I := I) L ->
      LimitTfDecay (I := I) L

/-- The conclusion of Black box 11.12 in the Hamilton Section 12 pipeline:
after passing to a subsequence, the rescaled pointed flows have a smooth
pointed Cheeger-Gromov-Hamilton limit.

The native project still lacks a full CGH-convergence relation, but the
conclusion now exposes the actual limit data: a pointed smooth Ricci flow on a
limit manifold, defined on the fixed backward window and regular on its open
interior, together with the subsequence selecting the convergent rescalings and
the scalar/pinching transfer data used by the Section 12 argument. -/
def Ham3CGHLimitExists
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) : Prop :=
  exists L : Ham3CGHLimitData (I := I) M,
    Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
      Ham3LimitRegWin (I := I) L /\
      Ham3LimitConnected (I := I) L /\
      Ham3LimitBoundaryless (I := I) L /\
      Ham3LimitFlow (I := I) L /\
      Ham3RicNonnegTransfer (I := I) P Q L /\
      Ham3LimitBaseScalarConv (I := I) P Q L /\
      Ham3PinchTransfer (I := I) P Q L

/-- Eventually the fixed backward time window `[-r0^2,0]` lies inside the
rescaled time slab `[-R_i t_i,0]`. -/
def Ham3Window
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (r : Real) : Prop :=
  exists N : Nat, forall i : Nat, N <= i ->
    forall s : Real, -(r ^ 2) <= s -> s <= 0 ->
      -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s /\ s <= 0

/-- A pair of scale-controlled balls used in the Section 12 noncollapsing
argument: the small `r0` ball and the containing unit ball at the same
point-time. -/
structure Ham3BallPair (M : Type*) where
  small : RicciFlow.Perelman.ScaleControlledBall M
  unit : RicciFlow.Perelman.ScaleControlledBall M
  same_center : unit.center = small.center
  same_time : unit.time = small.time
  unit_radius : unit.radius = 1
  volume_mono : small.volume <= unit.volume

namespace Ham3BallPair

/-- A small ball whose radius is at most one is nested in the unit ball of the
same pair, in the abstract `ScaleControlledBall` sense. -/
theorem nested_of_le {B : Ham3BallPair M}
    (hsmall : B.small.radius <= 1) :
    RicciFlow.Perelman.ScaleControlledBall.Nested B.small B.unit := by
  refine ⟨B.same_center, B.same_time, ?_⟩
  simpa [B.unit_radius] using hsmall

end Ham3BallPair

/-- The lower volume bound supplied by Perelman's noncollapsing theorem at the
fixed radius, recorded with actual small/unit ball witnesses.

The future real geodesic-ball volume producer should prove `volume_mono` from
Riemannian measure monotonicity and the metric inclusion supplied by
`RicciFlower.ball_subset_of_le r0_le_one`. -/
def Ham3Noncollapse
    {g0 : SmoothRiemannianMetric I M}
    (_P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (kappa r : Real) : Prop :=
  0 < kappa /\ 0 < r /\
    exists balls : Nat -> Ham3BallPair M, exists N : Nat, forall i : Nat, N <= i ->
      (balls i).small.center = Q.point i /\
        (balls i).small.time = 0 /\
        (balls i).small.radius = r /\
        (balls i).small.curvatureControlled /\
        RicciFlow.Perelman.KappaNoncollapsedAtBall 3 kappa (balls i).small

/-- Projection of the geometric noncollapsing package to the old unit-ball
volume lower-bound shape used by compactness statements. -/
theorem Ham3Noncollapse.unitVolLower
    {g0 : SmoothRiemannianMetric I M}
    {P : Ham3FlowPackage (I := I) (M := M) g0}
    {Q : Ham3BlowupData M} {kappa r : Real}
    (h : Ham3Noncollapse (I := I) P Q kappa r) :
    exists unitVolume : Nat -> Real, exists N : Nat, forall i : Nat, N <= i ->
      kappa * r ^ 3 <= unitVolume i := by
  rcases h with ⟨_hkappa, _hr, balls, N, hballs⟩
  refine ⟨fun i : Nat => (balls i).unit.volume, N, ?_⟩
  intro i hi
  rcases hballs i hi with
    ⟨_hcenter, _htime, hradius, hcurv, hnoncollapsed⟩
  have hsmall :
      kappa * r ^ 3 <= (balls i).small.volume := by
    have h :=
      hnoncollapsed.2.2 hcurv
    simpa [hradius] using h
  exact le_trans hsmall (balls i).volume_mono

/-- The geometric content behind the small-to-unit volume step: after the fixed
radius is known to be at most one, the eventual Perelman balls are nested in
the abstract ball-pair sense and carry the recorded volume monotonicity. -/
theorem Ham3Noncollapse.unitNested
    {g0 : SmoothRiemannianMetric I M}
    {P : Ham3FlowPackage (I := I) (M := M) g0}
    {Q : Ham3BlowupData M} {kappa r : Real}
    (hr : r <= 1)
    (h : Ham3Noncollapse (I := I) P Q kappa r) :
    exists balls : Nat -> Ham3BallPair M, exists N : Nat, forall i : Nat, N <= i ->
      (balls i).small.center = Q.point i /\
        (balls i).small.time = 0 /\
        (balls i).small.radius = r /\
        (balls i).small.curvatureControlled /\
        RicciFlow.Perelman.KappaNoncollapsedAtBall 3 kappa (balls i).small /\
        RicciFlow.Perelman.ScaleControlledBall.Nested
          (balls i).small (balls i).unit /\
        (balls i).small.volume <= (balls i).unit.volume := by
  rcases h with ⟨_hkappa, _hr, balls, N, hballs⟩
  refine ⟨balls, N, ?_⟩
  intro i hi
  rcases hballs i hi with
    ⟨hcenter, htime, hradius, hcurv, hnoncollapsed⟩
  have hsmall : (balls i).small.radius <= 1 := by
    rw [hradius]
    exact hr
  exact
    ⟨hcenter, htime, hradius, hcurv, hnoncollapsed,
      Ham3BallPair.nested_of_le (M := M) hsmall,
      (balls i).volume_mono⟩

/-- Projection of the normalized maximal-flow time interval used by
Corollary 7.4.  The normalization is a setup output, not a theorem about an
arbitrary flow package. -/
theorem ham3_time74
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists omega' : Real, exists h0ω' : 0 < omega',
      P.D = Realized.RealTimeInterval.closedOpen 0 omega' h0ω' := by
  exact ⟨omega, h0ω, hD⟩

/-- Continuity of the initial scalar trace.  This is the scalar-continuity
producer used only to choose the compact initial minimum. -/
theorem ham3_scalar0_cont74
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Continuous (fun x : M => ham3Scalar (I := I) P 0 x) := by
  rw [continuous_iff_continuousAt]
  intro x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
  have hmdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
            (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
            (P.S.ricci 0 y)) x :=
    Tensor0SBundle.inner0S_two_mdiff
      (I := I) (P.S.family.metric 0)
      (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0))
      (P.S.ricci 0) x
  have hfun :
      (fun y : M =>
          Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
            (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
            (P.S.ricci 0 y)) =
        fun y : M => ham3Scalar (I := I) P 0 y := by
    funext y
    have hmetric :
        Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y =
          Realized.metricTensor0S (I := I) (P.S.family.metric 0) y := by
      ext v
      rw [Tensor0SBundle.metricTensorField_apply,
        Realized.metricTensor0S_apply]
    change
      Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
          (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
          (P.S.ricci 0 y) =
        RicciFlow.SolutionOn.scalar (I := I) (ham3Solution (I := I) P) 0 y
    rw [RicciFlow.SolutionOn.scalar_eq_metricTrace,
      Realized.metricTracePair0SAt, hmetric]
    simp [RicciFlow.SolutionOn.ricci, RicciFlow.SolutionOn.ricciAt,
      RicciFlow.SolutionFamily.ricci_apply]
  exact (hfun ▸ hmdiff.continuousAt)

/-- Positive initial metric Ricci curvature gives positive time-zero Ricci for
the canonical Ricci tensor carried by the Hamilton flow package. -/
theorem ham3_ricci_pos0
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    RicciFlow.RicciPosInit (I := I) (M := M)
      (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci) := by
  intro x v hv
  have hmetric0 : P.S.family.metric 0 = g0 := by
    have hinit : P.D.initial = 0 := by
      rw [hD]
      rfl
    simpa [hinit] using P.startsAt
  have hpos0 :
      0 < RicciFlow.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (Curvature.vec2 (I := I) v v) := by
    rw [hmetric0]
    exact hpos x v hv
  simpa [Realized.twoTensorSecToFamily, RicciFlow.SolutionOn.ricci,
    RicciFlow.SolutionOn.ricciAt, RicciFlow.SolutionFamily.ricci,
    RicciFlow.SolutionFamily.ricciAt] using hpos0

/-- Positive initial Ricci curvature gives positive initial scalar curvature
after the normalized time setup identifies `t = 0` with the initial metric. -/
theorem ham3_scalar0_pos74
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    forall x : M, 0 < ham3Scalar (I := I) P 0 x := by
  intro x
  have hmetric0 : P.S.family.metric 0 = g0 := by
    have hinit : P.D.initial = 0 := by
      rw [hD]
      rfl
    simpa [hinit] using P.startsAt
  have hdimx : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hpos0 :
      forall v : TangentSpace I x, v ≠ 0 ->
        0 < P.S.ricciAt 0 x (Curvature.vec2 (I := I) v v) := by
    intro v hv
    change
      0 < RicciFlow.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (Curvature.vec2 (I := I) v v)
    rw [hmetric0]
    exact hpos x v hv
  exact
    DimensionThree.metricTrace_pos_of_posDef
      (I := I) (M := M) (P.S.family.metric 0) (P.S.ricciAt 0 x)
      hdimx hpos0

/-- Initial positive Ricci curvature supplies the positive scalar minimum used
by Corollary 7.4. -/
theorem ham3_init74
    [CompactSpace M] [Nonempty M]
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real,
      RicciFlow.InitialScalarMinimum (M := M) (ham3Scalar (I := I) P) c0 ∧
        forall x : M, 0 < ham3Scalar (I := I) P 0 x := by
  have hcont : Continuous (fun x : M => ham3Scalar (I := I) P 0 x) :=
    ham3_scalar0_cont74 (I := I) (M := M) P
  rcases RicciFlow.exists_initialScalarMinimum_of_continuous
      (M := M) (ham3Scalar (I := I) P) hcont with
    ⟨c0, hmin⟩
  exact ⟨c0, hmin, ham3_scalar0_pos74 (I := I) (M := M) hdim h0ω hpos P hD⟩

/-- Scalar curvature is continuous on the compact pole slab used in the
finite-time argument. -/
theorem ham3_cont74
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (c0 : Real) :
    ContinuousOn
      (fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
      (Realized.spacetimeSlab (M := M)
        (RicciFlow.scalarBlowupTime 3 c0)) := by
  have hreg :
      RicciFlow.ScalarSTContOn
        (I := I) (M := M) (ham3Solution (I := I) P) :=
    ham3_scalarSTCont (I := I) (M := M) P
  simpa [ham3Scalar, Realized.spacetimeSlab] using
    RicciFlow.SolutionOn.scalar_continuousOn
      (I := I) (M := M) (ham3Solution (I := I) P)
      P.isSmooth.isSolution hreg
      (RicciFlow.scalarBlowupTime 3 c0)

/-- Scalar evolution in the intrinsic package:
`partial_t R = Delta R + 2 |Ric|^2`. -/
theorem ham3_evol74
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    RicciFlow.ScalarEvolutionEquationOn
      (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
      (ham3Scalar (I := I) P)
      (ham3ScalarLap (I := I) P)
      (ham3RicNormSq (I := I) P) := by
  rw [← hD]
  have h :
      RicciFlow.ScalarEvolutionEquationOn
        (D := P.D)
        (ham3Solution (I := I) P).scalar
        (fun t x =>
          Realized.laplacianAt (I := I) (ham3RealFamily (I := I) P) t
            ((ham3Solution (I := I) P).scalar t) x)
        (fun t x =>
          Tensor0SBundle.normSq0S (I := I)
            ((ham3Solution (I := I) P).family.metric t) x 2
            ((ham3Solution (I := I) P).ricci t x)) := by
    refine
      RicciFlow.scalarEvolOfSmooth
        (I := I) (M := M) (ham3Solution (I := I) P) P.isSmooth
        (ham3RealFamily (I := I) P) ?_ ?_
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [ham3RealFamily, ham3RealFamilyCore, ht]
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [ham3RealFamily, ham3RealFamilyCore, ht]
  simpa [ham3Scalar, ham3ScalarLap, ham3RicNormSq, ham3Solution] using h

/-- The scalar Laplacian definition realizes the heat-operator Laplacian on
every compact time slab. -/
theorem ham3_lap74
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) (T : Real) :
    RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
      (I := I) (ham3RealFamily (I := I) P) T
      (ham3Scalar (I := I) P)
      (ham3ScalarLap (I := I) P) := by
  exact
    RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
      (I := I) (G := ham3RealFamily (I := I) P)
      (T := T) (scalar := ham3Scalar (I := I) P)
      (scalarLap := ham3ScalarLap (I := I) P)
      (by
        intro t _ht x
        rfl)

/-- WMP regularity producer for the scalar lower-bound package. -/
theorem ham3_reg74
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (c0 : Real) (hc0 : 0 < c0) (K : Real -> NNReal) :
    forall T : Real, 0 < T -> T < omega ->
      T < RicciFlow.scalarBlowupTime 3 c0 ->
        RicciFlow.ScalarLowerBoundWMPRegularity
          (I := I) (ham3RealFamily (I := I) P) T 3 c0
          (ham3Scalar (I := I) P) (K T) := by
  intro T _hT hTω hPole
  have hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hden_pos :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
    RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
      (n := 3) (c0 := c0) (by norm_num) hc0 hPole
  have hden :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        1 - (2 / (3 : Real)) * c0 * t ≠ 0 := by
    intro t ht
    exact ne_of_gt (hden_pos t ht)
  simpa [ham3RealFamily, ham3Scalar, ham3Solution] using
    ham3_scalarRegular (I := I) (M := M) P c0 K T hsubset hden

/-- Three-dimensional trace Cauchy-Schwarz for the intrinsic scalar and Ricci
norm package. -/
theorem ham3_ricBound74
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (t : Real) (x : M) :
    (1 / 3 : Real) * (ham3Scalar (I := I) P t x) ^ 2 <=
      ham3RicNormSq (I := I) P t x := by
  classical
  letI : Nonempty (Coordinates.CoordinateIdx (𝕜 := Real) E) :=
    ⟨⟨0, by simp [hdim]⟩⟩
  let basis : Module.Basis (Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) :=
    Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      Coordinates.CoordinateIdx (𝕜 := Real) E ->
        Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      Coordinates.inverseMetricFlatModelInChart_component
        (I := I) (P.S.family.metric t) x k l (extChartAt I x x)
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (P.S.family.metric t) x
        basis gInv := by
    simpa [basis, gInv] using
      Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (P.S.family.metric t) x
  have h :=
    Realized.metricTracePair0SAt_sq_div_rank_le_normSq0S
      (I := I) (g := P.S.family.metric t) (basis := basis)
      (gInv := gInv) hinv (P.S.ricciAt t x)
  have hcard :
      (1 / (Fintype.card (Coordinates.CoordinateIdx (𝕜 := Real) E) : Real)) =
        (1 / 3 : Real) := by
    simp [Coordinates.CoordinateIdx, hdim]
  have hcoef : ((Module.finrank Real E : Real)⁻¹) = (3⁻¹ : Real) := by
    simp [hdim]
  simpa [ham3Scalar, ham3RicNormSq, Coordinates.CoordinateIdx, hcard, hcoef]
    using h

/-- Compact value-set Lipschitz producer for the scalar lower-bound reaction. -/
theorem ham3_lip74
    [CompactSpace M]
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (c0 : Real)
    (hc0 : 0 < c0)
    (hcont : ContinuousOn
      (fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
      (Realized.spacetimeSlab (M := M)
        (RicciFlow.scalarBlowupTime 3 c0))) :
    exists K : Real -> NNReal,
      forall T : Real, 0 < T -> forall omega : Real, T < omega ->
        T < RicciFlow.scalarBlowupTime 3 c0 ->
          forall t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => RicciFlow.scalarLowerReaction 3 a t)
              (Realized.scalarWMPValueSet (M := M) T
                (ham3Scalar (I := I) P)
                (RicciFlow.scalarLowerBarrier 3 c0)) := by
  classical
  have hExists :
      ∀ T : Real, 0 < T -> T < RicciFlow.scalarBlowupTime 3 c0 ->
        ∃ K : NNReal,
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith K
              (fun a : Real => RicciFlow.scalarLowerReaction 3 a t)
              (Realized.scalarWMPValueSet (M := M) T
                (ham3Scalar (I := I) P)
                (RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T _hT hPole
    have hsubset :
        Realized.spacetimeSlab (M := M) T ⊆
          Realized.spacetimeSlab (M := M)
            (RicciFlow.scalarBlowupTime 3 c0) := by
      intro p hp
      exact ⟨⟨hp.1.1, le_trans hp.1.2 (le_of_lt hPole)⟩, trivial⟩
    have hscalar_cont_T :
        ContinuousOn
          (fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
          (Realized.spacetimeSlab (M := M) T) :=
      hcont.mono hsubset
    have hden :
        ∀ t : Real, t ∈ Set.Icc 0 T ->
          0 < 1 - (2 / 3 : Real) * c0 * t :=
      RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 hPole
    have hbar_cont :
        ContinuousOn (RicciFlow.scalarLowerBarrier 3 c0) (Set.Icc 0 T) := by
      unfold RicciFlow.scalarLowerBarrier
      have hden_cont :
          ContinuousOn (fun t : Real => 1 - (2 / 3 : Real) * c0 * t)
            (Set.Icc 0 T) := by
        fun_prop
      exact continuousOn_const.div hden_cont (fun t ht => ne_of_gt (hden t ht))
    have hcompact :
        IsCompact
          (Realized.scalarWMPValueSet (M := M) T
            (ham3Scalar (I := I) P)
            (RicciFlow.scalarLowerBarrier 3 c0)) :=
      Realized.scalarWMPValueSet_isCompact
        (M := M) T (ham3Scalar (I := I) P)
        (RicciFlow.scalarLowerBarrier 3 c0) hscalar_cont_T hbar_cont
    exact
      RicciFlow.exists_scalarLowerReaction_lipschitzOn_valueSet
        (M := M) 3 T (ham3Scalar (I := I) P)
        (RicciFlow.scalarLowerBarrier 3 c0) hcompact
  let K : Real -> NNReal := fun T =>
    if h : 0 < T ∧ T < RicciFlow.scalarBlowupTime 3 c0 then
      Classical.choose (hExists T h.1 h.2)
    else 0
  refine ⟨K, ?_⟩
  intro T hT _omega _hTω hPole t ht
  dsimp [K]
  rw [dif_pos ⟨hT, hPole⟩]
  exact Classical.choose_spec (hExists T hT hPole) t ht

/-- Section 11/7 producer: extract the scalar package needed by Corollary 7.4
from Hamilton's normalized maximal Ricci-flow package.

This is now the precise remaining frontier behind Lemma 11.1: it must identify
the maximal interval with `[0, omega)`, choose the scalar trace and its
Laplacian/Ricci-norm data, and supply scalar evolution, WMP regularity, the
Laplacian realization, and the three-dimensional Ricci-norm lower bound. -/
theorem ham3_scalar74
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists G : Realized.RealizedMetricFamily (I := I) (M := M) Real,
      exists c0 : Real,
      exists scalar scalarLap ricciNormSq : Real -> M -> Real,
      exists K : Real -> NNReal,
        RicciFlow.InitialScalarMinimum (M := M) scalar c0 /\
        (forall x : M, 0 < scalar 0 x) /\
        ContinuousOn
          (fun p : Real × M => scalar p.1 p.2)
          (Realized.spacetimeSlab (M := M)
            (RicciFlow.scalarBlowupTime 3 c0)) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            RicciFlow.ScalarLowerBoundWMPRegularity
              (I := I) G T 3 c0 scalar (K T)) /\
        RicciFlow.ScalarEvolutionEquationOn
          (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
          scalar scalarLap ricciNormSq /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
              (I := I) G T scalar scalarLap) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
              (1 / 3 : Real) * (scalar t x) ^ 2 <= ricciNormSq t x) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T ->
              LipschitzOnWith (K T)
                (fun a : Real => RicciFlow.scalarLowerReaction 3 a t)
                (Realized.scalarWMPValueSet (M := M) T scalar
                  (RicciFlow.scalarLowerBarrier 3 c0))) := by
  rcases hM with ⟨hcompact, _hconnected, _hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : Nonempty M := inferInstance
  rcases ham3_init74 (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont := ham3_cont74 (I := I) (M := M) P c0
  have hc0 : 0 < c0 :=
    RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases ham3_lip74 (I := I) (M := M) P c0 hc0 hcont with
    ⟨K, hK⟩
  refine ⟨ham3RealFamily (I := I) P, c0,
    ham3Scalar (I := I) P, ham3ScalarLap (I := I) P,
    ham3RicNormSq (I := I) P, K, hinit_min, hinit_pos, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · exact ham3_reg74 (I := I) (M := M) h0ω P hD c0 hc0 K
  · exact ham3_evol74 (I := I) (M := M) h0ω P hD
  · intro T _hT _hTω _hPole
    exact ham3_lap74 (I := I) (M := M) P T
  · intro _T _hT _hTω _hPole t _ht x
    exact ham3_ricBound74 (I := I) (M := M) hdim P t x
  · intro T hT hTω hPole
    exact hK T hT omega hTω hPole

/-- Lemma 11.1-style input: the maximal Ricci flow reaches a finite singular
time. -/
theorem ham3_finite_time
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real, 0 < c0 /\ omega <= 3 / (2 * c0) := by
  have hMcopy := hM
  rcases hM with ⟨hcompact, hconnected, hboundaryless, _hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  rcases ham3_scalar74 (I := I) (M := M) h0ω hMcopy g0 hpos P hD with
    ⟨G, c0, scalar, scalarLap, ricciNormSq, K,
      hinit_min, hinit_pos, hscalar_cont, hreg, hevol, hlap, hricci, hF_lip⟩
  have hfinite :
      0 < c0 ∧ omega <= 3 / (2 * c0) :=
    RicciFlow.finiteTime3D (I := I) (M := M) h0ω G c0 scalar scalarLap
      ricciNormSq K hinit_min hinit_pos hscalar_cont hreg hevol hlap
      hricci hF_lip
  exact ⟨c0, hfinite.1, hfinite.2⟩

private theorem ham3_rm_scalar_ctl
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (hsec9 : Ham3Section9RicNonneg (I := I) P omega)
    {t : Real} {x : M} (htD : t ∈ P.D.carrier) :
    0 <= ham3Scalar (I := I) P t x ∧
      ham3RmNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (ham3Scalar (I := I) P t x) ^ 2 := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  have htD' : t ∈ (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    simpa [hD] using htD
  have ht0 : 0 <= t := htD'.1
  have htω : t < omega := htD'.2
  have hricOn := hsec9 t ht0 htω
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hricNonneg :
      DimensionThree.RicciNonnegAt (I := I) (P.S.ricciAt t x) := by
    intro v
    simpa [Curvature.vec2, RicciFlow.SolutionOn.ricciAt] using
      hricOn t ⟨ht0, le_rfl⟩ x v
  have hricSym :
      DimensionThree.RicciSymAt (I := I) (P.S.ricciAt t x) :=
    RicciFlow.ricciSym_can (I := I) (M := M) P.S t x
  have hRmScalar :
      ham3RmNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (ham3Scalar (I := I) P t x) ^ 2 := by
    have hpoint :=
      DimensionThree.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric t)
        (Ric := P.S.ricciAt t x) (scalar := P.S.scalar t x)
        (Rm04 := P.S.base.rm04 t x) hdimT hricSym hricNonneg
        (fun basis horth =>
          RicciFlow.traceData_can (I := I) (M := M) P.S horth)
    simpa [ham3RmNormSq, ham3Scalar, ham3Solution] using hpoint
  have hscalarNonneg : 0 <= ham3Scalar (I := I) P t x := by
    rcases DimensionThree.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric t) (P.S.ricciAt t x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        Realized.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar t x) (P.S.ricciAt t x) DimensionThree.delta3 basis := by
      have htr :=
        RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric t)
          (P.S.ricciAt t x) horth
      simpa [RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar t x = DimensionThree.ricciEigenScalar3 l1 l2 l3 :=
      RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar t x
    rw [hscalar_eq]
    unfold DimensionThree.ricciEigenScalar3
    nlinarith
  exact ⟨hscalarNonneg, hRmScalar⟩

private theorem scalar_pos_of_rm {R rm : Real}
    (hR : 0 <= R) (hctl : rm <= (100 : Real) ^ 2 * R ^ 2)
    (hrm : 0 < rm) :
    0 < R := by
  by_contra hnot
  have hRle : R <= 0 := le_of_not_gt hnot
  have hR0 : R = 0 := le_antisymm hRle hR
  nlinarith

private theorem scalar_gt_of_rm {A R rm : Real}
    (hA : 0 < A) (hR : 0 <= R)
    (hctl : rm <= (100 : Real) ^ 2 * R ^ 2)
    (hrm : (100 : Real) ^ 2 * A ^ 2 < rm) :
    A < R := by
  have hsq : A ^ 2 < R ^ 2 := by
    nlinarith
  by_contra hnot
  have hRleA : R <= A := le_of_not_gt hnot
  have hdiff : 0 <= A - R := by linarith
  have hsum : 0 <= A + R := by linarith
  have hprod : 0 <= (A - R) * (A + R) :=
    mul_nonneg hdiff hsum
  nlinarith

private theorem ham3_scalar_cont_slab
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (T : Real) :
    ContinuousOn
      (fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
      (Realized.spacetimeSlab (M := M) T) := by
  have hreg :
      RicciFlow.ScalarSTContOn
        (I := I) (M := M) (ham3Solution (I := I) (M := M) P) :=
    ham3_scalarSTCont (I := I) (M := M) P
  simpa [ham3Scalar, Realized.spacetimeSlab] using
    RicciFlow.SolutionOn.scalar_continuousOn
      (I := I) (M := M) (ham3Solution (I := I) (M := M) P)
      P.isSmooth.isSolution hreg T

private theorem slab_max_of_continuousOn
    [CompactSpace M]
    {f : Real × M -> Real}
    {T t : Real} {x : M}
    (hcont : ContinuousOn f (Realized.spacetimeSlab (M := M) T))
    (ht : t ∈ Set.Icc 0 T) :
    ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 T ∧
        ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ y : M,
          f (s, y) <= f (tmax, xmax) := by
  classical
  let slab := Realized.spacetimeSlab (M := M) T
  have hcompact : IsCompact slab := by
    unfold slab Realized.spacetimeSlab
    exact isCompact_Icc.prod isCompact_univ
  have hnonempty : slab.Nonempty := ⟨(t, x), ⟨ht, trivial⟩⟩
  rcases hcompact.exists_isMaxOn hnonempty hcont with ⟨p, hp, hmax⟩
  rcases p with ⟨tmax, xmax⟩
  refine ⟨tmax, xmax, hp.1, ?_⟩
  intro s hs y
  exact hmax ⟨hs, trivial⟩

private def ham3PointLevel (B : Real) (i : Nat) : Real :=
  max B 0 + ((i : Real) + 1)

private theorem ham3PointLevel_pos (B : Real) (i : Nat) :
    0 < ham3PointLevel B i := by
  unfold ham3PointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem ham3PointLevel_gt_bound (B : Real) (i : Nat) :
    B < ham3PointLevel B i := by
  unfold ham3PointLevel
  have hB : B <= max B 0 := le_max_left B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem ham3PointLevel_ge_index (B : Real) (i : Nat) :
    ((i : Real) + 1) <= ham3PointLevel B i := by
  unfold ham3PointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  linarith

/-- Lemma 11.3 plus Corollary 11.4-style scalar blow-up producer.

The flow package supplies curvature blow-up at the finite maximal endpoint.
Section 9 Ricci nonnegativity and the dimension-three curvature-control
estimate convert that into scalar curvature blow-up. -/
theorem ham3_scalar_blowup
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (hsec9 : Ham3Section9RicNonneg (I := I) P omega) :
    Ham3ScalarBlowup (I := I) P := by
  intro A
  by_cases hA : 0 < A
  · rcases P.curvUnbounded ((100 : Real) ^ 2 * A ^ 2) with
      ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' :
        (100 : Real) ^ 2 * A ^ 2 <
          ham3RmNormSq (I := I) (M := M) P t x := by
      simpa [ham3RmNormSq, ham3Solution] using hRm
    have hctl :=
      ham3_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hsec9
        (t := t) (x := x) htD
    exact scalar_gt_of_rm hA hctl.1 hctl.2 hRm'
  · rcases P.curvUnbounded 0 with ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' : 0 < ham3RmNormSq (I := I) (M := M) P t x := by
      simpa [ham3RmNormSq, ham3Solution] using hRm
    have hctl :=
      ham3_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hsec9
        (t := t) (x := x) htD
    have hRpos :
        0 < ham3Scalar (I := I) P t x :=
      scalar_pos_of_rm hctl.1 hctl.2 hRm'
    exact lt_of_le_of_lt (le_of_not_gt hA) hRpos

/-- Lemma 11.6-style point selection from scalar blow-up: choose blow-up
points, times, and parabolic rescalings normalized by scalar curvature. -/
theorem ham3_point_select
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (_hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hfinite : exists omega c0 : Real, exists h0ω : 0 < omega,
      P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω /\
        0 < c0 /\ omega <= 3 / (2 * c0))
    (hscalarBlowup : Ham3ScalarBlowup (I := I) P) :
    exists Q : Ham3BlowupData M, Ham3PointSel (I := I) P Q := by
  classical
  rcases hM with ⟨hcompact, _hconnected, _hboundaryless, _hdim⟩
  letI : CompactSpace M := hcompact
  rcases hfinite with ⟨omega, _c0, h0ω, hD, _hc0, _hfiniteBound⟩
  let half : Real := omega / 2
  have hhalf_pos : 0 < half := by
    dsimp [half]
    linarith
  have hhalf_nonneg : 0 <= half := le_of_lt hhalf_pos
  have hhalf_lt_omega : half < omega := by
    dsimp [half]
    linarith
  have hcont_half :
      ContinuousOn
        (fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
        (Realized.spacetimeSlab (M := M) half) :=
    ham3_scalar_cont_slab (I := I) (M := M) P half
  have hbounded_half :
      RicciFlow.ScalarBoundedAboveOnSlab
        (M := M) (ham3Scalar (I := I) P) half :=
    RicciFlow.ScalarBoundedAboveOnSlab.of_continuousOn
      (M := M) hcont_half
  rcases hbounded_half with ⟨Bhalf, hBhalf⟩
  let level : Nat -> Real := fun i => ham3PointLevel Bhalf i
  have hraw : ∀ i : Nat, ∃ t : Real, ∃ x : M,
      t ∈ P.D.carrier /\ level i < ham3Scalar (I := I) P t x := by
    intro i
    exact hscalarBlowup (level i)
  let rawTime : Nat -> Real := fun i => Classical.choose (hraw i)
  let rawPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hraw i))
  have hraw_spec : ∀ i : Nat,
      rawTime i ∈ P.D.carrier /\
        level i < ham3Scalar (I := I) P (rawTime i) (rawPoint i) := by
    intro i
    simpa [rawTime, rawPoint] using
      Classical.choose_spec (Classical.choose_spec (hraw i))
  have hraw_nonneg : ∀ i : Nat, 0 <= rawTime i := by
    intro i
    have hmem : rawTime i ∈
        (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.1
  have hraw_lt_omega : ∀ i : Nat, rawTime i < omega := by
    intro i
    have hmem : rawTime i ∈
        (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.2
  have hmax_exists : ∀ i : Nat, ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          ham3Scalar (I := I) P s y <=
            ham3Scalar (I := I) P tmax xmax := by
    intro i
    exact slab_max_of_continuousOn (M := M)
      (f := fun p : Real × M => ham3Scalar (I := I) P p.1 p.2)
      (T := rawTime i) (t := rawTime i) (x := rawPoint i)
      (ham3_scalar_cont_slab (I := I) (M := M) P (rawTime i))
      ⟨hraw_nonneg i, le_rfl⟩
  let qTime : Nat -> Real := fun i => Classical.choose (hmax_exists i)
  let qPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hmax_exists i))
  have hq_spec : ∀ i : Nat,
      qTime i ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          ham3Scalar (I := I) P s y <=
            ham3Scalar (I := I) P (qTime i) (qPoint i) := by
    intro i
    simpa [qTime, qPoint] using
      Classical.choose_spec (Classical.choose_spec (hmax_exists i))
  let Q : Ham3BlowupData M := ⟨qPoint, qTime⟩
  refine ⟨Q, ?_⟩
  have hscale_lower : ∀ i : Nat,
      level i < ham3BlowupScale (I := I) P Q i := by
    intro i
    have hraw_le :=
      (hq_spec i).2 (rawTime i) ⟨hraw_nonneg i, le_rfl⟩ (rawPoint i)
    exact lt_of_lt_of_le (hraw_spec i).2 hraw_le
  have hscale_pos : ∀ i : Nat, 0 < ham3BlowupScale (I := I) P Q i := by
    intro i
    exact lt_trans (ham3PointLevel_pos Bhalf i) (hscale_lower i)
  have hq_gt_half : ∀ i : Nat, half < Q.time i := by
    intro i
    by_contra hnot
    have hle : Q.time i <= half := le_of_not_gt hnot
    have hmem_half : Q.time i ∈ Set.Icc 0 half :=
      ⟨(hq_spec i).1.1, hle⟩
    have hupper := hBhalf (Q.time i) hmem_half (Q.point i)
    have hB_lt_level : Bhalf < level i :=
      ham3PointLevel_gt_bound Bhalf i
    exact not_lt_of_ge hupper (lt_trans hB_lt_level (hscale_lower i))
  have htime_pos : ∀ i : Nat, 0 < Q.time i := by
    intro i
    exact lt_trans hhalf_pos (hq_gt_half i)
  have htime_mem : ∀ i : Nat, Q.time i ∈ P.D.carrier := by
    intro i
    rw [hD]
    exact ⟨(hq_spec i).1.1,
      lt_of_le_of_lt (hq_spec i).1.2 (hraw_lt_omega i)⟩
  refine ⟨hscale_pos, htime_pos, htime_mem, ?_, ?_, ?_⟩
  · intro A
    obtain ⟨N, hN⟩ := exists_nat_ge (A / half)
    refine ⟨N, ?_⟩
    intro i hi
    have hNi : (N : Real) <= i := by exact_mod_cast hi
    have hA_le_Nhalf : A <= (N : Real) * half := by
      have hm := mul_le_mul_of_nonneg_right hN hhalf_nonneg
      simpa [div_mul_cancel₀ A (ne_of_gt hhalf_pos)] using hm
    have hNhalf_le_ihalf : (N : Real) * half <= (i : Real) * half :=
      mul_le_mul_of_nonneg_right hNi hhalf_nonneg
    have hihalf_le_i1half : (i : Real) * half <= ((i : Real) + 1) * half := by
      nlinarith [hhalf_nonneg]
    have hi1half_le_levelhalf :
        ((i : Real) + 1) * half <= level i * half :=
      mul_le_mul_of_nonneg_right
        (ham3PointLevel_ge_index Bhalf i) hhalf_nonneg
    have hprod_gt : level i * half <
        ham3BlowupScale (I := I) P Q i * Q.time i := by
      nlinarith [hscale_lower i, hq_gt_half i,
        le_of_lt (ham3PointLevel_pos Bhalf i), hhalf_pos]
    exact le_of_lt
      (lt_of_le_of_lt
        (le_trans hA_le_Nhalf
          (le_trans hNhalf_le_ihalf
            (le_trans hihalf_le_i1half hi1half_le_levelhalf)))
        hprod_gt)
  · intro i
    have hscale_ne : ham3BlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htime0 : ham3RescaledTime (I := I) P Q i 0 = Q.time i := by
      dsimp [ham3RescaledTime]
      field_simp [hscale_ne]
      ring
    have hscalar0 :
        ham3Scalar (I := I) P
            (ham3RescaledTime (I := I) P Q i 0) (Q.point i) =
          ham3BlowupScale (I := I) P Q i := by
      rw [htime0]
      rfl
    dsimp [ham3RescaledScalar]
    rw [hscalar0]
    field_simp [hscale_ne]
  · intro i s x hsleft hsright
    have hscale_ne : ham3BlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htau_mem : ham3RescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (Q.time i) := by
      constructor
      · dsimp [ham3RescaledTime]
        have hdiv :
            -Q.time i <= s / ham3BlowupScale (I := I) P Q i := by
          have hdiv' :
              -(ham3BlowupScale (I := I) P Q i * Q.time i) /
                  ham3BlowupScale (I := I) P Q i <=
                s / ham3BlowupScale (I := I) P Q i :=
            div_le_div_of_nonneg_right hsleft (le_of_lt (hscale_pos i))
          have hleft :
              -(ham3BlowupScale (I := I) P Q i * Q.time i) /
                  ham3BlowupScale (I := I) P Q i = -Q.time i := by
            field_simp [hscale_ne]
          simpa [hleft] using hdiv'
        linarith
      · dsimp [ham3RescaledTime]
        have hdiv : s / ham3BlowupScale (I := I) P Q i <= 0 := by
          exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale_pos i))
        linarith
    have htau_raw : ham3RescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (rawTime i) :=
      ⟨htau_mem.1, le_trans htau_mem.2 (hq_spec i).1.2⟩
    have hscalar_le :
        ham3Scalar (I := I) P (ham3RescaledTime (I := I) P Q i s) x <=
          ham3BlowupScale (I := I) P Q i :=
      (hq_spec i).2 (ham3RescaledTime (I := I) P Q i s) htau_raw x
    dsimp [ham3RescaledScalar]
    have hmul :=
      mul_le_mul_of_nonneg_left hscalar_le
        (inv_nonneg.mpr (le_of_lt (hscale_pos i)))
    have hone :
        (ham3BlowupScale (I := I) P Q i)⁻¹ *
            ham3BlowupScale (I := I) P Q i = 1 := by
      field_simp [hscale_ne]
    simpa [hone] using hmul

/-- Section 9 shifted pinching preservation along the normalized Hamilton flow,
produced by the closed Ricci-flow WMP data package. -/
theorem ham3_pinch9_fixed
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    Ham3Section9PinchFixed (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hpos0 :
      RicciFlow.RicciPosInit (I := I) (M := M)
        (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci) :=
    ham3_ricci_pos0 (I := I) (M := M) h0ω hpos P hD
  have hinit : RicciFlow.PinchInitLt (I := I) (M := M)
      (fun t : Real => P.S.base.metric t)
      (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      P.S.scalar :=
    RicciFlow.pinchInitLt_pos (I := I) (M := M)
      (G := fun t : Real => P.S.base.metric t)
      (Ric := Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      (scalar := P.S.scalar)
      (RicciFlow.metricData_sol0 (I := I) (M := M) P.S)
      (RicciFlow.metricData_sol0_pos (I := I) (M := M) P.S hpos0)
      (RicciFlow.scalar0_cont_sol (I := I) (M := M) P.S P.isSmooth.isSolution)
  rcases hinit with ⟨delta, hdelta0, hdelta13, hpinch0⟩
  refine ⟨delta, hdelta0, hdelta13, ?_⟩
  intro T hT hTω
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    simpa using hdim
  have hTsub : Set.Icc 0 T ⊆ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hTreg : Set.Ioc 0 T ⊆ P.D.regular := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  exact RicciFlow.pinch_sol_closed (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdelta0 hdelta13 hdimT hTsub hTreg hpinch0

/-- Section 9 shifted pinching preservation along the normalized Hamilton flow,
produced by the closed Ricci-flow WMP data package. -/
theorem ham3_pinch9
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    Ham3Section9Pinch (I := I) P omega := by
  exact (ham3_pinch9_fixed (I := I) (M := M) h0ω hM hpos P hD).toVarying

/-- Section 9 Ricci nonnegativity along the normalized Hamilton flow, produced
as the `delta = 0` endpoint of the shifted WMP package. -/
theorem ham3_ric_nonneg9
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    Ham3Section9RicNonneg (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hpos0 := ham3_ricci_pos0 (I := I) (M := M) h0ω hpos P hD
  have hinit : Realized.TwoTensorFamilyNonnegativeAtTime
      (I := I) (M := M)
      (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci) 0 := by
    intro x v
    by_cases hv : v = 0
    · subst v
      have hbilin := Realized.twoTensorSecToFamily_bilin
        (I := I) (M := M) P.S.ricci 0 x
      have hzero :
          (Realized.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
              0 x 0 0 = 0 := by
        have h := hbilin.smul_left 0
          (0 : TangentSpace I x) (0 : TangentSpace I x)
        simpa using h
      rw [hzero]
    · exact le_of_lt (hpos0 x v hv)
  intro T hT hTω
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    simpa using hdim
  have hTsub : Set.Icc 0 T ⊆ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hTreg : Set.Ioc 0 T ⊆ P.D.regular := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  exact RicciFlow.ricci_nonneg_sol_closed (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdimT hTsub hTreg hinit

/-- Lemma 9.1-style input: nonnegative Ricci curvature persists on the selected
rescaled flow slabs. -/
theorem ham3_rescaled_ric_nonneg
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q) :
    Ham3RescaledRicNonneg (I := I) P Q := by
  rcases hsel with ⟨hscale, htime, htimeMem, _hprod, _hbase, _hscalarMax⟩
  have hricOn : Ham3Section9RicNonneg (I := I) P omega :=
    ham3_ric_nonneg9 (I := I) (M := M) h0ω hM hpos P hD
  intro i s x v hsleft hsright
  have hQiω : Q.time i < omega := by
    have hmem := htimeMem i
    rw [hD] at hmem
    exact hmem.2
  have hnonneg :=
    hricOn (Q.time i) (le_of_lt (htime i)) hQiω
  have hscale_ne : ham3BlowupScale (I := I) P Q i ≠ 0 :=
    ne_of_gt (hscale i)
  have hsdiv :
      -Q.time i <= s / ham3BlowupScale (I := I) P Q i := by
    have hdiv := div_le_div_of_nonneg_right hsleft (le_of_lt (hscale i))
    have hcancel :
        -(ham3BlowupScale (I := I) P Q i * Q.time i) /
            ham3BlowupScale (I := I) P Q i = -Q.time i := by
      field_simp [hscale_ne]
    rwa [hcancel] at hdiv
  have htau0 :
      0 <= ham3RescaledTime (I := I) P Q i s := by
    dsimp [ham3RescaledTime]
    linarith
  have htauT :
      ham3RescaledTime (I := I) P Q i s <= Q.time i := by
    dsimp [ham3RescaledTime]
    have hsdiv_nonpos :
        s / ham3BlowupScale (I := I) P Q i <= 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale i))
    linarith
  have htau : ham3RescaledTime (I := I) P Q i s ∈ Set.Icc 0 (Q.time i) :=
    ⟨htau0, htauT⟩
  have hraw := hnonneg (ham3RescaledTime (I := I) P Q i s) htau x v
  simpa [Realized.twoTensorSecToFamily, RicciFlow.SolutionOn.ricci,
    RicciFlow.SolutionOn.ricciAt, RicciFlow.SolutionFamily.ricci,
    RicciFlow.SolutionFamily.ricciAt] using hraw

/-- Positive scalar curvature on the maximal Hamilton flow interval, produced
from the scalar lower-barrier package used in Corollary 7.4. -/
theorem ham3_scalar_pos
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω) :
    ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x := by
  classical
  rcases hM with ⟨hcompact, _hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  rcases ham3_init74 (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont := ham3_cont74 (I := I) (M := M) P c0
  have hc0 : 0 < c0 :=
    RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases ham3_lip74 (I := I) (M := M) P c0 hc0 hcont with
    ⟨K, hK⟩
  have hreg :
      ∀ T : Real, 0 < T -> T < omega ->
        T < RicciFlow.scalarBlowupTime 3 c0 ->
          RicciFlow.ScalarLowerBoundWMPRegularity
            (I := I) (ham3RealFamily (I := I) P) T 3 c0
            (ham3Scalar (I := I) P) (K T) :=
    ham3_reg74 (I := I) (M := M) h0ω P hD c0 hc0 K
  have hevol :
      RicciFlow.ScalarEvolutionEquationOn
        (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
        (ham3Scalar (I := I) P)
        (ham3ScalarLap (I := I) P)
        (ham3RicNormSq (I := I) P) :=
    ham3_evol74 (I := I) (M := M) h0ω P hD
  have hlap :
      ∀ T : Real, 0 < T -> T < omega ->
        T < RicciFlow.scalarBlowupTime 3 c0 ->
          RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
            (I := I) (ham3RealFamily (I := I) P) T
            (ham3Scalar (I := I) P)
            (ham3ScalarLap (I := I) P) := by
    intro T _hT _hTω _hPole
    exact ham3_lap74 (I := I) (M := M) P T
  have hricci :
      ∀ T : Real, 0 < T -> T < omega ->
        T < RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
            (1 / 3 : Real) * (ham3Scalar (I := I) P t x) ^ 2 <=
              ham3RicNormSq (I := I) P t x := by
    intro _T _hT _hTω _hPole t _ht x
    exact ham3_ricBound74 (I := I) (M := M) hdim P t x
  have hF :
      ∀ T : Real, 0 < T -> T < omega ->
        T < RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => RicciFlow.scalarLowerReaction 3 a t)
              (Realized.scalarWMPValueSet (M := M) T
                (ham3Scalar (I := I) P)
                (RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T hT hTω hPole
    exact hK T hT omega hTω hPole
  have hfinite :
      omega <= RicciFlow.scalarBlowupTime 3 c0 := by
    have hfin := RicciFlow.finiteTime3D (I := I) (M := M)
      h0ω (ham3RealFamily (I := I) P) c0
      (ham3Scalar (I := I) P) (ham3ScalarLap (I := I) P)
      (ham3RicNormSq (I := I) P) K hinit_min hinit_pos hcont
      hreg hevol hlap hricci hF
    simpa [RicciFlow.scalarBlowupTime] using hfin.2
  have hlower :
      RicciFlow.ScalarLowerBarrierBoundUpToPole
        (M := M) (ham3Scalar (I := I) P) 3 c0 omega :=
    RicciFlow.scalarLowerBarrierBoundUpToPole_of_scalarEvolution_closedOpen
      (I := I) h0ω (ham3RealFamily (I := I) P) 3 c0 (by norm_num)
      hc0 (ham3Scalar (I := I) P) (ham3ScalarLap (I := I) P)
      (ham3RicNormSq (I := I) P) K hreg hevol hlap hricci
      (RicciFlow.InitialScalarMinimum.lowerBound (M := M) hinit_min) hF
  intro t htD x
  have ht_closed :
      t ∈ (Realized.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    simpa [hD] using htD
  rcases ht_closed with ⟨ht0, htω⟩
  by_cases ht_zero : t = 0
  · have h0 := hinit_pos x
    simpa [ham3Scalar, ham3Solution, ht_zero] using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
    have htblow : t < RicciFlow.scalarBlowupTime 3 c0 :=
      lt_of_lt_of_le htω hfinite
    have hbound :
        RicciFlow.scalarLowerBarrier 3 c0 t <=
          ham3Scalar (I := I) P t x :=
      hlower t htpos htω htblow x
    have hden :
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
      RicciFlow.scalarLowerBarrier_denominator_pos_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 (le_of_lt htpos) htblow
    have hpos_t :
        0 < ham3Scalar (I := I) P t x :=
      RicciFlow.scalar_curvature_positive_of_lower_barrier
        (n := 3) (c0 := c0) (t := t) hbound hc0 hden
    simpa [ham3Scalar, ham3Solution] using hpos_t

/-- Hamilton's pinching improvement along the chosen flow, in the native
domain-aware canonical-field form needed by the Section 12 limit argument. -/
theorem ham3_pinch_imp_can
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (_hric : Ham3RescaledRicNonneg (I := I) P Q)
    (_hsec9 : Ham3Section9Pinch (I := I) P omega) :
    Ham3PinchEstimate (I := I) P := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    simpa using hdim
  have hfixed : Ham3Section9PinchFixed (I := I) P omega :=
    ham3_pinch9_fixed (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hnonneg : Ham3Section9RicNonneg (I := I) P omega :=
    ham3_ric_nonneg9 (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hscalar :
      ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x :=
    ham3_scalar_pos (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ g0 hpos P hD
  rcases RicciFlow.pinchEstimate_sol (I := I) (M := M)
      P.S P.isSmooth h0ω hD hdimT hscalar hfixed hnonneg with
    ⟨epsilon, C, heps0, heps1, hC0, hest⟩
  exact ⟨epsilon, C, heps0, heps1, hC0, hest⟩

/-- Hamilton's pinching improvement along the chosen flow, in the all-real
display form used by older endpoint wrappers. -/
theorem ham3_pinch_imp
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hric : Ham3RescaledRicNonneg (I := I) P Q)
    (hsec9 : Ham3Section9Pinch (I := I) P omega) :
    exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
      RicciFlow.HamiltonTracefreePinchingEstimateOn
        tracefreeRmNormSq scalar weight C := by
  rcases ham3_pinch_imp_can (I := I) (M := M) h0ω hM g0 hpos P hD Q
      hsel hric hsec9 with
    ⟨epsilon, C, _heps0, _heps1, _hC0, hest⟩
  let tracefreeRmNormSq : Real -> M -> Real :=
    RicciFlow.carrierZeroExt (M := M) P.D
      (RicciFlow.tfRicNormSq P.S.scalar (RicciFlow.ricciNorm (I := I) P.S))
  let scalar : Real -> M -> Real :=
    RicciFlow.carrierScalarExt (M := M) P.D P.S.scalar
  let weight : Real -> M -> Real :=
    RicciFlow.carrierWeightExt (M := M) P.D P.S.scalar epsilon
  refine ⟨tracefreeRmNormSq, scalar, weight, C, ?_⟩
  have hdisplay :
      RicciFlow.PinchEstimateOn (M := M) tracefreeRmNormSq scalar weight C Set.univ := by
    simpa [tracefreeRmNormSq, scalar, weight] using
      RicciFlow.pinchEstimate_ext (M := M) (D := P.D) hest
  intro t x
  exact hdisplay t trivial x

/-- Corollary 11.4-style producer: nonnegative Ricci controls the full
curvature tensor on the selected rescaled slabs, with whatever universal
constant the pointwise Corollary 11.4 package supplies. -/
theorem ham3_rm_bound
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (_hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hric : Ham3RescaledRicNonneg (I := I) P Q) :
    exists C : Real, 0 < C /\
      forall (i : Nat) (s : Real) (x : M),
        -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
          ham3RmNormSq (I := I) (M := M) P
              (ham3RescaledTime (I := I) P Q i s) x <=
            C ^ 2 * (ham3BlowupScale (I := I) P Q i) ^ 2 := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  rcases hsel with ⟨hscale, _htime, _htimeMem, _hprod, _hbase, hscalarMax⟩
  refine ⟨100, by norm_num, ?_⟩
  intro i s x hsleft hsright
  let τ : Real := ham3RescaledTime (I := I) P Q i s
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hricNonneg :
      DimensionThree.RicciNonnegAt (I := I) (P.S.ricciAt τ x) := by
    intro v
    simpa [τ, Curvature.vec2, RicciFlow.SolutionOn.ricciAt] using
      hric i s x v hsleft hsright
  have hricSym :
      DimensionThree.RicciSymAt (I := I) (P.S.ricciAt τ x) :=
    RicciFlow.ricciSym_can (I := I) (M := M) P.S τ x
  have hRmScalar :
      ham3RmNormSq (I := I) (M := M) P τ x <=
        (100 : Real) ^ 2 * (ham3Scalar (I := I) P τ x) ^ 2 := by
    have hpoint :=
      DimensionThree.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric τ)
        (Ric := P.S.ricciAt τ x) (scalar := P.S.scalar τ x)
        (Rm04 := P.S.base.rm04 τ x) hdimT hricSym hricNonneg
        (fun basis horth =>
          RicciFlow.traceData_can (I := I) (M := M) P.S horth)
    simpa [ham3RmNormSq, ham3Scalar, ham3Solution, τ] using hpoint
  have hscalarNonneg : 0 <= ham3Scalar (I := I) P τ x := by
    rcases DimensionThree.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric τ) (P.S.ricciAt τ x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        Realized.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar τ x) (P.S.ricciAt τ x) DimensionThree.delta3 basis := by
      have htr :=
        RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric τ)
          (P.S.ricciAt τ x) horth
      simpa [RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar τ x = DimensionThree.ricciEigenScalar3 l1 l2 l3 :=
      RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar τ x
    rw [hscalar_eq]
    unfold DimensionThree.ricciEigenScalar3
    nlinarith
  have hscalarUpper :
      ham3Scalar (I := I) P τ x <= ham3BlowupScale (I := I) P Q i := by
    have hraw := hscalarMax i s x hsleft hsright
    have hmul :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt (hscale i))
    have hleft :
        ham3BlowupScale (I := I) P Q i *
            ham3RescaledScalar (I := I) P Q i s x =
          ham3Scalar (I := I) P τ x := by
      dsimp [ham3RescaledScalar, τ]
      field_simp [ne_of_gt (hscale i)]
    have hright :
        ham3BlowupScale (I := I) P Q i * (1 : Real) =
          ham3BlowupScale (I := I) P Q i := by
      ring
    simpa [hleft, hright] using hmul
  have hscalarSq :
      (ham3Scalar (I := I) P τ x) ^ 2 <=
        (ham3BlowupScale (I := I) P Q i) ^ 2 := by
    have hdiff :
        0 <= ham3BlowupScale (I := I) P Q i -
          ham3Scalar (I := I) P τ x := by
      linarith
    have hsum :
        0 <= ham3BlowupScale (I := I) P Q i +
          ham3Scalar (I := I) P τ x := by
      nlinarith [hscalarNonneg, le_of_lt (hscale i)]
    have hprod :
        0 <=
          (ham3BlowupScale (I := I) P Q i -
              ham3Scalar (I := I) P τ x) *
            (ham3BlowupScale (I := I) P Q i +
              ham3Scalar (I := I) P τ x) :=
      mul_nonneg hdiff hsum
    nlinarith
  have hscaled :
      (100 : Real) ^ 2 * (ham3Scalar (I := I) P τ x) ^ 2 <=
        (100 : Real) ^ 2 * (ham3BlowupScale (I := I) P Q i) ^ 2 :=
    mul_le_mul_of_nonneg_left hscalarSq (by norm_num)
  exact le_trans hRmScalar hscaled

/-- The fixed window `[-r0^2,0]` eventually lies inside each selected rescaled
time interval.  This is just the arithmetic part of the Section 12 argument. -/
theorem ham3_r0_window
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q) :
    Ham3Window (I := I) P Q ham3_r0 := by
  rcases hsel with ⟨_hscale, _htime, _htimeMem, hprod, _hbase, _hscalarMax⟩
  rcases hprod (ham3_r0 ^ 2) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi s hsleft hsright
  have hprod_i :
      ham3_r0 ^ 2 <= ham3BlowupScale (I := I) P Q i * Q.time i := hN i hi
  constructor
  · linarith
  · exact hsright

/-- Black box 11.8-style input: Perelman's no-local-collapsing theorem gives a
uniform volume lower bound at the fixed radius `r0`. -/
theorem ham3_noncollapse
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (_hrm :
      exists C : Real, 0 < C /\
        forall (i : Nat) (s : Real) (x : M),
          -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
            ham3RmNormSq (I := I) (M := M) P
                (ham3RescaledTime (I := I) P Q i s) x <=
              C ^ 2 * (ham3BlowupScale (I := I) P Q i) ^ 2)
    (_hwindow : Ham3Window (I := I) P Q ham3_r0) :
    exists kappa : Real, Ham3Noncollapse (I := I) P Q kappa ham3_r0 := by
  sorry

/-- Black box 11.12-style input: Hamilton compactness produces a pointed smooth
Cheeger-Gromov-Hamilton limit from curvature control and noncollapsing. -/
theorem ham3_cgh_limit
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (_hrm :
      exists C : Real, 0 < C /\
        forall (i : Nat) (s : Real) (x : M),
          -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
            ham3RmNormSq (I := I) (M := M) P
                (ham3RescaledTime (I := I) P Q i s) x <=
              C ^ 2 * (ham3BlowupScale (I := I) P Q i) ^ 2)
    (_hwindow : Ham3Window (I := I) P Q ham3_r0)
    (kappa : Real)
    (_hnoncollapse : Ham3Noncollapse (I := I) P Q kappa ham3_r0) :
    Ham3CGHLimitExists (I := I) P Q := by
  sorry

/-- The midpoint of the fixed backward window is a regular time of the limit
flow once the CGH output includes regularity on the open window. -/
theorem limit_mid_regular
    {L : Ham3CGHLimitData (I := I) M}
    (hreg : Ham3LimitRegWin (I := I) L) :
    -(ham3_r0 ^ 2) / 2 ∈ L.D.regular := by
  apply hreg
  have hsq : 0 < ham3_r0 ^ 2 := sq_pos_of_ne_zero ham3_r0_pos.ne'
  constructor <;> nlinarith

/-- CGH convergence transfers Ricci nonnegativity from the selected rescaled
flows to the smooth limit.

This is a genuine convergence-transfer frontier: the proof should pull back
the Ricci tensors by the CGH maps and pass the pointwise nonnegative quadratic
form inequality to the limit. -/
theorem limit_ric_nonneg
    (_hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (_hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (hric : Ham3RescaledRicNonneg (I := I) P Q)
    {L : Ham3CGHLimitData (I := I) M}
    (htransfer : Ham3RicNonnegTransfer (I := I) P Q L)
    (_hlimit :
      Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L) :
    LimitRicNonneg (I := I) L := by
  exact htransfer hric

/-- The point-selection normalization `R(g_i)(x_i,0)=1` passes to the CGH
base point in the smooth limit. -/
theorem limit_base_scalar_one
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    {L : Ham3CGHLimitData (I := I) M}
    (hconv : Ham3LimitBaseScalarConv (I := I) P Q L) :
    LimitBaseScalarOne (I := I) L := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  rcases hsel with ⟨_hscale, _htime, _htimeMem, _hprod, hbase, _hscalarMax⟩
  let f : Nat -> Real :=
    fun k : Nat =>
      ham3RescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k))
  have hconv' : Filter.Tendsto f Filter.atTop
      (nhds (L.S.scalar 0 L.basepoint)) := by
    simpa [Ham3LimitBaseScalarConv, f] using hconv
  have hconst : Filter.Tendsto f Filter.atTop (nhds (1 : Real)) := by
    have hf : f = fun _ : Nat => (1 : Real) := by
      funext k
      exact hbase (L.subseq k)
    rw [hf]
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => (1 : Real)) Filter.atTop (nhds (1 : Real)))
  have heq : L.S.scalar 0 L.basepoint = 1 :=
    tendsto_nhds_unique hconv' hconst
  simpa [LimitBaseScalarOne] using heq

/-- Ricci nonnegativity gives nonnegative scalar curvature on the limit flow. -/
theorem limit_scalar_nonneg
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hnonneg : LimitRicNonneg (I := I) L) :
    LimitScalarNonneg (I := I) L := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  dsimp [LimitScalarNonneg]
  intro t ht x
  rcases DimensionThree.ricciEigen3 (I := I) (M := L.N)
      (L.S.base.metric t) (L.S.ricciAt t x)
      (by simpa using hdim)
      (RicciFlow.ricciSym_can (I := I) (M := L.N) L.S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hl1 : 0 <= l1 := by
    have h := hnonneg t ht x (basis 0)
    have hcomp := hdiag.2 0 0
    rw [Realized.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (Curvature.vec2 (I := I) (basis 0) (basis 0)) = l1 := by
      simpa [DimensionThree.ricciDiag3] using hcomp
    rwa [hval] at h
  have hl2 : 0 <= l2 := by
    have h := hnonneg t ht x (basis 1)
    have hcomp := hdiag.2 1 1
    rw [Realized.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (Curvature.vec2 (I := I) (basis 1) (basis 1)) = l2 := by
      simpa [DimensionThree.ricciDiag3] using hcomp
    rwa [hval] at h
  have hl3 : 0 <= l3 := by
    have h := hnonneg t ht x (basis 2)
    have hcomp := hdiag.2 2 2
    rw [Realized.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (Curvature.vec2 (I := I) (basis 2) (basis 2)) = l3 := by
      simpa [DimensionThree.ricciDiag3] using hcomp
    rwa [hval] at h
  have hScalarTrace :
      Realized.ScalarRealizesRicciTraceAt (I := I)
        (L.S.scalar t x) (L.S.ricciAt t x) DimensionThree.delta3 basis := by
    have htr :=
      RicciFlow.scalarTrace_delta (I := I) (L.S.base.metric t)
        (L.S.ricciAt t x) horth
    simpa [RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar_eq :
      L.S.scalar t x = DimensionThree.ricciEigenScalar3 l1 l2 l3 :=
    RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
  rw [hscalar_eq]
  unfold DimensionThree.ricciEigenScalar3
  nlinarith

/-- CGH convergence plus the already-checked rescaled scalar/Ricci inputs
produce the concrete limit data used in the final Section 12 argument:
Ricci nonnegativity, base-point scalar normalization, and the pinching
transfer datum. -/
theorem limit_inherit
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (_hric : Ham3RescaledRicNonneg (I := I) P Q)
    (_hcgh : Ham3CGHLimitExists (I := I) P Q) :
    exists L : Ham3CGHLimitData (I := I) M,
      Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L /\
        Ham3RicNonnegTransfer (I := I) P Q L /\
        Ham3PinchTransfer (I := I) P Q L /\
        LimitRicNonneg (I := I) L /\
        LimitBaseScalarOne (I := I) L := by
  rcases _hcgh with
    ⟨L, hsubseq, hwindow, hregwin, hconn, hbdry, hflow,
      hricTransfer, hbaseconv, hpinchTransfer⟩
  have hlimit :
      Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L :=
    ⟨hsubseq, hwindow, hregwin, hconn, hbdry, hflow⟩
  have hnonneg : LimitRicNonneg (I := I) L :=
    limit_ric_nonneg (I := I) (M := M) hM g0 hpos P Q _hsel _hric
      hricTransfer hlimit
  have hbase : LimitBaseScalarOne (I := I) L :=
    limit_base_scalar_one (I := I) (M := M) P Q _hsel hbaseconv
  exact ⟨L, hsubseq, hwindow, hregwin, hconn, hbdry, hflow,
    hricTransfer, hpinchTransfer, hnonneg, hbase⟩

/-- Limit Ricci nonnegativity plus scalar normalization give scalar positivity
on the limit by the scalar strong maximum principle. -/
theorem limit_scal_pos_smp
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : Ham3LimitConnected (I := I) L)
    (hbdry : Ham3LimitBoundaryless (I := I) L)
    (hflow : Ham3LimitFlow (I := I) L)
    (hbase : LimitBaseScalarOne (I := I) L)
    (hcarrier0 : (0 : Real) ∈ L.D.carrier)
    (hricNonneg : LimitRicNonneg (I := I) L)
    (hscalarNonneg : LimitScalarNonneg (I := I) L) :
    LimitScalarPos (I := I) L := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  haveI : ConnectedSpace L.N := by
    simpa [Ham3LimitConnected] using hconn
  haveI : I.Boundaryless := by
    simpa [Ham3LimitBoundaryless] using hbdry
  have hsol : RicciFlow.IsSolutionOn (I := I) L.S := by
    simpa [Ham3LimitFlow] using hflow
  have hdimT : ∀ x : L.N, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    simpa using hdim
  have hricNonneg' :
      ∀ t : Real, t ∈ L.D.carrier → ∀ x : L.N, ∀ v : TangentSpace I x,
        0 ≤ L.S.ricciAt t x (Curvature.vec2 (I := I) v v) := by
    simpa [LimitRicNonneg] using hricNonneg
  have hscalarNonneg' :
      ∀ t : Real, t ∈ L.D.carrier → ∀ x : L.N, 0 ≤ L.S.scalar t x := by
    simpa [LimitScalarNonneg] using hscalarNonneg
  have hbase' : L.S.scalar 0 L.basepoint = 1 := by
    simpa [LimitBaseScalarOne] using hbase
  have hpos : 0 < L.S.scalar 0 L.basepoint := by
    rw [hbase']
    norm_num
  have hposAll :
      ∀ t : Real, t ∈ L.D.carrier → ∀ x : L.N, 0 < L.S.scalar t x :=
    RicciFlow.scalar_strong_maximum_principle (I := I) (M := L.N) L.S hsol
      hdimT hricNonneg' hscalarNonneg' hcarrier0 hpos
  intro t ht x
  exact hposAll t (L.D.regular_subset ht) x

/-- Limit Ricci nonnegativity plus scalar normalization give scalar positivity
on the limit by scalar nonnegativity and the scalar strong maximum principle. -/
theorem limit_scal_pos
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : Ham3LimitConnected (I := I) L)
    (hbdry : Ham3LimitBoundaryless (I := I) L)
    (hflow : Ham3LimitFlow (I := I) L)
    (hnonneg : LimitRicNonneg (I := I) L)
    (hbase : LimitBaseScalarOne (I := I) L)
    (hcarrier0 : (0 : Real) ∈ L.D.carrier) :
    LimitScalarPos (I := I) L := by
  exact limit_scal_pos_smp (I := I) (M := M) hdim hconn hbdry hflow hbase hcarrier0
    hnonneg
    (limit_scalar_nonneg (I := I) (M := M) hdim hnonneg)

/-- The CGH/pinching decay statement is an exact convergence frontier: prove it
from smooth pointed convergence of the rescaled flows, the rescaling rule for
Hamilton's improved pinching estimate, and scalar positivity on compact limit
sets. -/
theorem limit_tf_decay
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {L : Ham3CGHLimitData (I := I) M}
    (htransfer : Ham3PinchTransfer (I := I) P Q L)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (_hlimit :
      Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L)
    (hscalarPos : LimitScalarPos (I := I) L) :
    LimitTfDecay (I := I) L := by
  -- This is the remaining analytic CGH-transfer step: pull back the
  -- scale-invariant trace-free ratio, use the rescaled estimate
  -- `C * R_i^{-ε} * R(g_i)^{-ε}`, and let `i -> ∞`.
  exact htransfer hpinch hscalarPos

/-- Once the pinching estimate has been transferred to arbitrary-small upper
bounds on the CGH limit, nonnegativity of the canonical trace-free Ricci norm
upgrades the decay statement to actual vanishing. -/
theorem limit_tf_zero_of_decay
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hdecay : LimitTfDecay (I := I) L) :
    LimitTfZero (I := I) L := by
  classical
  intro t ht
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  intro x
  let q : Real :=
    RicciFlow.tfRicNormSq L.S.scalar (RicciFlow.ricciNorm (I := I) L.S) t x
  have hnonneg : 0 <= q := by
    have hdimT :
        forall (_t : Real) (y : L.N),
          Module.finrank Real (TangentSpace I y) = 3 := by
      intro _ y
      simpa using hdim
    simpa [q] using
      (RicciFlow.tfNonneg_sol (I := I) (M := L.N) L.S hdimT t x)
  have hle0 : q <= 0 := by
    have hforall : forall ε : Real, 0 < ε -> q <= 0 + ε := by
      intro ε hε
      simpa [q] using hdecay t ht x ε hε
    exact le_of_forall_pos_le_add hforall
  simpa [q] using le_antisymm hle0 hnonneg

/-- The Section 10 improved pinching estimate passes to the smooth CGH limit
and kills the trace-free Ricci part. -/
theorem limit_tf_zero
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {L : Ham3CGHLimitData (I := I) M}
    (htransfer : Ham3PinchTransfer (I := I) P Q L)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (_hlimit :
      Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L)
    (_hscalarPos : LimitScalarPos (I := I) L) :
    LimitTfZero (I := I) L := by
  exact limit_tf_zero_of_decay (I := I) (M := M) hdim
    (limit_tf_decay (I := I) (M := M) P Q htransfer hpinch _hlimit _hscalarPos)

/-- Vanishing trace-free Ricci norm gives the pointwise Einstein equation
`Ric = (R / 3) g` at that time. -/
theorem limitEinstein_of_tf0
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    {t0 : Real} (htf : LimitTfZeroAt (I := I) L t0) :
    LimitEinsteinAt (I := I) L t0 := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  intro x v w
  let g := L.S.base.metric t0
  let Ric := L.S.ricciAt t0 x
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hsym : DimensionThree.RicciSymAt (I := I) (M := L.N) Ric :=
    RicciFlow.ricciSym_can (I := I) (M := L.N) L.S t0 x
  rcases DimensionThree.ricciEigen3 (I := I) (M := L.N) g Ric hdimT hsym with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    RicciFlow.scalarTrace_delta (I := I) (M := L.N) g Ric horth
  have hscalar :
      L.S.scalar t0 x = DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
    calc
      L.S.scalar t0 x =
          Realized.metricTracePair0SAt (I := I) (M := L.N)
            (L.S.family.metric t0) (L.S.ricciAt t0 x) :=
            RicciFlow.SolutionOn.scalar_eq_metricTrace (I := I) (M := L.N)
              L.S t0 x
      _ = Realized.metricTracePair0SAt (I := I) (M := L.N) g Ric := by
            rfl
      _ = DimensionThree.ricciEigenScalar3 l1 l2 l3 := by
            exact RicciFlow.scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
        DimensionThree.delta3 :=
    DimensionThree.orthonormal_invBasis3 (I := I) (M := L.N) g basis horth
  have hnorm :
      RicciFlow.ricciNorm (I := I) L.S t0 x =
        RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
    calc
      RicciFlow.ricciNorm (I := I) L.S t0 x =
          Tensor0SBundle.normSq0S (I := I) (M := L.N) g x 2 Ric := by
            rfl
      _ = RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
            exact (RicciFlow.ricciNorm_inner (I := I) (M := L.N)
              g Ric basis hinv).symm
  have htf_eigen :
      DimensionThree.tracefreeRicciEigenNormSq3 l1 l2 l3 = 0 := by
    have htf_x := htf x
    rw [RicciFlow.tfRicNormSq, RicciFlow.tracefreeRicciNormSqOf,
      hscalar, hnorm,
      RicciFlow.ricciNormAt_diag (I := I) (M := L.N) hdiag] at htf_x
    simpa [RicciFlow.tfRicNormSqAt, RicciFlow.tfRic_eigen] using htf_x
  have heq :=
    (DimensionThree.tracefreeRicciEigenNormSq3_eq_zero_iff l1 l2 l3).1
      htf_eigen
  rcases heq with ⟨h12, h23⟩
  have hscalar_l1 : L.S.scalar t0 x / 3 = l1 := by
    rw [hscalar, h12, h23]
    unfold DimensionThree.ricciEigenScalar3
    ring
  let T := DimensionThree.ricciEndAt (I := I) (M := L.N) g Ric
  rcases RicciFlow.ricciEnd_diagVec (I := I) (M := L.N) g
      (Ric := Ric) horth hdiag with
    ⟨hT0, hT1, hT2⟩
  have hT_basis : forall i : Fin 3, T (basis i) = l1 • basis i := by
    intro i
    fin_cases i
    · simpa [T] using hT0
    · simpa [T, h12] using hT1
    · simpa [T, h12, h23] using hT2
  have hT_all : T v = l1 • v := by
    calc
      T v = T (∑ i : Fin 3, basis.repr v i • basis i) := by
        rw [basis.sum_repr]
      _ = ∑ i : Fin 3, T (basis.repr v i • basis i) := by
        exact map_sum T (fun i : Fin 3 => basis.repr v i • basis i) Finset.univ
      _ = ∑ i : Fin 3, basis.repr v i • T (basis i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp
      _ = ∑ i : Fin 3, basis.repr v i • (l1 • basis i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hT_basis i]
      _ = l1 • (∑ i : Fin 3, basis.repr v i • basis i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [smul_smul, mul_comm]
      _ = l1 • v := by
        rw [basis.sum_repr]
  calc
    L.S.ricciAt t0 x (Curvature.vec2 (I := I) v w) =
        g.inner x (T v) w := by
          exact (DimensionThree.ricciEnd_inner (I := I) (M := L.N) g Ric v w).symm
    _ = g.inner x (l1 • v) w := by rw [hT_all]
    _ = l1 * g.inner x v w := by simp
    _ = (L.S.scalar t0 x / 3) * (L.S.base.metric t0).inner x v w := by
          rw [hscalar_l1]

/-- Static Schur/space-form frontier for the Section 12 limit: a connected
three-dimensional limit metric whose Ricci tensor satisfies `Ric = (R / 3) g`
and whose scalar is positive at the selected time has constant positive
sectional curvature.

The remaining proof should use the static metric Bianchi package to prove the
Einstein factor is constant, then the three-dimensional Riemann-from-Ricci
component bridge with the RicciFlower slot convention. -/
theorem limit_const_sec_of_einstein
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : Ham3LimitConnected (I := I) L)
    (hbdry : Ham3LimitBoundaryless (I := I) L)
    (_hflow : Ham3LimitFlow (I := I) L)
    {t0 : Real} (_ht0 : t0 ∈ L.D.regular)
    (hscalar : LimitScalarPosAt (I := I) L t0)
    (heinstein : LimitEinsteinAt (I := I) L t0) :
    LimitConstPosSec (I := I) L := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  haveI : ConnectedSpace L.N := by
    simpa [Ham3LimitConnected] using hconn
  haveI : I.Boundaryless := by
    simpa [Ham3LimitBoundaryless] using hbdry
  let g : SmoothRiemannianMetric I L.N := L.S.base.metric t0
  have hEinStatic :
      ∀ y : L.N, ∀ v w : TangentSpace I y,
        Curvature.metricRicciAt (I := I) (M := L.N) g y
            (Realized.vec2 (I := I) v w) =
          (Curvature.metricScalarAt (I := I) (M := L.N) g y / 3) *
            g.inner y v w := by
    intro y v w
    have h := heinstein y v w
    simpa [g, LimitEinsteinAt, RicciFlow.SolutionOn.ricciAt,
      RicciFlow.SolutionFamily.ricciAt, RicciFlow.metricRicciAt,
      RicciFlow.SolutionOn.scalar, RicciFlow.SolutionFamily.scalar,
      RicciFlow.metricScalarAt] using h
  have hdScalar :
      ∀ x : L.N, ∀ X : TangentSpace I x,
        Realized.differential1FormFun (I := I)
            (fun y : L.N =>
              Curvature.metricScalarAt (I := I) (M := L.N) g y)
            x (fun _ : Fin 1 => X) = 0 := by
    intro x X
    have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
      simpa using hdim
    have hsym : DimensionThree.RicciSymAt (I := I)
        (L.S.ricciAt t0 x) :=
      RicciFlow.ricciSym_can (I := I) (M := L.N) L.S t0 x
    rcases DimensionThree.ricciEigen3 (I := I) (M := L.N) g
        (L.S.ricciAt t0 x) hdimT hsym with
      ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
    have hinv :
        Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
          DimensionThree.delta3 :=
      DimensionThree.orthonormal_invBasis3 (I := I) (M := L.N) g basis horth
    exact Curvature.dScalar_zero_ein3_at (I := I) (M := L.N) g basis
      DimensionThree.delta3 hinv hEinStatic X
  rcases Curvature.metricScalar_const_of_dScalar_zero (I := I) (M := L.N) g
      hdScalar with
    ⟨R0, hR0_metric⟩
  have hR0_scalar : ∀ x : L.N, L.S.scalar t0 x = R0 := by
    intro x
    have hx := hR0_metric x
    simpa [g, RicciFlow.SolutionOn.scalar, RicciFlow.SolutionFamily.scalar,
      RicciFlow.metricScalarAt] using hx
  have hR0_pos : 0 < R0 := by
    have hb := hscalar L.basepoint
    rw [hR0_scalar L.basepoint] at hb
    exact hb
  refine ⟨g, R0 / 6, by nlinarith, ?_⟩
  intro x X Y
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hsym : DimensionThree.RicciSymAt (I := I)
      (L.S.ricciAt t0 x) :=
    RicciFlow.ricciSym_can (I := I) (M := L.N) L.S t0 x
  rcases DimensionThree.ricciEigen3 (I := I) (M := L.N) g
      (L.S.ricciAt t0 x) hdimT hsym with
    ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
  have htrace :=
    RicciFlow.traceData_can (I := I) (M := L.N) L.S
      (t := t0) (x := x) (basis := basis) horth
  have hEinCompNeg : ∀ i j : Fin 3,
      Realized.ricciCompAt (I := I) basis (-(L.S.ricciAt t0 x)) i j =
        ((-L.S.scalar t0 x) / 3) * DimensionThree.delta3 i j := by
    intro i j
    have hij := heinstein x (basis i) (basis j)
    rw [Realized.ricciCompAt_apply]
    change -(L.S.ricciAt t0 x
        (Curvature.vec2 (I := I) (basis i) (basis j))) =
      ((-L.S.scalar t0 x) / 3) * DimensionThree.delta3 i j
    rw [hij]
    rw [horth i j]
    ring
  have hRm :=
    DimensionThree.rm04_einstein3_at (I := I) (M := L.N) htrace
      hEinCompNeg X Y
  have hscalar_x : L.S.scalar t0 x = R0 := hR0_scalar x
  calc
    Curvature.metricRm04StdAt (I := I) (M := L.N) g x X Y Y X =
        L.S.base.rm04 t0 x (Curvature.vec4 (I := I) X Y Y X) := by
          rfl
    _ = -((-L.S.scalar t0 x) / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := hRm
    _ = (R0 / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := by
          rw [hscalar_x]
          ring

/-- Pointwise 3D algebra/geometric frontier behind the final constant-curvature
step: at one regular time, positive scalar plus vanishing trace-free Ricci
forces a constant positive sectional-curvature metric. -/
theorem const_pos_of_tf0
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : Ham3LimitConnected (I := I) L)
    (hbdry : Ham3LimitBoundaryless (I := I) L)
    (hflow : Ham3LimitFlow (I := I) L)
    {t0 : Real} (ht0 : t0 ∈ L.D.regular)
    (hscalar : LimitScalarPosAt (I := I) L t0)
    (htf : LimitTfZeroAt (I := I) L t0) :
    LimitConstPosSec (I := I) L := by
  have heinstein : LimitEinsteinAt (I := I) L t0 :=
    limitEinstein_of_tf0 (I := I) (M := M) hdim htf
  exact limit_const_sec_of_einstein (I := I) (M := M) hdim hconn hbdry hflow ht0
    hscalar heinstein

/-- In dimension three, a smooth limit flow with positive scalar curvature and
vanishing trace-free Ricci on the regular backward window has constant positive
sectional curvature. -/
theorem limit_const_pos
    {L : Ham3CGHLimitData (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hreg : Ham3LimitRegWin (I := I) L)
    (hconn : Ham3LimitConnected (I := I) L)
    (hbdry : Ham3LimitBoundaryless (I := I) L)
    (hflow : Ham3LimitFlow (I := I) L)
    (hscalarPos : LimitScalarPos (I := I) L)
    (htf : LimitTfZero (I := I) L) :
    LimitConstPosSec (I := I) L := by
  let t0 : Real := -(ham3_r0 ^ 2) / 2
  have ht0 : t0 ∈ L.D.regular := by
    simpa [t0] using limit_mid_regular (I := I) (M := M) hreg
  exact const_pos_of_tf0 (I := I) (M := M) hdim hconn hbdry hflow ht0
    (hscalarPos t0 ht0) (htf t0 ht0)

/-- Myers/compactness and the eventual diffeomorphism in the CGH convergence
transfer a constant-positive-sectional metric on the limit back to `M`. -/
theorem limit_to_orig
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {L : Ham3CGHLimitData (I := I) M}
    (_hcgh :
      Ham3LimitSubseq (I := I) L /\
        Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L)
    (_hconst : LimitConstPosSec (I := I) L) :
    exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf := by
  sorry

/-- Pinching plus the smooth CGH limit and the compact-limit transfer step
produce a constant-positive-sectional metric on the original manifold. -/
theorem ham3_limit_const_metric
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hric : Ham3RescaledRicNonneg (I := I) P Q)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (hcgh : Ham3CGHLimitExists (I := I) P Q) :
    exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf := by
  have hdim : Module.finrank Real E = 3 := hM.2.2.2
  rcases limit_inherit (I := I) (M := M) hM g0 hpos P Q hsel hric hcgh with
    ⟨L, hsubseq, hwindow, hregwin, hconn, hbdry, hflow,
      _hricTransfer, hpinchTransfer, hnonneg, hbase⟩
  have hlimit :
      Ham3LimitSubseq (I := I) L /\
        Ham3LimitWindow (I := I) L /\
        Ham3LimitRegWin (I := I) L /\
        Ham3LimitConnected (I := I) L /\
        Ham3LimitBoundaryless (I := I) L /\
        Ham3LimitFlow (I := I) L :=
    ⟨hsubseq, hwindow, hregwin, hconn, hbdry, hflow⟩
  have hcarrier0 : (0 : Real) ∈ L.D.carrier := by
    apply hwindow
    constructor
    · nlinarith [sq_nonneg ham3_r0]
    · exact le_rfl
  have hscalarPos : LimitScalarPos (I := I) L :=
    limit_scal_pos (I := I) (M := M) hdim hconn hbdry hflow hnonneg hbase hcarrier0
  have htf : LimitTfZero (I := I) L :=
    limit_tf_zero (I := I) (M := M) hdim P Q hpinchTransfer hpinch hlimit hscalarPos
  have hconst : LimitConstPosSec (I := I) L :=
    limit_const_pos (I := I) (M := M) hdim hregwin hconn hbdry hflow hscalarPos htf
  exact limit_to_orig (I := I) (M := M) hM P Q hlimit hconst

/-- If a limiting constant-positive-sectional metric has been produced, then
`M` admits such a metric. -/
theorem ham3_const_of_limit
    (hlim : exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf) :
    AdmitsConstPosSec (I := I) (M := M) := by
  exact hlim

/-- Consumer endpoint: the global Ricci-flow package gives a constant positive
sectional-curvature metric. -/
theorem ham3_const_metric
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
  AdmitsConstPosSec (I := I) (M := M) := by
  rcases hpos with ⟨g0, hg0⟩
  rcases ham3_flow_exists_normalized (I := I) (M := M) hM g0 hg0 with
    ⟨omega, h0ω, P, hD⟩
  have hfinite_core : exists c0 : Real, 0 < c0 /\ omega <= 3 / (2 * c0) :=
    ham3_finite_time (I := I) (M := M) h0ω hM g0 hg0 P hD
  have hfinite :
      exists omega c0 : Real, exists h0ω : 0 < omega,
        P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω /\
          0 < c0 /\ omega <= 3 / (2 * c0) := by
    rcases hfinite_core with ⟨c0, hc0, hbound⟩
    exact ⟨omega, c0, h0ω, hD, hc0, hbound⟩
  have hnonneg9 : Ham3Section9RicNonneg (I := I) P omega :=
    ham3_ric_nonneg9 (I := I) (M := M) h0ω hM hg0 P hD
  have hscalarBlow : Ham3ScalarBlowup (I := I) P :=
    ham3_scalar_blowup (I := I) (M := M) h0ω hM P hD hnonneg9
  rcases ham3_point_select (I := I) (M := M) hM g0 hg0 P hfinite
      hscalarBlow with
    ⟨Q, hsel⟩
  have hric : Ham3RescaledRicNonneg (I := I) P Q :=
    ham3_rescaled_ric_nonneg (I := I) (M := M) h0ω hM g0 hg0 P hD Q hsel
  have hsec9 : Ham3Section9Pinch (I := I) P omega :=
    ham3_pinch9 (I := I) (M := M) h0ω hM hg0 P hD
  have hpinch : Ham3PinchEstimate (I := I) P :=
    ham3_pinch_imp_can (I := I) (M := M) h0ω hM g0 hg0 P hD Q hsel hric hsec9
  have hrm :
      exists C : Real, 0 < C /\
        forall (i : Nat) (s : Real) (x : M),
          -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
            ham3RmNormSq (I := I) (M := M) P
                (ham3RescaledTime (I := I) P Q i s) x <=
              C ^ 2 * (ham3BlowupScale (I := I) P Q i) ^ 2 :=
    ham3_rm_bound (I := I) (M := M) hM g0 hg0 P Q hsel hric
  have hwindow : Ham3Window (I := I) P Q ham3_r0 :=
    ham3_r0_window (I := I) P Q hsel
  rcases ham3_noncollapse (I := I) (M := M) hM g0 hg0 P Q hsel hrm hwindow with
    ⟨kappa, hnoncollapse⟩
  have hcgh : Ham3CGHLimitExists (I := I) P Q :=
    ham3_cgh_limit (I := I) (M := M) hM g0 hg0 P Q hsel hrm hwindow
      kappa hnoncollapse
  have hlim :
      exists gInf : SmoothRiemannianMetric I M,
        ConstPosSecMetric (I := I) (M := M) gInf :=
    ham3_limit_const_metric (I := I) (M := M) hM g0 hg0 P Q hsel hric hpinch hcgh
  exact ham3_const_of_limit (I := I) (M := M) hlim

/-- Topological/global geometry black box: a closed connected smooth
three-manifold with a constant positive sectional-curvature metric is a
spherical space form. -/
theorem ham3_space_box
    (hM : Closed3Manifold (I := I) (M := M))
    (hconst : AdmitsConstPosSec (I := I) (M := M)) :
    SphericalSpaceForm (I := I) (M := M) := by
  sorry

/-- A spherical-space-form model carries a constant positive sectional-curvature
metric.

Mathematically this is the direct construction: take the round metric on
`S^3`, descend it through the finite free isometric quotient, and pull it back
to `M` along the smooth equivalence stored in
`IsSphericalSpaceFormQuotient`. -/
theorem spaceForm_const_metric
    (model : IsSphericalSpaceFormQuotient I M) :
    AdmitsConstPosSec (I := I) (M := M) := by
  sorry

/-- Reverse presentation direction of the standard equivalence, obtained by
the quotient round metric construction. -/
theorem ham3_const_box
    (hM : Closed3Manifold (I := I) (M := M))
    (hsph : SphericalSpaceForm (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) := by
  have _hclosed : Closed3Manifold (I := I) (M := M) := hM
  exact spaceForm_const_metric (I := I) (M := M) hsph

/-- The theorem-facing equivalence between constant positive sectional
curvature and spherical space-form topology. -/
theorem ham3_equiv
    (hM : Closed3Manifold (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) <-> SphericalSpaceForm (I := I) (M := M) := by
  constructor
  · exact ham3_space_box (I := I) (M := M) hM
  · exact ham3_const_box (I := I) (M := M) hM

/-- Hamilton's theorem in dimension three, Theorem 2.1 in the Hamilton
blueprint: positive initial Ricci curvature implies existence of a constant
positive sectional-curvature metric, equivalently spherical space-form
topology. -/
theorem ham3_main
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) /\ SphericalSpaceForm (I := I) (M := M) := by
  have hconst : AdmitsConstPosSec (I := I) (M := M) :=
    ham3_const_metric (I := I) (M := M) hM hpos
  exact ⟨hconst, (ham3_equiv (I := I) (M := M) hM).1 hconst⟩

/-- Label alias for the LaTeX theorem `thm:main-hamilton-3d`. -/
theorem thm_2_1
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) /\ SphericalSpaceForm (I := I) (M := M) :=
  ham3_main (I := I) (M := M) hM hpos

end HamiltonPositiveRicci
end RicciFlower
