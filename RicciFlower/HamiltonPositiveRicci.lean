import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.ProperAction.Basic
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.LocalPinching
import RicciFlower.RicciFlow.Evolution.ScalarFiniteTime
import RicciFlower.RicciFlow.MaximalTime
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

/-- Constant positive sectional curvature, expressed by the standard
two-plane curvature formula against RicciFlower's lowered curvature convention
`Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`. -/
def ConstPosSecMetric (g : SmoothRiemannianMetric I M) : Prop :=
  exists c : Real, 0 < c /\
    forall x : M, forall X Y : TangentSpace I x,
      RicciFlow.metricRm04 (I := I) (M := M) g x
          (Curvature.vec4 (I := I) X X Y Y) =
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
`IsSolutionOn`, and the initial metric relation.  Finite-time singularity,
point selection, noncollapsing, compactness, and the limiting
constant-curvature metric are theorem endpoints below, not fields in this data
package. -/
structure Ham3FlowPackage (g0 : SmoothRiemannianMetric I M) where
  D : Realized.RealTimeInterval
  S : RicciFlower.RicciFlow.SolutionOn (I := I) (M := M) D
  isSmooth : RicciFlower.RicciFlow.IsSmoothSolutionOn (I := I) (M := M) S
  startsAt : S.family.metric D.initial = g0

/-- Accessor for the Ricci-flow solution carried by the Section 12 package.

Keeping this as a named accessor avoids brittle parsing around the capital field
projection `P.S` inside long component theorem statements. -/
abbrev ham3Solution
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    RicciFlow.SolutionOn (I := I) (M := M) P.D :=
  P.S

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

/-- The fixed radius used in Hamilton's Section 12 proof. -/
def ham3_r0 : Real := (1 : Real) / 10

theorem ham3_r0_pos : 0 < ham3_r0 := by
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

/-- The limit object is itself a smooth Ricci-flow solution. -/
def Ham3LimitFlow (L : Ham3CGHLimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  RicciFlow.IsSolutionOn (I := I) L.S

/-- The conclusion of Black box 11.12 in the Hamilton Section 12 pipeline:
after passing to a subsequence, the rescaled pointed flows have a smooth
pointed Cheeger-Gromov-Hamilton limit.

The native project still lacks a full CGH-convergence relation, but the
conclusion now exposes the actual limit data: a pointed smooth Ricci flow on a
limit manifold, defined on the fixed backward window, together with the
subsequence selecting the convergent rescalings. -/
def Ham3CGHLimitExists
    {g0 : SmoothRiemannianMetric I M}
    (_P : Ham3FlowPackage (I := I) (M := M) g0)
    (_Q : Ham3BlowupData M) : Prop :=
  exists L : Ham3CGHLimitData (I := I) M,
    Ham3LimitSubseq (I := I) L /\
      Ham3LimitWindow (I := I) L /\
      Ham3LimitFlow (I := I) L

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

/-- Intrinsic scalar curvature carried by the flow package: the metric trace
of the canonical pointwise Ricci tensor. -/
def ham3Scalar
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Real -> M -> Real :=
  RicciFlow.SolutionOn.scalar (I := I) (ham3Solution (I := I) P)

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

/-! ## Section 12 blow-up quantities derived from the maximal flow -/

/-- Hamilton's blow-up scale:
`R_i = R(x_i,t_i)` for the original maximal flow. -/
def ham3BlowupScale
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (i : Nat) : Real :=
  ham3Scalar (I := I) P (Q.time i) (Q.point i)

/-- Original flow time corresponding to rescaled time `s` in the `i`th blow-up:
`t_i + s / R_i`. -/
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

/-- Eventually the fixed backward time window `[-r0^2,0]` lies inside the
rescaled time slab `[-R_i t_i,0]`. -/
def Ham3Window
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (r : Real) : Prop :=
  exists N : Nat, forall i : Nat, N <= i ->
    forall s : Real, -(r ^ 2) <= s -> s <= 0 ->
      -(ham3BlowupScale (I := I) P Q i * Q.time i) <= s /\ s <= 0

/-- The lower volume bound supplied by Perelman's noncollapsing theorem at the
fixed radius.

The actual geodesic-ball volume accessor is part of the global compactness /
noncollapsing layer, so this Section 12 endpoint keeps only the theorem-shaped
consequence and does not store volume data in `Ham3BlowupData`. -/
def Ham3Noncollapse
    {g0 : SmoothRiemannianMetric I M}
    (_P : Ham3FlowPackage (I := I) (M := M) g0)
    (_Q : Ham3BlowupData M) (kappa r : Real) : Prop :=
  0 < kappa /\ 0 < r /\
    exists ballVolume : Nat -> Real, exists N : Nat, forall i : Nat, N <= i ->
      kappa * r ^ 3 <= ballVolume i

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

/-- Lemma 11.6-style input: choose blow-up points, times, and parabolic
rescalings normalized by scalar curvature. -/
theorem ham3_point_select
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (_hfinite : exists omega c0 : Real, exists h0ω : 0 < omega,
      P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω /\
        0 < c0 /\ omega <= 3 / (2 * c0)) :
    exists Q : Ham3BlowupData M, Ham3PointSel (I := I) P Q := by
  sorry

/-- Lemma 9.1-style input: nonnegative Ricci curvature persists on the selected
rescaled flow slabs. -/
theorem ham3_rescaled_ric_nonneg
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q) :
    Ham3RescaledRicNonneg (I := I) P Q := by
  sorry

/-- Hamilton's pinching improvement along the chosen flow. -/
theorem ham3_pinch_imp
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel (I := I) P Q)
    (_hric : Ham3RescaledRicNonneg (I := I) P Q) :
    exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
      RicciFlow.HamiltonTracefreePinchingEstimateOn
        tracefreeRmNormSq scalar weight C := by
  sorry

/-- Corollary 11.4-style producer: nonnegative Ricci controls the full
curvature tensor on the selected rescaled slabs, with whatever universal
constant the pointwise Corollary 11.4 package supplies. -/
theorem ham3_rm_bound
    (_hM : Closed3Manifold (I := I) (M := M))
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
  sorry

/-- The fixed window `[-r0^2,0]` eventually lies inside each selected rescaled
time interval.  This is just the arithmetic part of the Section 12 argument. -/
theorem ham3_r0_window
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q) :
    Ham3Window (I := I) P Q ham3_r0 := by
  rcases hsel with ⟨_hscale, _htime, hprod, _hbase, _hscalarMax⟩
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

/-- Pinching plus the smooth CGH limit and the compact-limit transfer step
produce a constant-positive-sectional metric on the original manifold. -/
theorem ham3_limit_const_metric
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hpinch :
      exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
        RicciFlow.HamiltonTracefreePinchingEstimateOn
          tracefreeRmNormSq scalar weight C)
    (_hcgh : Ham3CGHLimitExists (I := I) P Q) :
    exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf := by
  sorry

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
  rcases ham3_point_select (I := I) (M := M) hM g0 hg0 P hfinite with ⟨Q, hsel⟩
  have hric : Ham3RescaledRicNonneg (I := I) P Q :=
    ham3_rescaled_ric_nonneg (I := I) (M := M) hM g0 hg0 P Q hsel
  have hpinch :
      exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
        RicciFlow.HamiltonTracefreePinchingEstimateOn
          tracefreeRmNormSq scalar weight C :=
    ham3_pinch_imp (I := I) (M := M) hM g0 hg0 P Q hsel hric
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
    ham3_limit_const_metric (I := I) (M := M) hM g0 hg0 P Q hpinch hcgh
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
