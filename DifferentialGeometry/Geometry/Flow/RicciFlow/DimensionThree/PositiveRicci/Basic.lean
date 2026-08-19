import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicciHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.QuotientEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.HamiltonReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicciEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.SolutionEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.IntrinsicEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Estimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.MaximalFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.RicciPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.EarlyTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ScaleTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.RicciFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedGlobal
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Headlines
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Geometry.Metric.Sphere.PositiveSpaceForm
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def Closed3Manifold : Prop :=
  CompactSpace M /\ ConnectedSpace M /\ I.Boundaryless /\
    Module.finrank Real E = 3

def PosRicciMetric (g : SmoothRiemannianMetric I M) : Prop :=
  forall x : M, forall v : TangentSpace I x, v ≠ 0 ->
    0 < DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := M) g x
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

def AdmitsPosRicci : Prop :=
  exists g : SmoothRiemannianMetric I M, PosRicciMetric (I := I) (M := M) g

def ConstPosSecMetric (g : SmoothRiemannianMetric I M) : Prop :=
  exists c : Real, 0 < c /\
    forall x : M, forall X Y : TangentSpace I x,
      DifferentialGeometry.Geometry.Curvature.metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)

def AdmitsConstPosSec : Prop :=
  exists g : SmoothRiemannianMetric I M, ConstPosSecMetric (I := I) (M := M) g

instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

structure SphericalSpaceFormQuotientModel
    (I : ModelWithCorners Real E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Type _ where
  data : Geometry.RoundQuotientData.{0, u, u} (EuclideanSpace Real (Fin 4)) 3
  equiv : N ≃ₘ⟮I, 𝓡 3⟯ data.Q

def IsSphericalSpaceFormQuotient
    (I : ModelWithCorners Real E H) (N : Type u)
    [TopologicalSpace N] [ChartedSpace H N] : Prop :=
  Nonempty (SphericalSpaceFormQuotientModel I N)

def SphericalSpaceForm : Prop :=
  IsSphericalSpaceFormQuotient I M

def hamiltonMetricConnectionFamilyCore
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (g0 : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun t => by
    classical
    exact if _ht : t ∈ D.carrier then S.family.metric t else g0
  connection := fun t => by
    classical
    exact
      if _ht : t ∈ D.carrier then S.family.connection t
      else DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g0
  metricCompatible := by
    intro t
    classical
    by_cases ht : t ∈ D.carrier
    · simpa [ht] using S.family.metricCompatible ⟨t, ht⟩
    · simpa [ht] using
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
          (I := I) g0)

structure HamiltonFiniteTimeFlow (g0 : SmoothRiemannianMetric I M) where
  D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval
  S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSmooth : DifferentialGeometry.PDE.RicciFlow.IsSmoothSolutionOn (I := I) (M := M) S
  startsAt : S.family.metric D.initial = g0
  curvUnbounded : forall K : Real, exists t : Real, exists x : M,
    t ∈ D.carrier /\
      K < Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4
        (S.base.rm04 t x)

abbrev hamiltonSolution
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) P.D :=
  P.S

def hamiltonScalar
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar (I := I) (hamiltonSolution (I := I) P)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_space_time_continuous
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.PDE.RicciFlow.ScalarSTContOn
      (I := I) (M := M) (hamiltonSolution (I := I) (M := M) P) := by
  exact P.isSmooth.scalarSTCont

def hamiltonRiemannNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I)
      ((hamiltonSolution (I := I) (M := M) P).family.metric t) x 4
      (((hamiltonSolution (I := I) (M := M) P).base.rm04 t) x)

structure HamiltonBlowup (M : Type*) where
  point : Nat -> M
  time : Nat -> Real

def hamiltonBlowupScale
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) : Real :=
  hamiltonScalar (I := I) P (Q.time i) (Q.point i)

def hamiltonRescaledTime
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) (s : Real) : Real :=
  Q.time i + s / hamiltonBlowupScale (I := I) P Q i

def hamiltonRescaledScalar
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) (s : Real) (x : M) : Real :=
  (hamiltonBlowupScale (I := I) P Q i)⁻¹ *
    hamiltonScalar (I := I) P (hamiltonRescaledTime (I := I) P Q i s) x

def hamilton_reference_radius : Real := (1 : Real) / 10

theorem hamilton_reference_radius_pos : 0 < hamilton_reference_radius := by
  norm_num [hamilton_reference_radius]

theorem hamilton_reference_radius_le_one : hamilton_reference_radius ≤ (1 : Real) := by
  norm_num [hamilton_reference_radius]

theorem hamilton_reference_radius_inverse_sq : (100 : Real) = (hamilton_reference_radius⁻¹) ^ 2 := by
  norm_num [hamilton_reference_radius]

structure HamiltonCGHLimit (I : ModelWithCorners Real E H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M] where
  N : Type u
  [topology : TopologicalSpace N]
  [charted : ChartedSpace H N]
  [smooth : IsManifold I ∞ N]
  [smooth_plus : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
  [sigmaCompact : SigmaCompactSpace N]
  [t2 : T2Space N]
  [t2TangentBundle : T2Space (TangentBundle I N)]
  basepoint : N
  D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval
  S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := N) D
  isSolution : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S
  sourceTerm : Nat ->
    DifferentialGeometry.HCGCompactness.PointedFlowData.{u} (I := I) D
  origIndex : Nat -> Nat
  origStrict : StrictMono origIndex
  cghSubseq : Nat -> Nat
  cghStrict : StrictMono cghSubseq
  cgh : DifferentialGeometry.HCGCompactness.SmoothCGHConverges
    (I := I)
    { D := D, term := sourceTerm }
    { M := N, topology := topology, charted := charted, smooth := smooth,
      sigmaCompact := sigmaCompact, t2 := t2,
      t2TangentBundle := t2TangentBundle, basepoint := basepoint,
      S := S, isSolution := isSolution }
    cghSubseq
  sourceToOrig : forall i : Nat,
    letI : TopologicalSpace (sourceTerm i).M := (sourceTerm i).topology
    letI : ChartedSpace H (sourceTerm i).M := (sourceTerm i).charted
    (sourceTerm i).M ≃ₘ⟮I, I⟯ M
  limitComplete : forall t : Real, t ∈ D.carrier ->
    DifferentialGeometry.HCGCompactness.MetricComplete (I := I)
      { M := N, topology := topology, charted := charted, smooth := smooth,
        sigmaCompact := sigmaCompact, t2 := t2,
        t2TangentBundle := t2TangentBundle, basepoint := basepoint,
        metric := S.base.metric t }

namespace HamiltonCGHLimit

abbrev source (L : HamiltonCGHLimit (I := I) M) :
    DifferentialGeometry.HCGCompactness.PointedFlowSeq.{u} (I := I) :=
  { D := L.D, term := L.sourceTerm }

abbrev limit (L : HamiltonCGHLimit (I := I) M) :
    DifferentialGeometry.HCGCompactness.PointedFlowData.{u} (I := I) L.D :=
  { M := L.N, topology := L.topology, charted := L.charted, smooth := L.smooth,
    sigmaCompact := L.sigmaCompact, t2 := L.t2,
    t2TangentBundle := L.t2TangentBundle, basepoint := L.basepoint,
    S := L.S, isSolution := L.isSolution }

def subseq (L : HamiltonCGHLimit (I := I) M) : Nat -> Nat :=
  fun k => L.origIndex (L.cghSubseq k)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem subseq_strict (L : HamiltonCGHLimit (I := I) M) :
    StrictMono L.subseq :=
  L.origStrict.comp L.cghStrict

end HamiltonCGHLimit

def HamiltonLimitSubsequence (L : HamiltonCGHLimit (I := I) M) : Prop :=
  StrictMono L.subseq

def HamiltonLimitWindow (L : HamiltonCGHLimit (I := I) M) : Prop :=
  Set.Icc (-(hamilton_reference_radius ^ 2)) 0 ⊆ L.D.carrier

def HamiltonLimitRegularWindow (L : HamiltonCGHLimit (I := I) M) : Prop :=
  Set.Ioo (-(hamilton_reference_radius ^ 2)) 0 ⊆ L.D.regular

def HamiltonLimitConnected (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  ConnectedSpace L.N

def HamiltonLimitBoundaryless : Prop := I.Boundaryless

def HamiltonLimitFlow (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) L.S

def HamiltonLimitBaseScalarConvergence
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  Filter.Tendsto
    (fun k : Nat =>
      hamiltonRescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k)))
    Filter.atTop (nhds (L.S.scalar 0 L.basepoint))

def LimitRicNonneg (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall t : Real, t ∈ L.D.carrier -> forall x : L.N,
    forall v : TangentSpace I x,
      0 <= L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

def LimitBaseScalarOne (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  L.S.scalar 0 L.basepoint = 1

def LimitScalarPosAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, 0 < L.S.scalar t x

def LimitScalarPos (L : HamiltonCGHLimit (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitScalarPosAt (I := I) L t

def LimitScalarNonneg (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall t : Real, t ∈ L.D.carrier -> forall x : L.N,
    0 <= L.S.scalar t x

def LimitTracefreeZeroAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x = 0

def LimitTracefreeZero (L : HamiltonCGHLimit (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitTracefreeZeroAt (I := I) L t

def LimitTracefreeDecayAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall η : Real, 0 < η ->
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x <= η

def LimitTracefreeDecay (L : HamiltonCGHLimit (I := I) M) : Prop :=
  forall t : Real, t ∈ L.D.regular -> LimitTracefreeDecayAt (I := I) L t

def LimitEinsteinAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall v w : TangentSpace I x,
    L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
      (L.S.scalar t x / 3) * (L.S.base.metric t).inner x v w

def LimitConstPosSec (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  exists gInf : SmoothRiemannianMetric I L.N,
    ConstPosSecMetric (I := I) (M := L.N) gInf

def LimitRoundAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  let g := L.S.base.metric t
  exists K : Real, 0 < K /\
    (forall x : L.N, forall v : TangentSpace I x,
      (((Module.finrank Real E : Real) - 1) * K) * g.inner x v v <=
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /\
    ConstPosSecMetric (I := I) (M := L.N) g

theorem hamilton_short_time_exists
    {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace Real E0]
    [FiniteDimensional Real E0] [NeZero (Module.finrank Real E0)]
    {H0 : Type*} [TopologicalSpace H0] {I0 : ModelWithCorners Real E0 H0}
    {M0 : Type u} [TopologicalSpace M0] [ChartedSpace H0 M0] [IsManifold I0 ∞ M0]
    [SigmaCompactSpace M0] [T2Space M0] [BoundarylessManifold I0 M0]
    (hM : Closed3Manifold (I := I0) (M := M0))
    (g0 : SmoothRiemannianMetric I0 M0) :
    ∃ T : Real, 0 < T ∧ ∃ g_fam : Real → SmoothRiemannianMetric I0 M0,
      g_fam 0 = g0 ∧
      (∀ (x0 : M0) (i j : Fin (Module.finrank Real E0)),
        ContMDiffOn (𝓘(Real, Real).prod I0) 𝓘(Real) ∞
          (fun p : Real × M0 =>
            Integral.Measure.chartGramMatrix (I := I0) (g_fam p.1) x0 p.2 i j)
          (Set.Ioo (0 : Real) T ×ˢ (trivializationAt E0 (TangentSpace I0) x0).baseSet)) ∧
      (∀ (x0 : M0) (i j : Fin (Module.finrank Real E0)),
        ContinuousOn
          (fun p : Real × M0 =>
            Integral.Measure.chartGramMatrix (I := I0) (g_fam p.1) x0 p.2 i j)
          (Set.Ico (0 : Real) T ×ˢ (trivializationAt E0 (TangentSpace I0) x0).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : Real) T, ∀ x : M0, ∀ v w : TangentSpace I0 x,
        HasDerivWithinAt (fun s : Real => (g_fam s).inner x v w)
          ((-2 : Real) *
            DifferentialGeometry.Geometry.Curvature.ricciTensor
              (I := I0) (g_fam t) x v w) (Set.Ici 0) t) := by
  classical
  letI : CompactSpace M0 := hM.1
  letI : I0.Boundaryless := hM.2.2.1
  obtain ⟨T, hT, g_fam, hg0, hsmooth, hpde⟩ :=
    DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence
      (I := I0) (M := M0) g0
  refine ⟨T, hT, g_fam, hg0, ?_, ?_, hpde⟩
  · intro x0 i j
    exact (hsmooth x0 i j).mono (by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact ⟨⟨le_of_lt ht.1, ht.2⟩, hx⟩)
  · intro x0 i j
    exact (hsmooth x0 i j).continuousOn

theorem hamilton_short_time_solution_candidate
    [BoundarylessManifold I M]
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M) :
    ∃ T : Real, ∃ hT : 0 < T,
      ∃ S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT),
        S.family.metric
            (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT).initial
              = g0 ∧
        (∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
          ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
            (fun p : Real × M =>
              Integral.Measure.chartGramMatrix (I := I) (S.family.metric p.1) x0 p.2 i j)
            (Set.Ioo (0 : Real) T ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet)) ∧
        (∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
          ContinuousOn
            (fun p : Real × M =>
              Integral.Measure.chartGramMatrix (I := I) (S.family.metric p.1) x0 p.2 i j)
            (Set.Ico (0 : Real) T ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : Real) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (S.family.metric s).inner x v w)
            ((-2 : Real) *
              DifferentialGeometry.Geometry.Curvature.ricciTensor
                (I := I) (S.family.metric t) x v w) (Set.Ici 0) t) := by
  obtain ⟨T, hT, g_fam, hg0, hsmooth, hcont, hpde⟩ :=
    hamilton_short_time_exists hM g0
  refine ⟨T, hT, ⟨⟨g_fam⟩⟩, ?_, ?_, ?_, ?_⟩
  · change g_fam 0 = g0
    exact hg0
  · intro x0 i j
    exact hsmooth x0 i j
  · intro x0 i j
    exact hcont x0 i j
  · intro t ht x v w
    exact hpde t ht x v w

omit [SigmaCompactSpace M] in
theorem hamilton_short_time_is_solution
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M) :
    ∃ T : Real, ∃ hT : 0 < T,
      ∃ S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT),
        S.family.metric
            (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT).initial
              = g0 ∧
          DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S := by
  classical
  letI : CompactSpace M := hM.1
  haveI : I.Boundaryless := hM.2.2.1
  obtain ⟨T, hT, g, hstart, hjoint, hpde⟩ :=
    DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence
      (I := I) (M := M) g0
  refine ⟨T, hT, ⟨⟨g⟩⟩, ?_, ?_⟩
  · change g 0 = g0
    exact hstart
  · exact DifferentialGeometry.PDE.RicciFlow.solutionOn_of_joint
      (I := I) (M := M) hT g hjoint hpde

theorem hamilton_short_time_smooth_solution
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M) :
    ∃ T : Real, ∃ hT : 0 < T,
      ∃ S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT),
        S.family.metric
            (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 T hT).initial
              = g0 ∧
          DifferentialGeometry.PDE.RicciFlow.IsSmoothSolutionOn (I := I) (M := M) S := by
  haveI : I.Boundaryless := hM.2.2.1
  obtain ⟨T, hT, S, hstart, hSol⟩ :=
    hamilton_short_time_is_solution (I := I) (M := M) hM g0
  exact ⟨T, hT, S, hstart,
    DifferentialGeometry.PDE.RicciFlow.smoothOfSol (I := I) S hSol⟩

theorem hamilton_flow_exists_normalized
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
    exists omega : Real, exists h0ω : 0 < omega,
      exists P : HamiltonFiniteTimeFlow (I := I) (M := M) g0,
        P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω := by
  letI : CompactSpace M := hM.1
  letI : ConnectedSpace M := hM.2.1
  letI : I.Boundaryless := hM.2.2.1
  have hdim : Module.finrank Real E = 3 := hM.2.2.2
  have hscalar_pos : ∀ x : M,
      0 < metricScalarAt (I := I) (M := M) g0 x :=
    scalar_pos_of_ricci (I := I) (M := M) g0 hdim hpos
  rcases exists_max_flow (I := I) (M := M) g0 hdim hscalar_pos with
    ⟨omega, h0ω, Smax, hSmax, hstart, hmax⟩
  have hcurv : Rm04NormSqUnboundedAt (I := I) Smax Smax.base.rm04 :=
    rmUnbounded_of_maximal (I := I) hdim hSmax hmax
      (rm04Realizes_metric (I := I) Smax)
  let P : HamiltonFiniteTimeFlow (I := I) (M := M) g0 :=
    { D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω
      S := Smax
      isSmooth := smoothOfSol (I := I) Smax hSmax
      startsAt := by simpa using hstart
      curvUnbounded := by
        intro K
        rcases hcurv K with ⟨t, x, ht0, htω, hK⟩
        exact ⟨t, x, ⟨ht0, htω⟩, by simpa [curvatureNormSq] using hK⟩ }
  exact ⟨omega, h0ω, P, rfl⟩

theorem hamilton_flow_exists
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
    Nonempty (HamiltonFiniteTimeFlow (I := I) (M := M) g0) := by
  rcases hamilton_flow_exists_normalized (I := I) (M := M) hM g0 hpos with
    ⟨_omega, _h0ω, P, _hD⟩
  exact ⟨P⟩

noncomputable def hamiltonFiniteTimeFlowChoice
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
  HamiltonFiniteTimeFlow (I := I) (M := M) g0 :=
  Classical.choice (hamilton_flow_exists (I := I) (M := M) hM g0 hpos)

def hamiltonMetricConnectionFamily
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real :=
  hamiltonMetricConnectionFamilyCore (I := I) P.S g0

def hamiltonRicciNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (P.S.family.metric t) x 2 (P.S.ricciAt t x)

def hamiltonScalarLaplacian
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (hamiltonMetricConnectionFamily (I := I) P) t
      (hamiltonScalar (I := I) P t) x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_weak_maximum_principle_regularity_on_interval
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (c0 : Real) (K : Real -> NNReal) (T : Real)
    (hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / (3 : Real)) * c0 * t ≠ 0) :
    DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWMPRegularity
      (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
      (hamiltonScalar (I := I) P) (K T) := by
  simpa [hamiltonScalar, hamiltonSolution] using
    (DifferentialGeometry.PDE.RicciFlow.scalarRegOfSmooth (I := I) (M := M)
      P.S P.isSmooth (hamiltonMetricConnectionFamily (I := I) P) T 3 c0 (K T)
      hsubset
      (by
        intro t ht
        have htD : t ∈ P.D.carrier := hsubset t ht
        simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, htD])
      hden)

def HamiltonScalarBlowup
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) : Prop :=
  forall A : Real, exists t : Real, exists x : M,
    t ∈ P.D.carrier /\ A < hamiltonScalar (I := I) P t x

def HamiltonBlowupPointSelection
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  (forall i : Nat, 0 < hamiltonBlowupScale (I := I) P Q i) /\
    (forall i : Nat, 0 < Q.time i) /\
    (forall i : Nat, Q.time i ∈ P.D.carrier) /\
    (forall A : Real, exists N : Nat,
      forall i : Nat, N <= i ->
        A <= hamiltonBlowupScale (I := I) P Q i * Q.time i) /\
    (forall i : Nat, hamiltonRescaledScalar (I := I) P Q i 0 (Q.point i) = 1) /\
    (forall (i : Nat) (s : Real) (x : M),
      -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
        hamiltonRescaledScalar (I := I) P Q i s x <= 1)

noncomputable def hamiltonRescaledSolution
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    SolutionOn (I := I) (M := M)
      (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
        (hsel.1 i) (hsel.2.2.1 i)) :=
  paraSolution (I := I) P.S (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
    (hsel.1 i) (hsel.2.2.1 i)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_tracefree_ricci_norm_sq_identity
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    DifferentialGeometry.PDE.RicciFlow.ParabolicTraceFreeRicciNormSqScaling (M := M)
      (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
      (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (hamiltonRescaledSolution (I := I) P Q hsel i)))
      (Q.time i) (hamiltonBlowupScale (I := I) P Q i) := by
  intro s x
  simp only [hamiltonRescaledSolution,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAtOf,
    DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
    DifferentialGeometry.PDE.RicciFlow.paraSolution_ricciNorm]
  ring

structure HamiltonSourceRealization
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M) : Prop where
  time_mem : forall (i : Nat) (t : Real), t ∈ L.D.carrier ->
    t ∈ (paraInterval P.D (Q.time (L.origIndex i))
      (hamiltonBlowupScale (I := I) P Q (L.origIndex i))
      (hsel.1 (L.origIndex i)) (hsel.2.2.1 (L.origIndex i))).carrier
  basepoint_map : forall i : Nat,
    letI : TopologicalSpace (L.sourceTerm i).M := (L.sourceTerm i).topology
    letI : ChartedSpace H (L.sourceTerm i).M := (L.sourceTerm i).charted
    L.sourceToOrig i (L.sourceTerm i).basepoint = Q.point (L.origIndex i)
  metric_eq : forall i : Nat,
    letI : TopologicalSpace (L.sourceTerm i).M := (L.sourceTerm i).topology
    letI : ChartedSpace H (L.sourceTerm i).M := (L.sourceTerm i).charted
    letI : IsManifold I ∞ (L.sourceTerm i).M := (L.sourceTerm i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (L.sourceTerm i).M := by
      change IsManifold I ∞ (L.sourceTerm i).M
      infer_instance
    letI : SigmaCompactSpace (L.sourceTerm i).M := (L.sourceTerm i).sigmaCompact
    letI : T2Space (L.sourceTerm i).M := (L.sourceTerm i).t2
    forall t : Real, t ∈ L.D.carrier ->
      (L.sourceTerm i).S.base.metric t =
        Diffeomorph.pullbackMetricCross
          ((hamiltonRescaledSolution (I := I) P Q hsel (L.origIndex i)).base.metric t)
          (L.sourceToOrig i)

def HamiltonRescaledRicciNonnegative
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  forall (i : Nat) (s : Real) (x : M) (v : TangentSpace I x),
    -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
      0 <= P.S.ricciAt (hamiltonRescaledTime (I := I) P Q i s) x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)

def HamiltonPinching
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (omega : Real) : Prop :=
  forall T : Real, 0 <= T -> T < omega ->
    exists delta : Real,
      0 < delta /\ delta < (1 : Real) / 3 /\
        DifferentialGeometry.PDE.RicciFlow.PinchPres (I := I) (M := M)
          (fun t : Real => P.S.base.metric t)
          (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
            P.S.ricci)
          P.S.scalar T delta

def HamiltonFixedPinching
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (omega : Real) : Prop :=
  exists delta : Real,
    0 < delta /\ delta < (1 : Real) / 3 /\
      forall T : Real, 0 <= T -> T < omega ->
        DifferentialGeometry.PDE.RicciFlow.PinchPres (I := I) (M := M)
          (fun t : Real => P.S.base.metric t)
          (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
            P.S.ricci)
          P.S.scalar T delta

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem HamiltonFixedPinching.toVarying
    {g0 : SmoothRiemannianMetric I M}
    {P : HamiltonFiniteTimeFlow (I := I) (M := M) g0} {omega : Real}
    (h : HamiltonFixedPinching (I := I) P omega) :
    HamiltonPinching (I := I) P omega := by
  rcases h with ⟨delta, hdelta0, hdelta13, hpres⟩
  intro T hT hTω
  exact ⟨delta, hdelta0, hdelta13, hpres T hT hTω⟩

def HamiltonRicciNonnegative
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (omega : Real) : Prop :=
  forall T : Real, 0 <= T -> T < omega ->
    DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      (Set.Icc 0 T)

def HamiltonRicciNonnegativeTransfer
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M) : Prop :=
  HamiltonSourceRealization (I := I) P Q hsel L ->
    HamiltonRescaledRicciNonnegative (I := I) P Q ->
    LimitRicNonneg (I := I) L

def HamiltonPinchingEstimate
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) : Prop :=
  exists epsilon C : Real,
    0 < epsilon /\ epsilon < 1 /\ 0 <= C /\
      DifferentialGeometry.PDE.RicciFlow.PinchEstimateOn (M := M)
        (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
          (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
        P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.pinchWeight (M := M) P.S.scalar epsilon)
        C P.D.carrier

private theorem scaled_pinch_le
    {q R r C epsilon : Real}
    (hR : 0 < R) (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hpinch : q / r ^ 2 ≤ C * (R * r) ^ (-epsilon)) :
    q ≤ C * R ^ (-epsilon) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hmain :
      q ≤ (C * (R * r) ^ (-epsilon)) * r ^ 2 :=
    (div_le_iff₀ hr2).mp hpinch
  have hrewrite :
      (C * (R * r) ^ (-epsilon)) * r ^ 2 =
        (C * R ^ (-epsilon)) * r ^ (2 - epsilon) := by
    rw [Real.mul_rpow hR.le hr.le, ← Real.rpow_two r]
    calc
      C * (R ^ (-epsilon) * r ^ (-epsilon)) * r ^ (2 : Real) =
          (C * R ^ (-epsilon)) *
            (r ^ (-epsilon) * r ^ (2 : Real)) := by ring
      _ = (C * R ^ (-epsilon)) * r ^ (2 - epsilon) := by
        rw [← Real.rpow_add hr]
        congr 2
        ring
  rw [hrewrite] at hmain
  have hrpow : r ^ (2 - epsilon) ≤ 1 :=
    Real.rpow_le_one hr.le hr1 (by linarith)
  have hcoef : 0 ≤ C * R ^ (-epsilon) :=
    mul_nonneg hC (Real.rpow_nonneg hR.le _)
  exact hmain.trans (by simpa using mul_le_mul_of_nonneg_left hrpow hcoef)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_tracefree_ricci_norm_sq_at_zero_bound
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (hscalar :
      ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x)
    (hpinch : HamiltonPinchingEstimate (I := I) P) :
    ∃ epsilon C : Real,
      0 < epsilon ∧ epsilon < 1 ∧ 0 ≤ C ∧
        ∀ i : Nat, ∀ x : M,
          DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
              (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
              (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                (hamiltonRescaledSolution (I := I) P Q hsel i)) 0 x ≤
            C * hamiltonBlowupScale (I := I) P Q i ^ (-epsilon) := by
  rcases hpinch with ⟨epsilon, C, hepsilon0, hepsilon1, hC, hest⟩
  refine ⟨epsilon, C, hepsilon0, hepsilon1, hC, ?_⟩
  intro i x
  let R : Real := hamiltonBlowupScale (I := I) P Q i
  let r : Real := (hamiltonRescaledSolution (I := I) P Q hsel i).scalar 0 x
  let q : Real :=
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
      (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (hamiltonRescaledSolution (I := I) P Q hsel i)) 0 x
  have hR : 0 < R := hsel.1 i
  have htime : 0 < Q.time i := hsel.2.1 i
  have htimeMem : Q.time i ∈ P.D.carrier := hsel.2.2.1 i
  have hscalarOld : 0 < P.S.scalar (Q.time i) x :=
    hscalar (Q.time i) htimeMem x
  have hr_eq :
      r = R⁻¹ * P.S.scalar (Q.time i) x := by
    simp only [r, R, hamiltonRescaledSolution,
      DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
      DifferentialGeometry.PDE.RicciFlow.paraTime_zero]
  have hr : 0 < r := by
    rw [hr_eq]
    exact mul_pos (inv_pos.mpr hR) hscalarOld
  have hleft : -(R * Q.time i) ≤ (0 : Real) := by
    have : 0 < R * Q.time i := mul_pos hR htime
    linarith
  have hr1 : r ≤ 1 := by
    have hmax := hsel.2.2.2.2.2 i 0 x
      (by simpa only [R] using hleft) le_rfl
    have hr_display :
        r = hamiltonRescaledScalar (I := I) P Q i 0 x := by
      simpa only [R, hamiltonRescaledScalar, hamiltonRescaledTime, hamiltonScalar,
        hamiltonSolution, zero_div, add_zero] using hr_eq
    rwa [← hr_display] at hmax
  have hscalarOld_eq : P.S.scalar (Q.time i) x = R * r := by
    rw [hr_eq]
    field_simp [ne_of_gt hR]
  have hscalarDisplay :
      DifferentialGeometry.PDE.RicciFlow.ParabolicScalarCurvatureScaling (M := M)
        P.S.scalar
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (Q.time i) R := by
    intro s y
    simpa only [R, hamiltonRescaledSolution] using
      congrFun
        (congrFun
          (DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar
            (I := I) P.S (Q.time i) R hR htimeMem) s) y
  have hratio :=
    DifferentialGeometry.PDE.RicciFlow.para_tracefree_ratio_invariant
      (M := M)
      (scalar := P.S.scalar)
      (scalarR := (hamiltonRescaledSolution (I := I) P Q hsel i).scalar)
      (q := DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
      (qR := DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq
        (hamiltonRescaledSolution (I := I) P Q hsel i).scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (hamiltonRescaledSolution (I := I) P Q hsel i)))
      (τ := Q.time i) (R := R) hR hscalarDisplay
      (by simpa only [R] using hamilton_rescaled_tracefree_ricci_norm_sq_identity (I := I) P Q hsel i)
      0 x
  have hratio_le :
      q / r ^ 2 ≤ C * (R * r) ^ (-epsilon) := by
    rw [hratio]
    simpa only [q, r, R,
      DifferentialGeometry.PDE.RicciFlow.paraTime_zero, hscalarOld_eq,
      DifferentialGeometry.PDE.RicciFlow.pinchWeight] using
      hest (Q.time i) htimeMem x
  exact scaled_pinch_le hR hr hr1 hC hepsilon0 hepsilon1 hratio_le

def HamiltonPinchingTransfer
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M) : Prop :=
  HamiltonSourceRealization (I := I) P Q hsel L ->
    HamiltonPinchingEstimate (I := I) P ->
    LimitScalarPos (I := I) L ->
      LimitTracefreeDecay (I := I) L

def HamiltonCGHLimitExistence
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q) : Prop :=
  exists L : HamiltonCGHLimit (I := I) M,
    HamiltonSourceRealization (I := I) P Q hsel L /\
      HamiltonLimitSubsequence (I := I) L /\
      HamiltonLimitWindow (I := I) L /\
      HamiltonLimitRegularWindow (I := I) L /\
      HamiltonLimitConnected (I := I) L /\
      HamiltonLimitBoundaryless (I := I) /\
      HamiltonLimitFlow (I := I) L /\
      HamiltonRicciNonnegativeTransfer (I := I) P Q hsel L /\
      HamiltonLimitBaseScalarConvergence (I := I) P Q L /\
      LimitScalarPos (I := I) L /\
      HamiltonPinchingTransfer (I := I) P Q hsel L

def HamiltonWindow
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (r : Real) : Prop :=
  exists N : Nat, forall i : Nat, N <= i ->
    forall s : Real, -(r ^ 2) <= s -> s <= 0 ->
      -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s /\ s <= 0

def HamiltonRiemannCurvatureBound
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) : Prop :=
  forall (i : Nat) (s : Real) (x : M),
    -(hamiltonBlowupScale (I := I) P Q i * Q.time i) <= s -> s <= 0 ->
      hamiltonRiemannNormSq (I := I) (M := M) P
          (hamiltonRescaledTime (I := I) P Q i s) x <=
        (100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2

def hamiltonRescaledInitialTime
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q) (i : Nat) :
    (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
      (hsel.1 i) (hsel.2.2.1 i)).FlowTime :=
  ⟨0, (paraInterval P.D (Q.time i) (hamiltonBlowupScale (I := I) P Q i)
    (hsel.1 i) (hsel.2.2.1 i)).initial_mem⟩

def hamiltonRescaledBall
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (i : Nat) (r : Real) (hr : 0 < r) :
    Perelman.FlowMetricBall (hamiltonRescaledSolution (I := I) P Q hsel i)
      (hamiltonRescaledInitialTime (I := I) P Q hsel i) where
  center := Q.point i
  radius := r
  radius_pos := hr

def HamiltonRiemannCurvatureControl
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (r : Real) : Prop :=
  exists hr : 0 < r, exists N : Nat, forall i : Nat, N <= i ->
    let B := hamiltonRescaledBall (I := I) P Q hsel i r hr
    B.IsRmControlled

def HamiltonNoncollapse
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (kappa r : Real) : Prop :=
  0 < kappa /\
    exists hr : 0 < r, exists N : Nat, forall i : Nat, N <= i ->
      let B := hamiltonRescaledBall (I := I) P Q hsel i r hr
      B.IsRmControlled /\ B.IsKappaNoncollapsed kappa

structure HamiltonCompactness
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (hsel : HamiltonBlowupPointSelection (I := I) P Q) where
  rmBound : HamiltonRiemannCurvatureBound (I := I) P Q
  window : HamiltonWindow (I := I) P Q hamilton_reference_radius
  kappa : Real
  noncollapse : HamiltonNoncollapse (I := I) P Q hsel kappa hamilton_reference_radius

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_continuous
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Continuous (fun x : M => hamiltonScalar (I := I) P 0 x) := by
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
        fun y : M => hamiltonScalar (I := I) P 0 y := by
    funext y
    have hmetric :
        Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y =
          DifferentialGeometry.Geometry.Operator.metricTensor0S (I := I) (P.S.family.metric 0)
            y := by
      ext v
      rw [Tensor0SBundle.metricTensorField_apply,
        DifferentialGeometry.Geometry.Operator.metricTensor0S_apply]
    change
      Tensor0SBundle.inner0S (I := I) (P.S.family.metric 0) y 2
          (Tensor0SBundle.metricTensorField (I := I) (P.S.family.metric 0) y)
          (P.S.ricci 0 y) =
        DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar (I := I) (hamiltonSolution (I := I) P) 0 y
    rw [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace,
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt, hmetric]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci_apply]
  exact (hfun ▸ hmdiff.continuousAt)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_ricci_positive
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    DifferentialGeometry.PDE.RicciFlow.RicciPosInit (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
        P.S.ricci) := by
  intro x v hv
  have hmetric0 : P.S.family.metric 0 = g0 := by
    have hinit : P.D.initial = 0 := by
      rw [hD]
      rfl
    simpa [hinit] using P.startsAt
  have hpos0 :
      0 < DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    rw [hmetric0]
    exact hpos x v hv
  simpa [DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt] using hpos0

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_positive
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    forall x : M, 0 < hamiltonScalar (I := I) P 0 x := by
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
        0 < P.S.ricciAt 0 x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    intro v hv
    change
      0 < DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := M)
        (P.S.family.metric 0) x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)
    rw [hmetric0]
    exact hpos x v hv
  exact
    DifferentialGeometry.Geometry.Curvature.metricTrace_pos_of_posDef
      (I := I) (M := M) (P.S.family.metric 0) (P.S.ricciAt 0 x)
      hdimx hpos0

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_initial_scalar_minimum
    [CompactSpace M] [Nonempty M]
    (hdim : Module.finrank Real E = 3)
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real,
      DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum (M := M) (hamiltonScalar (I := I) P) c0 ∧
        forall x : M, 0 < hamiltonScalar (I := I) P 0 x := by
  have hcont : Continuous (fun x : M => hamiltonScalar (I := I) P 0 x) :=
    hamilton_initial_scalar_continuous (I := I) (M := M) P
  rcases DifferentialGeometry.PDE.RicciFlow.exists_initialScalarMinimum_of_continuous
      (M := M) (hamiltonScalar (I := I) P) hcont with
    ⟨c0, hmin⟩
  exact ⟨c0, hmin, hamilton_initial_scalar_positive (I := I) (M := M) hdim h0ω hpos P hD⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_slab_continuous_on
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (T : Real) (hTω : T < omega) :
    ContinuousOn
      (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
  have hreg :
      DifferentialGeometry.PDE.RicciFlow.ScalarSTContOn
        (I := I) (M := M) (hamiltonSolution (I := I) P) :=
    hamilton_scalar_space_time_continuous (I := I) (M := M) P
  simpa [hamiltonScalar, DifferentialGeometry.Analysis.Parabolic.spacetimeSlab] using
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_continuousOn
      (I := I) (M := M) (hamiltonSolution (I := I) P)
      hreg
      T
      (by
        intro t ht
        rw [hD]
        exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_evolution_equation
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
      (hamiltonScalar (I := I) P)
      (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) := by
  rw [← hD]
  have h :
      DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
        (D := P.D)
        (hamiltonSolution (I := I) P).scalar
        (fun t x =>
          DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (hamiltonMetricConnectionFamily (I := I) P)
            t
            ((hamiltonSolution (I := I) P).scalar t) x)
        (fun t x =>
          Tensor0SBundle.normSq0S (I := I)
            ((hamiltonSolution (I := I) P).family.metric t) x 2
            ((hamiltonSolution (I := I) P).ricci t x)) := by
    refine
      DifferentialGeometry.PDE.RicciFlow.scalarEvolOfSmooth
        (I := I) (M := M) (hamiltonSolution (I := I) P) P.isSmooth
        (hamiltonMetricConnectionFamily (I := I) P) ?_ ?_
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, ht]
    · intro t
      have ht : (t : Real) ∈ P.D.carrier := P.D.regular_subset t.2
      simp [hamiltonMetricConnectionFamily, hamiltonMetricConnectionFamilyCore, ht]
  simpa [hamiltonScalar, hamiltonScalarLaplacian, hamiltonRicciNormSq, hamiltonSolution] using h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_laplacian_realizes_heat
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) (T : Real) :
    DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
      (I := I) (hamiltonMetricConnectionFamily (I := I) P) T
      (hamiltonScalar (I := I) P)
      (hamiltonScalarLaplacian (I := I) P) := by
  exact
    DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
      (I := I) (G := hamiltonMetricConnectionFamily (I := I) P)
      (T := T) (scalar := hamiltonScalar (I := I) P)
      (scalarLap := hamiltonScalarLaplacian (I := I) P)
      (by
        intro t _ht x
        rfl)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_weak_maximum_principle_regularity
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (c0 : Real) (hc0 : 0 < c0) (K : Real -> NNReal) :
    forall T : Real, 0 < T -> T < omega ->
      T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
        DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWMPRegularity
          (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
          (hamiltonScalar (I := I) P) (K T) := by
  intro T _hT hTω hPole
  have hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ P.D.carrier := by
    intro t ht
    rw [hD]
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hden_pos :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
    DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
      (n := 3) (c0 := c0) (by norm_num) hc0 hPole
  have hden :
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        1 - (2 / (3 : Real)) * c0 * t ≠ 0 := by
    intro t ht
    exact ne_of_gt (hden_pos t ht)
  simpa [hamiltonMetricConnectionFamily, hamiltonScalar, hamiltonSolution] using
    hamilton_scalar_weak_maximum_principle_regularity_on_interval (I := I) (M := M) P c0 K T hsubset hden

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_sq_le_three_ricci_norm_sq
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (t : Real) (x : M) :
    (1 / 3 : Real) * (hamiltonScalar (I := I) P t x) ^ 2 <=
      hamiltonRicciNormSq (I := I) P t x := by
  classical
  letI : Nonempty (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :=
    ⟨⟨0, by simp [hdim]⟩⟩
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
    Real
      (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) (P.S.family.metric t) x k l (extChartAt I x x)
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (P.S.family.metric t) x
        basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (P.S.family.metric t) x
  have h :=
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S
      (I := I) (g := P.S.family.metric t) (basis := basis)
      (gInv := gInv) hinv (P.S.ricciAt t x)
  have hcard :
      (1 / (Fintype.card (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
        Real)) =
        (1 / 3 : Real) := by
    simp [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hdim]
  have hcoef : ((Module.finrank Real E : Real)⁻¹) = (3⁻¹ : Real) := by
    simp [hdim]
  simpa [hamiltonScalar, hamiltonRicciNormSq, DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hcard,
    hcoef]
    using h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_slab_lipschitz
    [CompactSpace M]
    {omega : Real}
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (c0 : Real)
    (hc0 : 0 < c0)
    (hcont : forall T : Real, 0 <= T -> T < omega ->
      ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T)) :
    exists K : Real -> NNReal,
      forall T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          forall t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a t)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
  classical
  have hExists :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
        ∃ K : NNReal,
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith K
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a t)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T hT hTω hPole
    have hscalar_cont_T :
        ContinuousOn
          (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) :=
      hcont T (le_of_lt hT) hTω
    have hden :
        ∀ t : Real, t ∈ Set.Icc 0 T ->
          0 < 1 - (2 / 3 : Real) * c0 * t :=
      DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 hPole
    have hbar_cont :
        ContinuousOn (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)
          (Set.Icc 0 T) := by
      unfold DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier
      have hden_cont :
          ContinuousOn (fun t : Real => 1 - (2 / 3 : Real) * c0 * t)
            (Set.Icc 0 T) := by
        fun_prop
      exact continuousOn_const.div hden_cont (fun t ht => ne_of_gt (hden t ht))
    have hcompact :
        IsCompact
          (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
            (hamiltonScalar (I := I) P)
            (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) :=
      DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet_isCompact
        (M := M) T (hamiltonScalar (I := I) P)
        (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0) hscalar_cont_T hbar_cont
    exact
      DifferentialGeometry.PDE.RicciFlow.exists_scalarLowerReaction_lipschitzOn_valueSet
        (M := M) 3 T (hamiltonScalar (I := I) P)
        (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0) hcompact
  let K : Real -> NNReal := fun T =>
    if h : 0 < T ∧ T < omega ∧
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 then
      Classical.choose (hExists T h.1 h.2.1 h.2.2)
    else 0
  refine ⟨K, ?_⟩
  intro T hT hTω hPole t ht
  dsimp [K]
  rw [dif_pos ⟨hT, hTω, hPole⟩]
  exact Classical.choose_spec (hExists T hT hTω hPole) t ht

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_evolution_data
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real,
      exists c0 : Real,
      exists scalar scalarLap ricciNormSq : Real -> M -> Real,
      exists K : Real -> NNReal,
        DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum (M := M) scalar c0 /\
        (forall x : M, 0 < scalar 0 x) /\
        (forall T : Real, 0 <= T -> T < omega ->
          ContinuousOn (fun p : Real × M => scalar p.1 p.2)
            (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T)) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWMPRegularity
              (I := I) G T 3 c0 scalar (K T)) /\
        DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
          (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
          scalar scalarLap ricciNormSq /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
              (I := I) G T scalar scalarLap) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
              (1 / 3 : Real) * (scalar t x) ^ 2 <= ricciNormSq t x) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T ->
              LipschitzOnWith (K T)
                (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a t)
                (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet
                  (M := M) T scalar
                  (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0))) := by
  rcases hM with ⟨hcompact, _hconnected, _hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : Nonempty M := inferInstance
  rcases hamilton_initial_scalar_minimum (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont :
      forall T : Real, 0 <= T -> T < omega ->
        ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    intro T _hT hTω
    exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω
  have hc0 : 0 < c0 :=
    DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases hamilton_scalar_slab_lipschitz (I := I) (M := M) (omega := omega) P c0 hc0 hcont with
    ⟨K, hK⟩
  refine ⟨hamiltonMetricConnectionFamily (I := I) P, c0,
    hamiltonScalar (I := I) P, hamiltonScalarLaplacian (I := I) P,
    hamiltonRicciNormSq (I := I) P, K, hinit_min, hinit_pos, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · exact hamilton_scalar_weak_maximum_principle_regularity (I := I) (M := M) h0ω P hD c0 hc0 K
  · exact hamilton_scalar_evolution_equation (I := I) (M := M) h0ω P hD
  · intro T _hT _hTω _hPole
    exact hamilton_scalar_laplacian_realizes_heat (I := I) (M := M) P T
  · intro _T _hT _hTω _hPole t _ht x
    exact hamilton_scalar_sq_le_three_ricci_norm_sq (I := I) (M := M) hdim P t x
  · intro T hT hTω hPole
    exact hK T hT hTω hPole

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_extinction_time_bound
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists c0 : Real, 0 < c0 /\ omega <= 3 / (2 * c0) := by
  have hMcopy := hM
  rcases hM with ⟨hcompact, hconnected, hboundaryless, _hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  rcases hamilton_scalar_evolution_data (I := I) (M := M) h0ω hMcopy g0 hpos P hD with
    ⟨G, c0, scalar, scalarLap, ricciNormSq, K,
      hinit_min, hinit_pos, hscalar_cont, hreg, hevol, hlap, hricci, hF_lip⟩
  have hfinite :
      0 < c0 ∧ omega <= 3 / (2 * c0) :=
    DifferentialGeometry.PDE.RicciFlow.finiteTime3D (I := I) (M := M) h0ω G c0 scalar scalarLap
      ricciNormSq K hinit_min hinit_pos hscalar_cont hreg hevol hlap
      hricci hF_lip
  exact ⟨c0, hfinite.1, hfinite.2⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem hamilton_rm_scalar_ctl
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (hsec9 : HamiltonRicciNonnegative (I := I) P omega)
    {t : Real} {x : M} (htD : t ∈ P.D.carrier) :
    0 <= hamiltonScalar (I := I) P t x ∧
      hamiltonRiemannNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P t x) ^ 2 := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  have htD' : t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
    h0ω).carrier := by
    simpa [hD] using htD
  have ht0 : 0 <= t := htD'.1
  have htω : t < omega := htD'.2
  have hricOn := hsec9 t ht0 htω
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hricNonneg :
      DifferentialGeometry.Geometry.Curvature.RicciNonnegAt (I := I) (P.S.ricciAt t x) := by
    intro v
    simpa [DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt] using
      hricOn t ⟨ht0, le_rfl⟩ x v
  have hricSym :
      DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (P.S.ricciAt t x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := M) P.S t x
  have hRmScalar :
      hamiltonRiemannNormSq (I := I) (M := M) P t x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P t x) ^ 2 := by
    have hpoint :=
      DifferentialGeometry.Geometry.Curvature.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric t)
        (Ric := P.S.ricciAt t x) (scalar := P.S.scalar t x)
        (Rm04 := P.S.base.rm04 t x) hdimT hricSym hricNonneg
        (fun basis horth =>
          DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := M) P.S horth)
    simpa [hamiltonRiemannNormSq, hamiltonScalar, hamiltonSolution] using hpoint
  have hscalarNonneg : 0 <= hamiltonScalar (I := I) P t x := by
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric t) (P.S.ricciAt t x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar t x) (P.S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3
            basis := by
      have htr :=
        DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric t)
          (P.S.ricciAt t x) horth
      simpa [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar t x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
      DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar t x
    rw [hscalar_eq]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem hamilton_scalar_cont_slab
    {omega : Real} (h0ω : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (T : Real) :
    T < omega ->
    ContinuousOn
      (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
  intro hTω
  exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω

omit [SigmaCompactSpace M] [T2Space M] in
private theorem slab_max_of_continuousOn
    [CompactSpace M]
    {f : Real × M -> Real}
    {T t : Real} {x : M}
    (hcont : ContinuousOn f (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T))
    (ht : t ∈ Set.Icc 0 T) :
    ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 T ∧
        ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ y : M,
          f (s, y) <= f (tmax, xmax) := by
  classical
  let slab := DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T
  have hcompact : IsCompact slab := by
    unfold slab DifferentialGeometry.Analysis.Parabolic.spacetimeSlab
    exact isCompact_Icc.prod isCompact_univ
  have hnonempty : slab.Nonempty := ⟨(t, x), ⟨ht, trivial⟩⟩
  rcases hcompact.exists_isMaxOn hnonempty hcont with ⟨p, hp, hmax⟩
  rcases p with ⟨tmax, xmax⟩
  refine ⟨tmax, xmax, hp.1, ?_⟩
  intro s hs y
  exact hmax ⟨hs, trivial⟩

private def hamiltonPointLevel (B : Real) (i : Nat) : Real :=
  max B 0 + ((i : Real) + 1)

private theorem hamiltonPointLevel_pos (B : Real) (i : Nat) :
    0 < hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem hamiltonPointLevel_gt_bound (B : Real) (i : Nat) :
    B < hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hB : B <= max B 0 := le_max_left B 0
  have hi : 0 < (i : Real) + 1 := by positivity
  linarith

private theorem hamiltonPointLevel_ge_index (B : Real) (i : Nat) :
    ((i : Real) + 1) <= hamiltonPointLevel B i := by
  unfold hamiltonPointLevel
  have hmax0 : 0 <= max B 0 := le_max_right B 0
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_scalar_blowup
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (hsec9 : HamiltonRicciNonnegative (I := I) P omega) :
    HamiltonScalarBlowup (I := I) P := by
  intro A
  by_cases hA : 0 < A
  · rcases P.curvUnbounded ((100 : Real) ^ 2 * A ^ 2) with
      ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' :
        (100 : Real) ^ 2 * A ^ 2 <
          hamiltonRiemannNormSq (I := I) (M := M) P t x := by
      simpa [hamiltonRiemannNormSq, hamiltonSolution] using hRm
    have hctl :=
      hamilton_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hsec9
        (t := t) (x := x) htD
    exact scalar_gt_of_rm hA hctl.1 hctl.2 hRm'
  · rcases P.curvUnbounded 0 with ⟨t, x, htD, hRm⟩
    refine ⟨t, x, htD, ?_⟩
    have hRm' : 0 < hamiltonRiemannNormSq (I := I) (M := M) P t x := by
      simpa [hamiltonRiemannNormSq, hamiltonSolution] using hRm
    have hctl :=
      hamilton_rm_scalar_ctl (I := I) (M := M) h0ω hM P hD hsec9
        (t := t) (x := x) htD
    have hRpos :
        0 < hamiltonScalar (I := I) P t x :=
      scalar_pos_of_rm hctl.1 hctl.2 hRm'
    exact lt_of_le_of_lt (le_of_not_gt hA) hRpos

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_exists_blowup_point_sequence
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hfinite : exists omega c0 : Real, exists h0ω : 0 < omega,
      P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω /\
        0 < c0 /\ omega <= 3 / (2 * c0))
    (hscalarBlowup : HamiltonScalarBlowup (I := I) P) :
    exists Q : HamiltonBlowup M, HamiltonBlowupPointSelection (I := I) P Q := by
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
        (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) half) :=
    hamilton_scalar_cont_slab (I := I) (M := M) h0ω P hD half hhalf_lt_omega
  have hbounded_half :
      DifferentialGeometry.PDE.RicciFlow.ScalarBoundedAboveOnSlab
        (M := M) (hamiltonScalar (I := I) P) half :=
    DifferentialGeometry.PDE.RicciFlow.ScalarBoundedAboveOnSlab.of_continuousOn
      (M := M) hcont_half
  rcases hbounded_half with ⟨Bhalf, hBhalf⟩
  let level : Nat -> Real := fun i => hamiltonPointLevel Bhalf i
  have hraw : ∀ i : Nat, ∃ t : Real, ∃ x : M,
      t ∈ P.D.carrier /\ level i < hamiltonScalar (I := I) P t x := by
    intro i
    exact hscalarBlowup (level i)
  let rawTime : Nat -> Real := fun i => Classical.choose (hraw i)
  let rawPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hraw i))
  have hraw_spec : ∀ i : Nat,
      rawTime i ∈ P.D.carrier /\
        level i < hamiltonScalar (I := I) P (rawTime i) (rawPoint i) := by
    intro i
    simpa [rawTime, rawPoint] using
      Classical.choose_spec (Classical.choose_spec (hraw i))
  have hraw_nonneg : ∀ i : Nat, 0 <= rawTime i := by
    intro i
    have hmem : rawTime i ∈
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
          h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.1
  have hraw_lt_omega : ∀ i : Nat, rawTime i < omega := by
    intro i
    have hmem : rawTime i ∈
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
          h0ω).carrier := by
      simpa [hD] using (hraw_spec i).1
    exact hmem.2
  have hmax_exists : ∀ i : Nat, ∃ tmax : Real, ∃ xmax : M,
      tmax ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          hamiltonScalar (I := I) P s y <=
            hamiltonScalar (I := I) P tmax xmax := by
    intro i
    exact slab_max_of_continuousOn (M := M)
      (f := fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
      (T := rawTime i) (t := rawTime i) (x := rawPoint i)
      (hamilton_scalar_cont_slab (I := I) (M := M) h0ω P hD (rawTime i) (hraw_lt_omega i))
      ⟨hraw_nonneg i, le_rfl⟩
  let qTime : Nat -> Real := fun i => Classical.choose (hmax_exists i)
  let qPoint : Nat -> M := fun i =>
    Classical.choose (Classical.choose_spec (hmax_exists i))
  have hq_spec : ∀ i : Nat,
      qTime i ∈ Set.Icc 0 (rawTime i) ∧
        ∀ s : Real, s ∈ Set.Icc 0 (rawTime i) -> ∀ y : M,
          hamiltonScalar (I := I) P s y <=
            hamiltonScalar (I := I) P (qTime i) (qPoint i) := by
    intro i
    simpa [qTime, qPoint] using
      Classical.choose_spec (Classical.choose_spec (hmax_exists i))
  let Q : HamiltonBlowup M := ⟨qPoint, qTime⟩
  refine ⟨Q, ?_⟩
  have hscale_lower : ∀ i : Nat,
      level i < hamiltonBlowupScale (I := I) P Q i := by
    intro i
    have hraw_le :=
      (hq_spec i).2 (rawTime i) ⟨hraw_nonneg i, le_rfl⟩ (rawPoint i)
    exact lt_of_lt_of_le (hraw_spec i).2 hraw_le
  have hscale_pos : ∀ i : Nat, 0 < hamiltonBlowupScale (I := I) P Q i := by
    intro i
    exact lt_trans (hamiltonPointLevel_pos Bhalf i) (hscale_lower i)
  have hq_gt_half : ∀ i : Nat, half < Q.time i := by
    intro i
    by_contra hnot
    have hle : Q.time i <= half := le_of_not_gt hnot
    have hmem_half : Q.time i ∈ Set.Icc 0 half :=
      ⟨(hq_spec i).1.1, hle⟩
    have hupper := hBhalf (Q.time i) hmem_half (Q.point i)
    have hB_lt_level : Bhalf < level i :=
      hamiltonPointLevel_gt_bound Bhalf i
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
        (hamiltonPointLevel_ge_index Bhalf i) hhalf_nonneg
    have hprod_gt : level i * half <
        hamiltonBlowupScale (I := I) P Q i * Q.time i := by
      nlinarith [hscale_lower i, hq_gt_half i,
        le_of_lt (hamiltonPointLevel_pos Bhalf i), hhalf_pos]
    exact le_of_lt
      (lt_of_le_of_lt
        (le_trans hA_le_Nhalf
          (le_trans hNhalf_le_ihalf
            (le_trans hihalf_le_i1half hi1half_le_levelhalf)))
        hprod_gt)
  · intro i
    have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htime0 : hamiltonRescaledTime (I := I) P Q i 0 = Q.time i := by
      dsimp [hamiltonRescaledTime]
      field_simp [hscale_ne]
      ring
    have hscalar0 :
        hamiltonScalar (I := I) P
            (hamiltonRescaledTime (I := I) P Q i 0) (Q.point i) =
          hamiltonBlowupScale (I := I) P Q i := by
      rw [htime0]
      rfl
    dsimp [hamiltonRescaledScalar]
    rw [hscalar0]
    field_simp [hscale_ne]
  · intro i s x hsleft hsright
    have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
      ne_of_gt (hscale_pos i)
    have htau_mem : hamiltonRescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (Q.time i) := by
      constructor
      · dsimp [hamiltonRescaledTime]
        have hdiv :
            -Q.time i <= s / hamiltonBlowupScale (I := I) P Q i := by
          have hdiv' :
              -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
                  hamiltonBlowupScale (I := I) P Q i <=
                s / hamiltonBlowupScale (I := I) P Q i :=
            div_le_div_of_nonneg_right hsleft (le_of_lt (hscale_pos i))
          have hleft :
              -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
                  hamiltonBlowupScale (I := I) P Q i = -Q.time i := by
            field_simp [hscale_ne]
          simpa [hleft] using hdiv'
        linarith
      · dsimp [hamiltonRescaledTime]
        have hdiv : s / hamiltonBlowupScale (I := I) P Q i <= 0 := by
          exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale_pos i))
        linarith
    have htau_raw : hamiltonRescaledTime (I := I) P Q i s ∈
        Set.Icc 0 (rawTime i) :=
      ⟨htau_mem.1, le_trans htau_mem.2 (hq_spec i).1.2⟩
    have hscalar_le :
        hamiltonScalar (I := I) P (hamiltonRescaledTime (I := I) P Q i s) x <=
          hamiltonBlowupScale (I := I) P Q i :=
      (hq_spec i).2 (hamiltonRescaledTime (I := I) P Q i s) htau_raw x
    dsimp [hamiltonRescaledScalar]
    have hmul :=
      mul_le_mul_of_nonneg_left hscalar_le
        (inv_nonneg.mpr (le_of_lt (hscale_pos i)))
    have hone :
        (hamiltonBlowupScale (I := I) P Q i)⁻¹ *
            hamiltonBlowupScale (I := I) P Q i = 1 := by
      field_simp [hscale_ne]
    simpa [hone] using hmul

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_fixed_pinching
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    HamiltonFixedPinching (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hpos0 :
      DifferentialGeometry.PDE.RicciFlow.RicciPosInit (I := I) (M := M)
        (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
          P.S.ricci) :=
    hamilton_initial_ricci_positive (I := I) (M := M) h0ω hpos P hD
  have hinit : DifferentialGeometry.PDE.RicciFlow.PinchInitLt (I := I) (M := M)
      (fun t : Real => P.S.base.metric t)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
      P.S.scalar :=
    DifferentialGeometry.PDE.RicciFlow.pinchInitLt_pos (I := I) (M := M)
      (G := fun t : Real => P.S.base.metric t)
      (Ric := DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
        P.S.ricci)
      (scalar := P.S.scalar)
      (DifferentialGeometry.PDE.RicciFlow.initialMetricRicciDataOfSolution
        (I := I) (M := M) P.S)
      (DifferentialGeometry.PDE.RicciFlow.initial_metric_ricci_data_positive
        (I := I) (M := M) P.S hpos0)
      (DifferentialGeometry.PDE.RicciFlow.initial_scalar_curvature_continuous_of_solution
        (I := I) (M := M) P.S
        P.isSmooth.isSolution
        (by
          rw [hD]
          exact ⟨le_rfl, h0ω⟩))
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
  exact DifferentialGeometry.PDE.RicciFlow.pinch_sol_closed (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdelta0 hdelta13 hdimT hTsub hTreg hpinch0

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_pinching
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    HamiltonPinching (I := I) P omega := by
  exact (hamilton_fixed_pinching (I := I) (M := M) h0ω hM hpos P hD).toVarying

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_ricci_nonnegative
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    HamiltonRicciNonnegative (I := I) P omega := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hpos0 := hamilton_initial_ricci_positive (I := I) (M := M) h0ω hpos P hD
  have hinit : DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime
      (I := I) (M := M)
      (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M) P.S.ricci)
        0 := by
    intro x v
    by_cases hv : v = 0
    · subst v
      have hbilin := DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin
        (I := I) (M := M) P.S.ricci 0 x
      have hzero :
          (DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily (I := I) (M := M)
            P.S.ricci)
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
  exact DifferentialGeometry.PDE.RicciFlow.ricci_nonnegative_of_closed_solution_wmp_data
    (I := I) (M := M) (S := P.S)
    P.isSmooth hT hdimT hTsub hTreg hinit

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_rescaled_ricci_nonnegative
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q) :
    HamiltonRescaledRicciNonnegative (I := I) P Q := by
  rcases hsel with ⟨hscale, htime, htimeMem, _hprod, _hbase, _hscalarMax⟩
  have hricOn : HamiltonRicciNonnegative (I := I) P omega :=
    hamilton_ricci_nonnegative (I := I) (M := M) h0ω hM hpos P hD
  intro i s x v hsleft hsright
  have hQiω : Q.time i < omega := by
    have hmem := htimeMem i
    rw [hD] at hmem
    exact hmem.2
  have hnonneg :=
    hricOn (Q.time i) (le_of_lt (htime i)) hQiω
  have hscale_ne : hamiltonBlowupScale (I := I) P Q i ≠ 0 :=
    ne_of_gt (hscale i)
  have hsdiv :
      -Q.time i <= s / hamiltonBlowupScale (I := I) P Q i := by
    have hdiv := div_le_div_of_nonneg_right hsleft (le_of_lt (hscale i))
    have hcancel :
        -(hamiltonBlowupScale (I := I) P Q i * Q.time i) /
            hamiltonBlowupScale (I := I) P Q i = -Q.time i := by
      field_simp [hscale_ne]
    rwa [hcancel] at hdiv
  have htau0 :
      0 <= hamiltonRescaledTime (I := I) P Q i s := by
    dsimp [hamiltonRescaledTime]
    linarith
  have htauT :
      hamiltonRescaledTime (I := I) P Q i s <= Q.time i := by
    dsimp [hamiltonRescaledTime]
    have hsdiv_nonpos :
        s / hamiltonBlowupScale (I := I) P Q i <= 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hsright (le_of_lt (hscale i))
    linarith
  have htau : hamiltonRescaledTime (I := I) P Q i s ∈ Set.Icc 0 (Q.time i) :=
    ⟨htau0, htauT⟩
  have hraw := hnonneg (hamiltonRescaledTime (I := I) P Q i s) htau x v
  simpa [DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci,
    DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt] using hraw

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_positive
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x := by
  classical
  rcases hM with ⟨hcompact, _hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  rcases hamilton_initial_scalar_minimum (I := I) (M := M) hdim h0ω hpos P hD with
    ⟨c0, hinit_min, hinit_pos⟩
  have hcont :
      forall T : Real, 0 <= T -> T < omega ->
        ContinuousOn (fun p : Real × M => hamiltonScalar (I := I) P p.1 p.2)
          (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    intro T _hT hTω
    exact hamilton_scalar_slab_continuous_on (I := I) (M := M) h0ω P hD T hTω
  have hc0 : 0 < c0 :=
    DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.pos_of_forall_pos
      (M := M) hinit_min hinit_pos
  rcases hamilton_scalar_slab_lipschitz (I := I) (M := M) (omega := omega) P c0 hc0 hcont with
    ⟨K, hK⟩
  have hreg :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          DifferentialGeometry.PDE.RicciFlow.ScalarLowerBoundWMPRegularity
            (I := I) (hamiltonMetricConnectionFamily (I := I) P) T 3 c0
            (hamiltonScalar (I := I) P) (K T) :=
    hamilton_scalar_weak_maximum_principle_regularity (I := I) (M := M) h0ω P hD c0 hc0 K
  have hevol :
      DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEquationOn
        (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω)
        (hamiltonScalar (I := I) P)
        (hamiltonScalarLaplacian (I := I) P)
        (hamiltonRicciNormSq (I := I) P) :=
    hamilton_scalar_evolution_equation (I := I) (M := M) h0ω P hD
  have hlap :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
            (I := I) (hamiltonMetricConnectionFamily (I := I) P) T
            (hamiltonScalar (I := I) P)
            (hamiltonScalarLaplacian (I := I) P) := by
    intro T _hT _hTω _hPole
    exact hamilton_scalar_laplacian_realizes_heat (I := I) (M := M) P T
  have hricci :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
            (1 / 3 : Real) * (hamiltonScalar (I := I) P t x) ^ 2 <=
              hamiltonRicciNormSq (I := I) P t x := by
    intro _T _hT _hTω _hPole t _ht x
    exact hamilton_scalar_sq_le_three_ricci_norm_sq (I := I) (M := M) hdim P t x
  have hF :
      ∀ T : Real, 0 < T -> T < omega ->
        T < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 ->
          ∀ t : Real, t ∈ Set.Icc 0 T ->
            LipschitzOnWith (K T)
              (fun a : Real => DifferentialGeometry.PDE.RicciFlow.scalarLowerReaction 3 a t)
              (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet (M := M) T
                (hamiltonScalar (I := I) P)
                (DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0)) := by
    intro T hT hTω hPole
    exact hK T hT hTω hPole
  have hfinite :
      omega <= DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 := by
    have hfin := DifferentialGeometry.PDE.RicciFlow.finiteTime3D (I := I) (M := M)
      h0ω (hamiltonMetricConnectionFamily (I := I) P) c0
      (hamiltonScalar (I := I) P) (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) K hinit_min hinit_pos hcont
      hreg hevol hlap hricci hF
    simpa [DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime] using hfin.2
  have hlower :
      DifferentialGeometry.PDE.RicciFlow.ScalarLowerBarrierBoundUpToPole
        (M := M) (hamiltonScalar (I := I) P) 3 c0 omega :=
    DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrierBoundUpToPole_of_scalarEvolution_closedOpen
      (I := I) h0ω (hamiltonMetricConnectionFamily (I := I) P) 3 c0 (by norm_num)
      hc0 (hamiltonScalar (I := I) P) (hamiltonScalarLaplacian (I := I) P)
      (hamiltonRicciNormSq (I := I) P) K hreg hevol hlap hricci
      (DifferentialGeometry.PDE.RicciFlow.InitialScalarMinimum.lowerBound (M := M) hinit_min) hF
  intro t htD x
  have ht_closed :
      t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega
        h0ω).carrier := by
    simpa [hD] using htD
  rcases ht_closed with ⟨ht0, htω⟩
  by_cases ht_zero : t = 0
  · have h0 := hinit_pos x
    simpa [hamiltonScalar, hamiltonSolution, ht_zero] using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
    have htblow : t < DifferentialGeometry.PDE.RicciFlow.scalarBlowupTime 3 c0 :=
      lt_of_lt_of_le htω hfinite
    have hbound :
        DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 c0 t <=
          hamiltonScalar (I := I) P t x :=
      hlower t htpos htω htblow x
    have hden :
        0 < 1 - (2 / (3 : Real)) * c0 * t :=
      DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier_denominator_pos_of_lt_blowup
        (n := 3) (c0 := c0) (by norm_num) hc0 (le_of_lt htpos) htblow
    have hpos_t :
        0 < hamiltonScalar (I := I) P t x :=
      DifferentialGeometry.PDE.RicciFlow.scalar_curvature_positive_of_lower_barrier
        (n := 3) (c0 := c0) (t := t) hbound hc0 hden
    simpa [hamiltonScalar, hamiltonSolution] using hpos_t

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_pinching_implies_pinch_estimate
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    HamiltonPinchingEstimate (I := I) P := by
  rcases hM with ⟨hcompact, hconnected, hboundaryless, hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    simpa using hdim
  have hfixed : HamiltonFixedPinching (I := I) P omega :=
    hamilton_fixed_pinching (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hnonneg : HamiltonRicciNonnegative (I := I) P omega :=
    hamilton_ricci_nonnegative (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ hpos P hD
  have hscalar :
      ∀ t : Real, t ∈ P.D.carrier -> ∀ x : M, 0 < P.S.scalar t x :=
    hamilton_scalar_positive (I := I) (M := M) h0ω
      ⟨hcompact, hconnected, hboundaryless, hdim⟩ g0 hpos P hD
  rcases DifferentialGeometry.PDE.RicciFlow.exists_pinching_estimate_of_smooth_solution (I := I) (M := M)
      P.S P.isSmooth h0ω hD hdimT hscalar hfixed hnonneg with
    ⟨epsilon, C, heps0, heps1, hC0, hest⟩
  exact ⟨epsilon, C, heps0, heps1, hC0, hest⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_pinching_implies_tracefree_pinch_estimate
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {omega : Real} (h0ω : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen 0 omega h0ω) :
    exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
      DifferentialGeometry.PDE.RicciFlow.HamiltonTracefreePinchingEstimateOn
        tracefreeRmNormSq scalar weight C := by
  rcases hamilton_pinching_implies_pinch_estimate (I := I) (M := M) h0ω hM g0 hpos P hD with
    ⟨epsilon, C, _heps0, _heps1, _hC0, hest⟩
  let tracefreeRmNormSq : Real -> M -> Real :=
    DifferentialGeometry.PDE.RicciFlow.carrierZeroExt (M := M) P.D
      (DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq P.S.scalar
        (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) P.S))
  let scalar : Real -> M -> Real :=
    DifferentialGeometry.PDE.RicciFlow.carrierScalarExt (M := M) P.D P.S.scalar
  let weight : Real -> M -> Real :=
    DifferentialGeometry.PDE.RicciFlow.carrierWeightExt (M := M) P.D P.S.scalar epsilon
  refine ⟨tracefreeRmNormSq, scalar, weight, C, ?_⟩
  have hdisplay :
      DifferentialGeometry.PDE.RicciFlow.PinchEstimateOn (M := M) tracefreeRmNormSq scalar weight C
        Set.univ := by
    simpa [tracefreeRmNormSq, scalar, weight] using
      DifferentialGeometry.PDE.RicciFlow.pinchEstimate_ext (M := M) (D := P.D) hest
  intro t x
  exact hdisplay t trivial x

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_rescaled_curvature_bound
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (hric : HamiltonRescaledRicciNonnegative (I := I) P Q) :
    HamiltonRiemannCurvatureBound (I := I) P Q := by
  classical
  rcases hM with ⟨_hcompact, _hconnected, _hboundaryless, hdim⟩
  rcases hsel with ⟨hscale, _htime, _htimeMem, _hprod, _hbase, hscalarMax⟩
  intro i s x hsleft hsright
  let τ : Real := hamiltonRescaledTime (I := I) P Q i s
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hricNonneg :
      DifferentialGeometry.Geometry.Curvature.RicciNonnegAt (I := I) (P.S.ricciAt τ x) := by
    intro v
    simpa [τ, DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt] using
      hric i s x v hsleft hsright
  have hricSym :
      DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (P.S.ricciAt τ x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := M) P.S τ x
  have hRmScalar :
      hamiltonRiemannNormSq (I := I) (M := M) P τ x <=
        (100 : Real) ^ 2 * (hamiltonScalar (I := I) P τ x) ^ 2 := by
    have hpoint :=
      DifferentialGeometry.Geometry.Curvature.normSqLeOfFirstTrace
        (I := I) (M := M) (g := P.S.base.metric τ)
        (Ric := P.S.ricciAt τ x) (scalar := P.S.scalar τ x)
        (Rm04 := P.S.base.rm04 τ x) hdimT hricSym hricNonneg
        (fun basis horth =>
          DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := M) P.S horth)
    simpa [hamiltonRiemannNormSq, hamiltonScalar, hamiltonSolution, τ] using hpoint
  have hscalarNonneg : 0 <= hamiltonScalar (I := I) P τ x := by
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigenBasis3
        (I := I) (M := M) (P.S.base.metric τ) (P.S.ricciAt τ x)
        hdimT hricSym hricNonneg with
      ⟨basis, l1, l2, l3, horth, hdiag, h1, h2, h3⟩
    have hScalarTrace :
        DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
          (P.S.scalar τ x) (P.S.ricciAt τ x) DifferentialGeometry.Geometry.Curvature.delta3
            basis := by
      have htr :=
        DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (P.S.base.metric τ)
          (P.S.ricciAt τ x) horth
      simpa [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
    have hscalar_eq :
        P.S.scalar τ x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
      DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
    change 0 <= P.S.scalar τ x
    rw [hscalar_eq]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    nlinarith
  have hscalarUpper :
      hamiltonScalar (I := I) P τ x <= hamiltonBlowupScale (I := I) P Q i := by
    have hraw := hscalarMax i s x hsleft hsright
    have hmul :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt (hscale i))
    have hleft :
        hamiltonBlowupScale (I := I) P Q i *
            hamiltonRescaledScalar (I := I) P Q i s x =
          hamiltonScalar (I := I) P τ x := by
      dsimp [hamiltonRescaledScalar, τ]
      field_simp [ne_of_gt (hscale i)]
    have hright :
        hamiltonBlowupScale (I := I) P Q i * (1 : Real) =
          hamiltonBlowupScale (I := I) P Q i := by
      ring
    simpa [hleft, hright] using hmul
  have hscalarSq :
      (hamiltonScalar (I := I) P τ x) ^ 2 <=
        (hamiltonBlowupScale (I := I) P Q i) ^ 2 := by
    have hdiff :
        0 <= hamiltonBlowupScale (I := I) P Q i -
          hamiltonScalar (I := I) P τ x := by
      linarith
    have hsum :
        0 <= hamiltonBlowupScale (I := I) P Q i +
          hamiltonScalar (I := I) P τ x := by
      nlinarith [hscalarNonneg, le_of_lt (hscale i)]
    have hprod :
        0 <=
          (hamiltonBlowupScale (I := I) P Q i -
              hamiltonScalar (I := I) P τ x) *
            (hamiltonBlowupScale (I := I) P Q i +
              hamiltonScalar (I := I) P τ x) :=
      mul_nonneg hdiff hsum
    nlinarith
  have hscaled :
      (100 : Real) ^ 2 * (hamiltonScalar (I := I) P τ x) ^ 2 <=
        (100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2 :=
    mul_le_mul_of_nonneg_left hscalarSq (by norm_num)
  exact le_trans hRmScalar hscaled

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_reference_radius_window
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q) :
    HamiltonWindow (I := I) P Q hamilton_reference_radius := by
  rcases hsel with ⟨_hscale, _htime, _htimeMem, hprod, _hbase, _hscalarMax⟩
  rcases hprod (hamilton_reference_radius ^ 2) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi s hsleft hsright
  have hprod_i :
      hamilton_reference_radius ^ 2 <= hamiltonBlowupScale (I := I) P Q i * Q.time i := hN i hi
  constructor
  · linarith
  · exact hsright

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_blowup_scale_tendsto_atTop
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q) :
    Filter.Tendsto (hamiltonBlowupScale (I := I) P Q)
      Filter.atTop Filter.atTop := by
  rcases hsel with ⟨hscale, _htime, htimeMem, hprod, _hbase, _hscalarMax⟩
  rw [Filter.tendsto_atTop]
  intro A
  rcases hprod (A * omega) with ⟨N, hN⟩
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun i hi => hi⟩] with i hi
  have hprod_i :
      A * omega ≤ hamiltonBlowupScale (I := I) P Q i * Q.time i :=
    hN i hi
  have htime_i := htimeMem i
  rw [hD] at htime_i
  have hlt :
      hamiltonBlowupScale (I := I) P Q i * Q.time i <
        hamiltonBlowupScale (I := I) P Q i * omega :=
    mul_lt_mul_of_pos_left htime_i.2 (hscale i)
  exact le_of_lt
    (lt_of_mul_lt_mul_right (lt_of_le_of_lt hprod_i hlt) h0omega.le)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_pinching_error_tendsto_zero
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (L : HamiltonCGHLimit (I := I) M)
    {epsilon C : Real} (hepsilon : 0 < epsilon) :
    Filter.Tendsto
      (fun k : Nat =>
        C * hamiltonBlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
      Filter.atTop (nhds 0) := by
  have hscale :
      Filter.Tendsto
        (fun k : Nat => hamiltonBlowupScale (I := I) P Q (L.subseq k))
        Filter.atTop Filter.atTop :=
    (hamilton_blowup_scale_tendsto_atTop (I := I) h0omega P hD Q hsel).comp
      L.subseq_strict.tendsto_atTop
  have hpow :
      Filter.Tendsto
        (fun k : Nat =>
          hamiltonBlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hepsilon).comp hscale
  simpa only [mul_zero] using tendsto_const_nhds.mul hpow

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_eventually_rescaled_radius_ge
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (r rho : Real) (hr : 0 < r) (hrho : 0 < rho) :
    exists N : Nat, forall i : Nat, N <= i ->
      r <= Real.sqrt (hamiltonBlowupScale (I := I) P Q i) * rho := by
  rcases hsel with ⟨hscale, _htime, htimeMem, hprod, _hbase, _hscalarMax⟩
  let C : Real := (r / rho) ^ 2
  rcases hprod (C * omega) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi
  have hprod_i :
      C * omega <= hamiltonBlowupScale (I := I) P Q i * Q.time i := hN i hi
  have htime_i := htimeMem i
  rw [hD] at htime_i
  have hprod_lt :
      hamiltonBlowupScale (I := I) P Q i * Q.time i <
        hamiltonBlowupScale (I := I) P Q i * omega :=
    mul_lt_mul_of_pos_left htime_i.2 (hscale i)
  have hscale_lower : C < hamiltonBlowupScale (I := I) P Q i := by
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hprod_i hprod_lt) h0omega.le
  have hsqrt :
      Real.sqrt C <= Real.sqrt (hamiltonBlowupScale (I := I) P Q i) :=
    Real.sqrt_le_sqrt (le_of_lt hscale_lower)
  have hquot_nonneg : 0 <= r / rho := (div_pos hr hrho).le
  have hsqrt' :
      r / rho <= Real.sqrt (hamiltonBlowupScale (I := I) P Q i) := by
    simpa only [C, Real.sqrt_sq hquot_nonneg] using hsqrt
  have hmul := mul_le_mul_of_nonneg_right hsqrt' hrho.le
  calc
    r = (r / rho) * rho := (div_mul_cancel₀ r (ne_of_gt hrho)).symm
    _ <= Real.sqrt (hamiltonBlowupScale (I := I) P Q i) * rho := hmul

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_rescaled_curvature_control
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (hrm : HamiltonRiemannCurvatureBound (I := I) P Q)
    (hwindow : HamiltonWindow (I := I) P Q hamilton_reference_radius) :
    HamiltonRiemannCurvatureControl (I := I) P Q hsel hamilton_reference_radius := by
  rcases hwindow with ⟨N, hN⟩
  refine ⟨hamilton_reference_radius_pos, N, ?_⟩
  intro i hi
  let B := hamiltonRescaledBall (I := I) P Q hsel i hamilton_reference_radius hamilton_reference_radius_pos
  change B.IsRmControlled
  unfold Perelman.FlowMetricBall.IsRmControlled
  dsimp [B, hamiltonRescaledBall, hamiltonRescaledInitialTime]
  constructor
  · intro s hs
    have hw := hN i hi s (by simpa using hs.1) (by simpa using hs.2)
    rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_carrier]
    change hamiltonRescaledTime (I := I) P Q i s ∈ P.D.carrier
    rw [hD]
    have hscale := hsel.1 i
    have htimeMem := hsel.2.2.1 i
    rw [hD] at htimeMem
    have hnum : 0 <= hamiltonBlowupScale (I := I) P Q i * Q.time i + s := by
      linarith [hw.1]
    have hlo : 0 <= hamiltonRescaledTime (I := I) P Q i s := by
      rw [show hamiltonRescaledTime (I := I) P Q i s =
          (hamiltonBlowupScale (I := I) P Q i * Q.time i + s) /
            hamiltonBlowupScale (I := I) P Q i by
        unfold hamiltonRescaledTime
        field_simp [ne_of_gt hscale]]
      exact div_nonneg hnum (le_of_lt hscale)
    have hsdiv : s / hamiltonBlowupScale (I := I) P Q i <= 0 :=
      div_nonpos_of_nonpos_of_nonneg hw.2 (le_of_lt hscale)
    have hhi : hamiltonRescaledTime (I := I) P Q i s < omega := by
      unfold hamiltonRescaledTime
      linarith [htimeMem.2, hsdiv]
    exact ⟨hlo, hhi⟩
  · intro s hs x _hx
    have hw := hN i hi s (by simpa using hs.1) (by simpa using hs.2)
    have hscale := hsel.1 i
    have hold := hrm i s x hw.1 hw.2
    have hold' :
        Tensor0SBundle.normSq0S (I := I)
            (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
              (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s)) x 4
            (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
              (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s) x) <=
          (100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2 := by
      simpa [hamiltonRiemannNormSq, hamiltonSolution, hamiltonRescaledTime] using hold
    unfold Perelman.FlowMetricBall.rmNormSq hamiltonRescaledSolution
    rw [DifferentialGeometry.PDE.RicciFlow.paraRmNormSq]
    have hmul := mul_le_mul_of_nonneg_left hold'
      (mul_nonneg (by positivity : 0 <= hamilton_reference_radius ^ 4)
        (sq_nonneg (hamiltonBlowupScale (I := I) P Q i)⁻¹))
    calc
      hamilton_reference_radius ^ 4 *
          ((hamiltonBlowupScale (I := I) P Q i)⁻¹ ^ 2 *
            Tensor0SBundle.normSq0S (I := I)
              (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
                (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s)) x 4
              (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
                (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s) x)) =
          (hamilton_reference_radius ^ 4 * (hamiltonBlowupScale (I := I) P Q i)⁻¹ ^ 2) *
            Tensor0SBundle.normSq0S (I := I)
              (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
                (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s)) x 4
              (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
                (Q.time i) (hamiltonBlowupScale (I := I) P Q i) s) x) := by ring
      _ <= (hamilton_reference_radius ^ 4 * (hamiltonBlowupScale (I := I) P Q i)⁻¹ ^ 2) *
          ((100 : Real) ^ 2 * (hamiltonBlowupScale (I := I) P Q i) ^ 2) := hmul
      _ = 1 := by
        field_simp [ne_of_gt hscale]
        norm_num [hamilton_reference_radius]

omit [NeZero (Module.finrank ℝ E)] in
theorem hamilton_noncollapse_of_no_local_collapsing
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (hrm : HamiltonRiemannCurvatureControl (I := I) P Q hsel hamilton_reference_radius)
    {rho : Real} (hnlc : Perelman.NoLocalCollapsing P.S rho) :
    exists kappa : Real,
      HamiltonNoncollapse (I := I) P Q hsel kappa hamilton_reference_radius := by
  rcases hnlc with ⟨kappa, hkappa, hbelow⟩
  rcases hrm with ⟨hr, Nrm, hRm⟩
  rcases hamilton_eventually_rescaled_radius_ge (I := I) h0omega P hD Q hsel
      hamilton_reference_radius rho hr hbelow.1 with ⟨Nscale, hscale⟩
  refine ⟨kappa, hkappa, hr, Nat.max Nrm Nscale, ?_⟩
  intro i hi
  have hiRm : Nrm <= i := le_trans (Nat.le_max_left Nrm Nscale) hi
  have hiScale : Nscale <= i := le_trans (Nat.le_max_right Nrm Nscale) hi
  let B := hamiltonRescaledBall (I := I) P Q hsel i hamilton_reference_radius hr
  have hRm_i : B.IsRmControlled := hRm i hiRm
  have hbelow_i := Perelman.para_noncollapse (I := I) P.S (Q.time i)
    (hamiltonBlowupScale (I := I) P Q i) (hsel.1 i) (hsel.2.2.1 i)
    kappa rho hbelow
  have hkappa_i : B.IsKappaNoncollapsed kappa :=
    hbelow_i.2 (hamiltonRescaledInitialTime (I := I) P Q hsel i) B
      (hscale i hiScale) hRm_i
  exact ⟨hRm_i, hkappa_i⟩

theorem hamilton_noncollapse
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (hD : P.D = DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      0 omega h0omega)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (_hrm : HamiltonRiemannCurvatureControl (I := I) P Q hsel hamilton_reference_radius) :
    exists kappa : Real, HamiltonNoncollapse (I := I) P Q hsel kappa hamilton_reference_radius := by
  classical
  letI : CompactSpace M := hM.1
  letI : ConnectedSpace M := hM.2.1
  letI : I.Boundaryless := hM.2.2.1
  have hsol :
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) P.S :=
    P.isSmooth.isSolution
  have hnlc : Perelman.NoLocalCollapsing P.S hamilton_reference_radius := by
    have htransport :
        ∀ (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
          (hD' : D =
            DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
              0 omega h0omega)
          (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn
            (I := I) (M := M) D),
          DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S →
            Perelman.NoLocalCollapsing S hamilton_reference_radius := by
      intro D hD' S hS
      subst D
      exact Perelman.no_local_open (I := I) (M := M) h0omega
        S hS hM.2.2.2 hamilton_reference_radius_pos
    exact htransport P.D hD P.S hsol
  exact hamilton_noncollapse_of_no_local_collapsing
    (I := I) h0omega P hD Q hsel _hrm hnlc

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem limit_mid_regular
    {L : HamiltonCGHLimit (I := I) M}
    (hreg : HamiltonLimitRegularWindow (I := I) L) :
    -(hamilton_reference_radius ^ 2) / 2 ∈ L.D.regular := by
  apply hreg
  have hsq : 0 < hamilton_reference_radius ^ 2 := sq_pos_of_ne_zero hamilton_reference_radius_pos.ne'
  constructor <;> nlinarith

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_ric_nonneg
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (hric : HamiltonRescaledRicciNonnegative (I := I) P Q)
    {L : HamiltonCGHLimit (I := I) M}
    (hreal : HamiltonSourceRealization (I := I) P Q hsel L)
    (htransfer : HamiltonRicciNonnegativeTransfer (I := I) P Q hsel L) :
    LimitRicNonneg (I := I) L := by
  exact htransfer hreal hric

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_base_scalar_one
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    {L : HamiltonCGHLimit (I := I) M}
    (hconv : HamiltonLimitBaseScalarConvergence (I := I) P Q L) :
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
      hamiltonRescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k))
  have hconv' : Filter.Tendsto f Filter.atTop
      (nhds (L.S.scalar 0 L.basepoint)) := by
    simpa [HamiltonLimitBaseScalarConvergence, f] using hconv
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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem limit_scalar_nonneg
    {L : HamiltonCGHLimit (I := I) M}
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
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N)
      (L.S.base.metric t) (L.S.ricciAt t x)
      (by simpa using hdim)
      (DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hl1 : 0 <= l1 := by
    have h := hnonneg t ht x (basis 0)
    have hcomp := hdiag.2 0 0
    rw [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0))
          = l1 := by
      simpa [DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hcomp
    rwa [hval] at h
  have hl2 : 0 <= l2 := by
    have h := hnonneg t ht x (basis 1)
    have hcomp := hdiag.2 1 1
    rw [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 1) (basis 1))
          = l2 := by
      simpa [DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hcomp
    rwa [hval] at h
  have hl3 : 0 <= l3 := by
    have h := hnonneg t ht x (basis 2)
    have hcomp := hdiag.2 2 2
    rw [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply] at hcomp
    have hval :
        L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 2) (basis 2))
          = l3 := by
      simpa [DifferentialGeometry.Geometry.Curvature.ricciDiag3] using hcomp
    rwa [hval] at h
  have hScalarTrace :
      DifferentialGeometry.Geometry.Curvature.ScalarRealizesRicciTraceAt (I := I)
        (L.S.scalar t x) (L.S.ricciAt t x) DifferentialGeometry.Geometry.Curvature.delta3
          basis := by
    have htr :=
      DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (L.S.base.metric t)
        (L.S.ricciAt t x) horth
    simpa [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar_eq :
      L.S.scalar t x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 :=
    DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hScalarTrace hdiag
  rw [hscalar_eq]
  unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
  nlinarith

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_inherit
    (g0 : SmoothRiemannianMetric I M)
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    (_hric : HamiltonRescaledRicciNonnegative (I := I) P Q)
    (_hcgh : HamiltonCGHLimitExistence (I := I) P Q hsel) :
    exists L : HamiltonCGHLimit (I := I) M,
      HamiltonSourceRealization (I := I) P Q hsel L /\
      HamiltonLimitSubsequence (I := I) L /\
      HamiltonLimitWindow (I := I) L /\
        HamiltonLimitRegularWindow (I := I) L /\
        HamiltonLimitConnected (I := I) L /\
        HamiltonLimitBoundaryless (I := I) /\
        HamiltonLimitFlow (I := I) L /\
        HamiltonRicciNonnegativeTransfer (I := I) P Q hsel L /\
        HamiltonPinchingTransfer (I := I) P Q hsel L /\
        LimitRicNonneg (I := I) L /\
        LimitBaseScalarOne (I := I) L /\
        LimitScalarPos (I := I) L := by
  rcases _hcgh with
    ⟨L, hreal, hsubseq, hwindow, hregwin, hconn, hbdry, hflow,
      hricTransfer, hbaseconv, hscalarPos, hpinchTransfer⟩
  have hlimit :
      HamiltonLimitSubsequence (I := I) L /\
      HamiltonLimitWindow (I := I) L /\
        HamiltonLimitRegularWindow (I := I) L /\
        HamiltonLimitConnected (I := I) L /\
        HamiltonLimitBoundaryless (I := I) /\
        HamiltonLimitFlow (I := I) L :=
    ⟨hsubseq, hwindow, hregwin, hconn, hbdry, hflow⟩
  have hnonneg : LimitRicNonneg (I := I) L :=
    limit_ric_nonneg (I := I) (M := M) g0 P Q hsel _hric
      hreal hricTransfer
  have hbase : LimitBaseScalarOne (I := I) L :=
    limit_base_scalar_one (I := I) (M := M) P Q hsel hbaseconv
  exact ⟨L, hreal, hsubseq, hwindow, hregwin, hconn, hbdry, hflow,
    hricTransfer, hpinchTransfer, hnonneg, hbase, hscalarPos⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_tracefree_decay
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    {L : HamiltonCGHLimit (I := I) M}
    (hreal : HamiltonSourceRealization (I := I) P Q hsel L)
    (htransfer : HamiltonPinchingTransfer (I := I) P Q hsel L)
    (hpinch : HamiltonPinchingEstimate (I := I) P)
    (hscalarPos : LimitScalarPos (I := I) L) :
    LimitTracefreeDecay (I := I) L := by
  exact htransfer hreal hpinch hscalarPos

omit [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [T2Space M] in
theorem tracefree_zero_of_decay
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    {t : Real}
    (hdecay : LimitTracefreeDecayAt (I := I) L t) :
    LimitTracefreeZeroAt (I := I) L t := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  intro x
  let q : Real :=
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x
  have hnonneg : 0 <= q := by
    have hdimT :
        forall (_t : Real) (y : L.N),
          Module.finrank Real (TangentSpace I y) = 3 := by
      intro _ y
      simpa using hdim
    simpa [q] using
      (DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_nonneg (I := I) (M := L.N) L.S hdimT t x)
  have hle0 : q <= 0 := by
    have hforall : forall ε : Real, 0 < ε -> q <= 0 + ε := by
      intro ε hε
      simpa [q] using hdecay x ε hε
    exact le_of_forall_pos_le_add hforall
  simpa [q] using le_antisymm hle0 hnonneg

omit [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [T2Space M] in
theorem limit_tracefree_zero_of_decay
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hdecay : LimitTracefreeDecay (I := I) L) :
    LimitTracefreeZero (I := I) L := by
  intro t ht
  exact tracefree_zero_of_decay (I := I) (M := M) hdim (hdecay t ht)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_tracefree_zero
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : HamiltonBlowupPointSelection (I := I) P Q)
    {L : HamiltonCGHLimit (I := I) M}
    (hreal : HamiltonSourceRealization (I := I) P Q hsel L)
    (htransfer : HamiltonPinchingTransfer (I := I) P Q hsel L)
    (hpinch : HamiltonPinchingEstimate (I := I) P)
    (_hscalarPos : LimitScalarPos (I := I) L) :
    LimitTracefreeZero (I := I) L := by
  exact limit_tracefree_zero_of_decay (I := I) (M := M) hdim
    (limit_tracefree_decay (I := I) (M := M) P Q hsel hreal htransfer hpinch
      _hscalarPos)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem limitEinstein_of_tf0
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    {t0 : Real} (htf : LimitTracefreeZeroAt (I := I) L t0) :
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
  have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (M := L.N) Ric :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g Ric hdimT
    hsym with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (M := L.N) g Ric horth
  have hscalar :
      L.S.scalar t0 x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
    calc
      L.S.scalar t0 x =
          DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (M := L.N)
            (L.S.family.metric t0) (L.S.ricciAt t0 x) :=
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace (I := I) (M := L.N)
              L.S t0 x
      _ = DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (M := L.N) g
        Ric := by
            rfl
      _ = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
            exact DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (M := L.N) g basis horth
  have hnorm :
      DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S t0 x =
        DifferentialGeometry.PDE.RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
    calc
      DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S t0 x =
          Tensor0SBundle.normSq0S (I := I) (M := L.N) g x 2 Ric := by
            rfl
      _ = DifferentialGeometry.PDE.RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
            exact (DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner (I := I) (M := L.N)
              g Ric basis hinv).symm
  have htf_eigen :
      DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3 l1 l2 l3 = 0 := by
    have htf_x := htf x
    rw [DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
      hscalar, hnorm,
      DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag (I := I) (M := L.N) hdiag] at htf_x
    simpa [DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt,
      DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues] using htf_x
  have heq :=
    (DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3_eq_zero_iff l1 l2 l3).1
      htf_eigen
  rcases heq with ⟨h12, h23⟩
  have hscalar_l1 : L.S.scalar t0 x / 3 = l1 := by
    rw [hscalar, h12, h23]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    ring
  let T := DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) (M := L.N) g Ric
  rcases DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec (I := I) (M := L.N) g
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
    L.S.ricciAt t0 x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
        g.inner x (T v) w := by
          exact (DifferentialGeometry.Geometry.Curvature.ricciEnd_inner (I := I) (M := L.N) g Ric v
            w).symm
    _ = g.inner x (l1 • v) w := by rw [hT_all]
    _ = l1 * g.inner x v w := by simp
    _ = (L.S.scalar t0 x / 3) * (L.S.base.metric t0).inner x v w := by
          rw [hscalar_l1]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
theorem limit_round_base
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : HamiltonLimitConnected (I := I) L)
    (hbdry : HamiltonLimitBoundaryless (I := I))
    {t0 : Real}
    (hbase :
      letI : TopologicalSpace L.N := L.topology
      letI : ChartedSpace H L.N := L.charted
      letI : IsManifold I ∞ L.N := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
      letI : SigmaCompactSpace L.N := L.sigmaCompact
      letI : T2Space L.N := L.t2
      0 < L.S.scalar t0 L.basepoint)
    (heinstein : LimitEinsteinAt (I := I) L t0) :
    LimitRoundAt (I := I) L t0 := by
  classical
  letI : NeZero (Module.finrank Real E) := ⟨by omega⟩
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  haveI : ConnectedSpace L.N := by
    simpa [HamiltonLimitConnected] using hconn
  haveI : I.Boundaryless := by
    simpa [HamiltonLimitBoundaryless] using hbdry
  let g : SmoothRiemannianMetric I L.N := L.S.base.metric t0
  have hEinStatic :
      ∀ y : L.N, ∀ v w : TangentSpace I y,
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := L.N) g y
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
          (DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) (M := L.N) g y / 3) *
            g.inner y v w := by
    intro y v w
    have h := heinstein y v w
    simpa [g, LimitEinsteinAt, DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt,
        DifferentialGeometry.Geometry.Curvature.metricRicciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
        DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt] using h
  have hdScalar :
      ∀ x : L.N, ∀ X : TangentSpace I x,
        DifferentialGeometry.Geometry.Operator.differential1FormFun (I := I)
            (fun y : L.N =>
              DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) (M := L.N) g y)
            x (fun _ : Fin 1 => X) = 0 := by
    intro x X
    have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
      simpa using hdim
    have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I)
        (L.S.ricciAt t0 x) :=
      DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g
        (L.S.ricciAt t0 x) hdimT hsym with
      ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
    have hinv :
        Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
          DifferentialGeometry.Geometry.Curvature.delta3 :=
      DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (M := L.N) g basis
        horth
    exact DifferentialGeometry.Geometry.Curvature.dScalar_zero_ein3_at (I := I) (M := L.N) g basis
      DifferentialGeometry.Geometry.Curvature.delta3 hinv hEinStatic X
  rcases DifferentialGeometry.Geometry.Curvature.metricScalar_const_of_dScalar_zero (I := I)
    (M := L.N) g
      hdScalar with
    ⟨R0, hR0_metric⟩
  have hR0_scalar : ∀ x : L.N, L.S.scalar t0 x = R0 := by
    intro x
    have hx := hR0_metric x
    simpa [g, DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt] using hx
  have hR0_pos : 0 < R0 := by
    rw [hR0_scalar L.basepoint] at hbase
    exact hbase
  have hRic :
      forall x : L.N, forall v : TangentSpace I x,
        (((Module.finrank Real E : Real) - 1) * (R0 / 6)) * g.inner x v v <=
          DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    intro x v
    rw [hEinStatic x v v, hR0_metric x, hdim]
    convert le_rfl using 1
    all_goals ring
  refine ⟨R0 / 6, by nlinarith, hRic, R0 / 6, by nlinarith, ?_⟩
  intro x X Y
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I)
      (L.S.ricciAt t0 x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g
      (L.S.ricciAt t0 x) hdimT hsym with
    ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
  have htrace :=
    DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := L.N) L.S
      (t := t0) (x := x) (basis := basis) horth
  have hEinCompNeg : ∀ i j : Fin 3,
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (-(L.S.ricciAt t0 x)) i j
        =
        ((-L.S.scalar t0 x) / 3) * DifferentialGeometry.Geometry.Curvature.delta3 i j := by
    intro i j
    have hij := heinstein x (basis i) (basis j)
    rw [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply]
    change -(L.S.ricciAt t0 x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j))) =
      ((-L.S.scalar t0 x) / 3) * DifferentialGeometry.Geometry.Curvature.delta3 i j
    rw [hij]
    rw [horth i j]
    ring
  have hRm :=
    DifferentialGeometry.Geometry.Curvature.rm04_einstein3_at (I := I) (M := L.N) htrace
      hEinCompNeg X Y
  have hscalar_x : L.S.scalar t0 x = R0 := hR0_scalar x
  calc
    DifferentialGeometry.Geometry.Curvature.metricRm04StdAt (I := I) (M := L.N) g x X Y Y X =
        L.S.base.rm04 t0 x (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Y X) := by
          rfl
    _ = -((-L.S.scalar t0 x) / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := hRm
    _ = (R0 / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := by
          rw [hscalar_x]
          ring

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
theorem limit_round_of_ein
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : HamiltonLimitConnected (I := I) L)
    (hbdry : HamiltonLimitBoundaryless (I := I))
    {t0 : Real}
    (hscalar : LimitScalarPosAt (I := I) L t0)
    (heinstein : LimitEinsteinAt (I := I) L t0) :
    LimitRoundAt (I := I) L t0 := by
  exact limit_round_base (I := I) (M := M) hdim hconn hbdry
    (hscalar L.basepoint) heinstein

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
theorem limit_const_sec_of_einstein
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : HamiltonLimitConnected (I := I) L)
    (hbdry : HamiltonLimitBoundaryless (I := I))
    {t0 : Real}
    (hscalar : LimitScalarPosAt (I := I) L t0)
    (heinstein : LimitEinsteinAt (I := I) L t0) :
    LimitConstPosSec (I := I) L := by
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  rcases limit_round_of_ein (I := I) (M := M) hdim hconn hbdry hscalar
      heinstein with
    ⟨_K, _hK, _hRic, hsec⟩
  exact ⟨L.S.base.metric t0, hsec⟩

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem const_pos_of_tf0
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : HamiltonLimitConnected (I := I) L)
    (hbdry : HamiltonLimitBoundaryless (I := I))
    {t0 : Real}
    (hscalar : LimitScalarPosAt (I := I) L t0)
    (htf : LimitTracefreeZeroAt (I := I) L t0) :
    LimitConstPosSec (I := I) L := by
  letI : NeZero (Module.finrank Real E) := ⟨by omega⟩
  have heinstein : LimitEinsteinAt (I := I) L t0 :=
    limitEinstein_of_tf0 (I := I) (M := M) hdim htf
  exact limit_const_sec_of_einstein (I := I) (M := M) hdim hconn hbdry
    hscalar heinstein

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem limit_const_pos
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hreg : HamiltonLimitRegularWindow (I := I) L)
    (hconn : HamiltonLimitConnected (I := I) L)
    (hbdry : HamiltonLimitBoundaryless (I := I))
    (hscalarPos : LimitScalarPos (I := I) L)
    (htf : LimitTracefreeZero (I := I) L) :
    LimitConstPosSec (I := I) L := by
  let t0 : Real := -(hamilton_reference_radius ^ 2) / 2
  have ht0 : t0 ∈ L.D.regular := by
    simpa [t0] using limit_mid_regular (I := I) (M := M) hreg
  exact const_pos_of_tf0 (I := I) (M := M) hdim hconn hbdry
    (hscalarPos t0 ht0) (htf t0 ht0)

theorem limit_to_orig
    (hM : Closed3Manifold (I := I) (M := M))
    {L : HamiltonCGHLimit (I := I) M}
    {t : Real} (_ht : t ∈ L.D.carrier)
    (_hconn : HamiltonLimitConnected (I := I) L)
    (_hround : LimitRoundAt (I := I) L t) :
    exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  letI : T2Space (TangentBundle I L.N) := L.t2TangentBundle
  haveI : ConnectedSpace L.N := by
    simpa [HamiltonLimitConnected] using _hconn
  haveI : ConnectedSpace M := hM.2.1
  haveI : I.Boundaryless := hM.2.2.1
  let g : SmoothRiemannianMetric I L.N := L.S.base.metric t
  change exists K : Real, 0 < K /\
    (forall x : L.N, forall v : TangentSpace I x,
      (((Module.finrank Real E : Real) - 1) * K) * g.inner x v v <=
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /\
    ConstPosSecMetric (I := I) (M := L.N) g at _hround
  rcases _hround with ⟨K, hK, hRic, hsecg⟩
  have hRicBM :
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (((Module.finrank Real E : Real) - 1) * K) := by
    intro x v
    rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor]
    exact hRic x v
  have hcomplete :
      DifferentialGeometry.HCGCompactness.MetricComplete
        (I := I) (L.limit.atTime (I := I) t) := by
    simpa [HamiltonCGHLimit.limit, g] using L.limitComplete t _ht
  have hdim : 2 <= Module.finrank Real E := by
    have hdim3 : Module.finrank Real E = 3 := hM.2.2.2
    omega
  letI : CompactSpace L.N :=
    DifferentialGeometry.HCGCompactness.PointedRiemannianManifold.compact_of_ricci
      (I := I) (P := L.limit.atTime (I := I) t) (by
        simpa [HamiltonCGHLimit.limit, HamiltonLimitConnected] using _hconn)
      hdim hK (by simpa [HamiltonCGHLimit.limit, g] using hRicBM) hcomplete
  let Phi := L.cgh.spatial.maps
  obtain ⟨k, hk⟩ :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.exists_source_univ
      (I := I) Phi (isCompact_univ : IsCompact (Set.univ : Set L.N))
  have hsource : Phi.source k = Set.univ := hk k le_rfl
  let j : Nat := L.cghSubseq k
  letI : TopologicalSpace (L.sourceTerm j).M := (L.sourceTerm j).topology
  letI : ChartedSpace H (L.sourceTerm j).M := (L.sourceTerm j).charted
  letI : ConnectedSpace (L.sourceTerm j).M :=
    (L.sourceToOrig j).symm.surjective.connectedSpace (L.sourceToOrig j).symm.continuous
  have htarget : Phi.target k = Set.univ :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.target_univ
      (I := I) Phi k (isCompact_univ : IsCompact (Set.univ : Set L.N))
        inferInstance hsource
  let limitToSource : L.N ≃ₘ⟮I, I⟯ (L.sourceTerm j).M :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.globalDiffeomorph
      (I := I) Phi k hsource htarget
  let limitToOrig : L.N ≃ₘ⟮I, I⟯ M :=
    limitToSource.trans (L.sourceToOrig j)
  rcases hsecg with ⟨c, hc, hsec⟩
  refine ⟨Diffeomorph.pullbackMetricCross g limitToOrig.symm, c, hc, fun x X Y => ?_⟩
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04Std_pullbackCross
        g limitToOrig.symm x X Y Y X, hsec,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x X X,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x Y Y,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x X Y]

omit [NeZero (Module.finrank ℝ E)] in
theorem constant_positive_sectional_curvature_implies_spherical_space_form
    (hM : Closed3Manifold (I := I) (M := M))
    (hconst : AdmitsConstPosSec (I := I) (M := M)) :
    SphericalSpaceForm (I := I) (M := M) := by
  obtain ⟨hcompact, hconn, hbdry, hdim⟩ := hM
  obtain ⟨g, c, hc, hsec⟩ := hconst
  let model :=
    Geometry.constPosQuotient
      (I := I) (M := M) hcompact hconn hbdry hdim g c hc hsec
  exact ⟨⟨model.1, model.2⟩⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem spaceForm_const_metric
    (hM : Closed3Manifold (I := I) (M := M))
    (model : IsSphericalSpaceFormQuotient I M) :
    AdmitsConstPosSec (I := I) (M := M) := by
  obtain ⟨S⟩ := model
  obtain ⟨_hcompact, _hconn, hbdry, _hdim⟩ := hM
  haveI : I.Boundaryless := hbdry
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  obtain ⟨c, hc, hsec⟩ := S.data.gQuot_constPosSec
  refine ⟨Diffeomorph.pullbackMetricCross S.data.gQuot S.equiv, c, hc, fun x X Y => ?_⟩
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04Std_pullbackCross
        S.data.gQuot S.equiv x X Y Y X, hsec,
    ← Diffeomorph.pullbackMetricCross_inner S.data.gQuot S.equiv x X X,
    ← Diffeomorph.pullbackMetricCross_inner S.data.gQuot S.equiv x Y Y,
    ← Diffeomorph.pullbackMetricCross_inner S.data.gQuot S.equiv x X Y]

omit [NeZero (Module.finrank ℝ E)] in
theorem spherical_space_form_implies_constant_positive_sectional_curvature
    (hM : Closed3Manifold (I := I) (M := M))
    (hsph : SphericalSpaceForm (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) :=
  spaceForm_const_metric (I := I) (M := M) hM hsph

omit [NeZero (Module.finrank ℝ E)] in
theorem constant_positive_sectional_curvature_iff_spherical_space_form
    (hM : Closed3Manifold (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) <-> SphericalSpaceForm (I := I) (M := M) := by
  constructor
  · exact constant_positive_sectional_curvature_implies_spherical_space_form (I := I) (M := M) hM
  · exact spherical_space_form_implies_constant_positive_sectional_curvature (I := I) (M := M) hM

end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
