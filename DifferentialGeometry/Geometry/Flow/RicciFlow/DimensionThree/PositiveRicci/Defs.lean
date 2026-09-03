import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CompactnessConclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedGlobal
import DifferentialGeometry.Geometry.Curvature.MetricConditions
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

def hamiltonReferenceRadius : Real := (1 : Real) / 10

theorem hamilton_reference_radius_pos : 0 < hamiltonReferenceRadius := by
  norm_num [hamiltonReferenceRadius]

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

def hamiltonLimitConnected (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  ConnectedSpace L.N

def hamiltonLimitBoundaryless : Prop := I.Boundaryless

def hamiltonLimitBaseScalarConvergence
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

def limitBaseScalarOne (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  L.S.scalar 0 L.basepoint = 1

def limitTracefreeRicciZeroAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x = 0

def limitTracefreeRicciDecayAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall η : Real, 0 < η ->
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x <= η

def limitEinsteinAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall v w : TangentSpace I x,
    L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
      (L.S.scalar t x / 3) * (L.S.base.metric t).inner x v w

def limitRoundAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
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
    constantPositiveSectionalCurvatureMetric (I := I) (M := L.N) g


end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
