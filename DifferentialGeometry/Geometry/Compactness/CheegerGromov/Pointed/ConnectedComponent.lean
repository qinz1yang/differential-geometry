import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Restriction
import DifferentialGeometry.Topology.Manifold.ConnectedComponent

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace PointedRiemannianManifold

variable (X : PointedRiemannianManifold I)

local instance : TopologicalSpace X.M := X.topology
local instance : ChartedSpace H X.M := X.charted

def connectedComponent : PointedRiemannianManifold I :=
  X.restrictOpen (connectedComponentOpen (I := I) X.basepoint) mem_connectedComponent

theorem connectedComponent_connected :
    letI : TopologicalSpace X.connectedComponent.M := X.connectedComponent.topology
    ConnectedSpace X.connectedComponent.M := by
  change ConnectedSpace (connectedComponentOpen (I := I) X.basepoint)
  exact connectedComponentOpen_connectedSpace X.basepoint

end PointedRiemannianManifold

theorem MetricComplete.connectedComponent
    {X : PointedRiemannianManifold I} (hX : MetricComplete X) :
    MetricComplete X.connectedComponent := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  exact metricComplete_restrictOpen X _ mem_connectedComponent isClosed_connectedComponent hX

theorem HasCurvDerivBound.connectedComponent
    {X : PointedRiemannianManifold I} {k : ℕ} {C : ℝ}
    (hX : HasCurvDerivBound X k C) : HasCurvDerivBound X.connectedComponent k C := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  exact hasCurvDerivBound_restrictOpen X _ mem_connectedComponent k C hX

namespace PointedRiemannianSeq

variable (S : PointedRiemannianSeq I)

local instance (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology
local instance (i : ℕ) : ChartedSpace H (S.obj i).M := (S.obj i).charted

def connectedComponent : PointedRiemannianSeq I :=
  S.restrictOpen (fun i => connectedComponentOpen (I := I) (S.obj i).basepoint)
    (fun _ => mem_connectedComponent)

end PointedRiemannianSeq

theorem SeqMetricComplete.connectedComponent
    {S : PointedRiemannianSeq I} (hS : SeqMetricComplete S) :
    SeqMetricComplete S.connectedComponent where
  complete i := (hS.complete i).connectedComponent

def SeqBoundedGeometry.connectedComponent
    {S : PointedRiemannianSeq I} (hS : SeqBoundedGeometry S) :
    SeqBoundedGeometry S.connectedComponent where
  C := hS.C
  nonneg := hS.nonneg
  bound i k := (hS.bound i k).connectedComponent

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def BaseInjBound.connectedComponent
    {S : PointedRiemannianSeq I} (hρ : BaseInjBound S) (hS : SeqMetricComplete S) :
    BaseInjBound S.connectedComponent where
  ρ := hρ.ρ
  pos := hρ.pos
  bound i := by
    let : TopologicalSpace (S.obj i).M := (S.obj i).topology
    let : ChartedSpace H (S.obj i).M := (S.obj i).charted
    exact (hasInjRadiusAt_restrictOpen_iff (S.obj i) _ mem_connectedComponent
      isClosed_connectedComponent (hS.complete i) _ hρ.ρ).mpr (hρ.bound i)

end InnerProduct

end DifferentialGeometry.CheegerGromovCompactness
