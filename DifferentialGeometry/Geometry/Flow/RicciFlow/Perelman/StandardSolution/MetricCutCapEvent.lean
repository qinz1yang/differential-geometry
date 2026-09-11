import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalRegion
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FullRetainedUnchangedLocus
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OrientedFiniteCutCapGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
variable (a s : ℝ) (has : a < s)
  (incoming : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a s has))
variable (gTerminal : SmoothRiemannianMetric I (terminalRegularRegion incoming.base.metric a s))
  {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
  (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
  (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
  (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f)))
  (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) (terminalRegularRegion incoming.base.metric a s))
  (o : SmoothOrientation I M)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "Ret" => finiteCapRetained hL hδ f hf hdisj R

def MetricCutCapEventOn :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) Ret → Prop :=
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    fun gRet =>
      IsSolutionOn incoming ∧ IsTerminalLimitMetric incoming.base.metric a s gTerminal ∧
      OrientedFiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R o ∧
      FullRetainedUnchangedLocusGeometry I hdim hL hδ f hf hdisj hs hδ1 R (terminalRegularRegion incoming.base.metric a s) hRet ∧
      (let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
       let Ψ := retainedCoreDomainMap f R (terminalRegularRegion incoming.base.metric a s) hRet
       ∀ (p : retainedCore f R) (v w : TangentSpace IR p),
         gTerminal.inner (Ψ p) (mfderiv IR I Ψ p v) (mfderiv IR I Ψ p w) =
           gRet.inner (Φ p) (mfderiv IR (𝓡 3) Φ p v) (mfderiv IR (𝓡 3) Φ p w)) ∧
      (IsEmpty Ret → ∀ gOther : SmoothRiemannianMetric (𝓡 3) Ret, gOther = gRet)

theorem metricCutCapEventOn_of_retained_identity
    (hIncoming : IsSolutionOn incoming)
    (hTerminal : IsTerminalLimitMetric incoming.base.metric a s gTerminal)
    (hGeometry : OrientedFiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R o) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    ∀ gRet : SmoothRiemannianMetric (𝓡 3) Ret,
      (let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
       let Ψ := retainedCoreDomainMap f R (terminalRegularRegion incoming.base.metric a s) hRet
       ∀ (p : retainedCore f R) (v w : TangentSpace IR p),
         gTerminal.inner (Ψ p) (mfderiv IR I Ψ p v) (mfderiv IR I Ψ p w) =
           gRet.inner (Φ p) (mfderiv IR (𝓡 3) Φ p v) (mfderiv IR (𝓡 3) Φ p w)) →
      MetricCutCapEventOn I a s has incoming gTerminal hdim hL hδ f hf hdisj hs hδ1 R hRet o gRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  dsimp only
  intro gRet hTensor
  refine ⟨hIncoming, hTerminal, hGeometry,
    fullRetainedUnchangedLocusGeometry I hdim hL hδ f hf hdisj hs hδ1 R (terminalRegularRegion incoming.base.metric a s) hRet, hTensor, ?_⟩
  intro hEmpty gOther
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  exact (hEmpty.false p).elim
end DifferentialGeometry.PDE.RicciFlow
