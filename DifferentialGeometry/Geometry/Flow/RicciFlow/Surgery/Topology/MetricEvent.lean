import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.Defs

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology (ClosedOrientedManifold SphericalCutCapTransition)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

def metricSmoothUpTo (M : ClosedOrientedManifold.{u} 3)
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) M.Carrier) (J : Set ℝ) : Prop :=
  ∀ p : M.Carrier, ∀ t ∈ J,
    ∃ U : Set M.Carrier, IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × M.Carrier → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j : Fin 3, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
          𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ J, ∀ x ∈ U, ∀ i j : Fin 3,
          A (s, x) i j = (g s).inner x
            ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).symmL ℝ x
              (EuclideanSpace.single i (1 : ℝ)))
            ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) p).symmL ℝ x
              (EuclideanSpace.single j (1 : ℝ)))

structure IncomingSlab (M : ClosedOrientedManifold.{u} 3) (a s : ℝ) where
  lt : a < s
  flow : SolutionOn (I := 𝓡 3) (M := M.Carrier) (RealTimeInterval.closedOpen a s lt)
  equation : IsSolutionOn flow
  smoothUpTo : metricSmoothUpTo M flow.base.metric (Ico a s)

namespace IncomingSlab

variable {M : ClosedOrientedManifold.{u} 3} {a s : ℝ} (G : IncomingSlab M a s)

def riemannNorm (t : ℝ) (x : M.Carrier) : ℝ :=
  Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))

def terminalRegularRegion : Set M.Carrier :=
  {x | ∃ U : Set M.Carrier, IsOpen U ∧ x ∈ U ∧
    ∃ a' ∈ Ico a s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ U, ∀ t ∈ Ico a' s, G.riemannNorm t y ≤ K}

theorem isOpen_terminalRegularRegion : IsOpen G.terminalRegularRegion := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hxU, a', ha', K, hK, hbound⟩
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  exact ⟨U, hU, hy, a', ha', K, hK, hbound⟩

def terminalRegularOpen : TopologicalSpace.Opens M.Carrier :=
  ⟨G.terminalRegularRegion, G.isOpen_terminalRegularRegion⟩

def terminalMetricConverges
    (gbar : SmoothRiemannianMetric (𝓡 3) G.terminalRegularOpen) : Prop :=
  letI : SecondCountableTopology M.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) M.Carrier
  letI : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.terminalRegularOpen
  ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ x ∈ K,
      DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) gbar gbar x < ε

structure TerminalLimitMetric where
  metric : SmoothRiemannianMetric (𝓡 3) G.terminalRegularOpen
  converges : G.terminalMetricConverges metric

end IncomingSlab

structure MetricCutCapEvent (M Q : ClosedOrientedManifold.{u} 3) (a s : ℝ) where
  transition : SphericalCutCapTransition M Q
  incoming : IncomingSlab M a s
  terminal : incoming.TerminalLimitMetric
  outputMetric : SmoothRiemannianMetric (𝓡 3) Q.Carrier
  unchanged : Set transition.tubes.core
  unchanged_compact : IsCompact unchanged
  unchanged_retained : unchanged ⊆ transition.retainedCore
  [unchangedCharts : ChartedSpace (EuclideanHalfSpace 3) unchanged]
  [unchangedSmooth : IsManifold (𝓡∂ 3) ∞ unchanged]
  unchanged_induced : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
    (fun x : unchanged => (x.1.1 : M.Carrier))
  terminalInclusion : C(unchanged, incoming.terminalRegularOpen)
  terminalInclusion_eq : ∀ x : unchanged, (terminalInclusion x).1 = x.1.1
  terminalInclusion_smooth : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ terminalInclusion
  outputInclusion : C(unchanged, Q.Carrier)
  outputInclusion_eq : ∀ x : unchanged,
    transition.presentation (transition.capping.coreInclusion x.1) = Sum.inl (outputInclusion x)
  outputInclusion_smooth : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ outputInclusion
  unchanged_metric_eq : ∀ x : unchanged, ∀ v w : TangentSpace (𝓡∂ 3) x,
    terminal.metric.inner (terminalInclusion x)
        (mfderiv (𝓡∂ 3) (𝓡 3) terminalInclusion x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) terminalInclusion x w) =
      outputMetric.inner (outputInclusion x)
        (mfderiv (𝓡∂ 3) (𝓡 3) outputInclusion x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) outputInclusion x w)
  unchanged_contains_outside : ∀ x : transition.tubes.core,
    x ∈ transition.retainedCore → x.1 ∉ transition.tubes.surgeryRegion → x ∈ unchanged
  every_component_meets_unchanged : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : unchanged, ConnectedComponents.mk (outputInclusion x) = c

attribute [instance] MetricCutCapEvent.unchangedCharts MetricCutCapEvent.unchangedSmooth

namespace MetricCutCapEvent

theorem unchanged_isEmpty_of_isEmpty {M Q : ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s) (h : IsEmpty Q.Carrier) : IsEmpty E.unchanged :=
  ⟨fun x => h.false (E.outputInclusion x)⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery
