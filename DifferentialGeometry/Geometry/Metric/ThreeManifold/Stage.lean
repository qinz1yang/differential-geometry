import DifferentialGeometry.Topology.ThreeManifold.OrientedStage
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u

abbrev Metric (P : OrientedThreeStage.{u}) := SmoothRiemannianMetric ThreeModel P.Carrier

def chartVector (P : OrientedThreeStage.{u}) (p x : P.Carrier) (i : Fin 3) :
    TangentSpace ThreeModel x :=
  (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ x
    (EuclideanSpace.single i (1 : ℝ))

def MetricSmoothUpTo (P : OrientedThreeStage.{u}) (g : ℝ → P.Metric) (J : Set ℝ) : Prop :=
  ∀ p : P.Carrier, ∀ t ∈ J,
    ∃ U : Set P.Carrier, IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × P.Carrier → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j : Fin 3, ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
          𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ J, ∀ x ∈ U, ∀ i j : Fin 3,
          A (s, x) i j = (g s).inner x (P.chartVector p x i) (P.chartVector p x j)

variable (P : OrientedThreeStage.{u})

def componentMetric (g : P.Metric) (c : ConnectedComponents P.Carrier) : (P.component c).toClosedOrientedManifold.Metric :=
  g.restrictOpen (P.componentOpen c)

end DifferentialGeometry.Topology.ClosedOrientedManifold
