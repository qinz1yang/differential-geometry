import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Topology.Connected.FiniteEDistance
import Mathlib.Topology.UniformSpace.UniformEmbedding
import DifferentialGeometry.Topology.Compactness.Connected
import Mathlib.Topology.EMetricSpace.Paracompact

section

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.restrict_connectedComponent
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g) (p : M) :
    RiemannianMetricComplete (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) p)) := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) p
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : IsManifold 𝓘(ℝ, E) 1 M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := M) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  let : CompleteSpace M := hg
  let : IsManifold 𝓘(ℝ, E) 1 C :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let eC : PseudoEMetricSpace C := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  let : PseudoEMetricSpace C := eC
  let : UniformSpace C := eC.toUniformSpace
  have hiso : Isometry (Subtype.val : C → M) := by
    intro x y
    change riemannianEDistOf g (x : M) (y : M) = riemannianEDistOf gC x y
    exact (Metric.edistOf_restrictOpen_connCompOpen g p x y).symm
  have hc : IsClosed (Set.range (Subtype.val : C → M)) := by
    rw [Subtype.range_coe]
    exact isClosed_connectedComponent
  exact hiso.isUniformInducing.completeSpace hc.isComplete

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.to_canonical [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g) :
    DifferentialGeometry.RiemannianMetricComplete g := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨?_⟩
  exact hg

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem sigmaCompactSpace_connectedComponent_of_riemannianMetric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) :
    SigmaCompactSpace (connectedComponentOpen (I := 𝓘(ℝ, E)) p) := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) p
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := 𝓘(ℝ, E)) p
  let : LocallyCompactSpace C := ChartedSpace.locallyCompactSpace E C
  let : IsManifold 𝓘(ℝ, E) 1 C :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := C) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace C := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) C
  exact DifferentialGeometry.Topology.sigmaCompactSpace_of_preconnected C

end DifferentialGeometry.Geometry

end

end
