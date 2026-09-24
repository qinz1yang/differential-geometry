import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric
import DifferentialGeometry.Geometry.Metric.DistancePullback
import Mathlib.Topology.MetricSpace.Isometry

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetricComplete_of_emetricSpace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (d : EMetricSpace M)
    (hdist : ∀ p q : M, @edist M d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace M d.toUniformSpace) : RiemannianMetricComplete g := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let r : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have heq : r = d.toPseudoEMetricSpace := by
    apply PseudoEMetricSpace.ext
    ext p q
    exact (hdist p q).symm
  change @CompleteSpace M r.toUniformSpace
  rw [heq]
  exact hcomplete

end DifferentialGeometry.Geometry

section

noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T3Space A]

theorem riemannianMetricComplete_pullback_of_emetricSpace
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (d : EMetricSpace Q)
    (hdist : ∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace Q d.toUniformSpace) :
    RiemannianMetricComplete (Diffeomorph.pullbackMetricCross g Φ.symm) := by
  let d' : EMetricSpace A := EMetricSpace.induced Φ.symm Φ.symm.injective d
  have hcomplete' : @CompleteSpace A d'.toUniformSpace := by
    let _ : EMetricSpace Q := d
    let _ : EMetricSpace A := d'
    let _ : CompleteSpace Q := hcomplete
    let e : A ≃ᵢ Q := { Φ.symm.toEquiv with isometry_toFun := fun _ _ => rfl }
    exact e.completeSpace
  apply riemannianMetricComplete_of_emetricSpace _ d' _ hcomplete'
  intro p q
  change @edist Q d.toEDist (Φ.symm p) (Φ.symm q) = _
  rw [hdist, Metric.edistOf_pullbackMetricCross]

end DifferentialGeometry.Geometry

end
