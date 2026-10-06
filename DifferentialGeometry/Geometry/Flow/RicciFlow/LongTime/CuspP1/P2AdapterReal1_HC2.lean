import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric
import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomain

/-!
# S-MIRRORS G1 (`_HC2`): real `canonicalPositiveDomainMetric_complete_homogeneous`

Replaces the placeholder mirror `canonicalPositiveDomainMetric_complete_homogeneous_P2A` of
`P2AdapterImportedLemmas.lean` by the IMS03 theorem
`DifferentialGeometry.Geometry.Metric.canonicalPositiveDomainMetric_complete_homogeneous`
(`Geometry/Metric/Conformal/PositiveDomain.lean`, copied verbatim from branch
`gc/juihuichung/ims03-astra-20261005`, tip `f49e541fb`, together with its three IMS03-only
import dependencies).  The statement is literally that of the mirror (with the metric
`canonicalPositiveDomainMetric_P2A` of `P2AdapterImportedDefs`); it is closed by the real theorem
because `canonicalPositiveDomainMetric_P2A` is a verbatim copy of the real
`canonicalPositiveDomainMetric` (definitional unfolding).
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

section PositiveDomain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]

omit [SecondCountableTopology M] in
/-- The mirror `canonicalPositiveDomainMetric_P2A` is the real
`canonicalPositiveDomainMetric` (verbatim copy, equal by unfolding). -/
theorem canonicalPositiveDomainMetric_P2A_eq_HC2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x) :
    canonicalPositiveDomainMetric_P2A g hδ U hU =
      DifferentialGeometry.Geometry.Metric.canonicalPositiveDomainMetric g hδ U hU :=
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Statement of the mirror `canonicalPositiveDomainMetric_complete_homogeneous_P2A`, proved by the
real IMS03 theorem `canonicalPositiveDomainMetric_complete_homogeneous`. -/
theorem canonicalPositiveDomainMetric_complete_homogeneous_P2A_HC2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M))) (hdim : Module.finrank ℝ E = 3) :
    let : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
    DifferentialGeometry.Geometry.RiemannianMetricComplete
        (canonicalPositiveDomainMetric_P2A g hδ U hU) ∧
      HomogeneouslyRegularMetric (canonicalPositiveDomainMetric_P2A g hδ U hU) :=
  DifferentialGeometry.Geometry.Metric.canonicalPositiveDomainMetric_complete_homogeneous
    g hδ U hU hK hdim

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Consumer of G1: the completeness half of the conclusion. -/
theorem canonicalPositiveDomainMetric_complete_P2A_HC2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M))) (hdim : Module.finrank ℝ E = 3) :
    let : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
    DifferentialGeometry.Geometry.RiemannianMetricComplete
      (canonicalPositiveDomainMetric_P2A g hδ U hU) :=
  (canonicalPositiveDomainMetric_complete_homogeneous_P2A_HC2 g hδ U hU hK hdim).1

end PositiveDomain

end GC.LongTime.CuspP1
