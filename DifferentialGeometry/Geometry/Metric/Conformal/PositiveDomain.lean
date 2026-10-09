import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.Completeness.PositiveDomain
import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomainCharts

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Metric

open Bundle Filter Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Bundle Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem contMDiff_neg_log_on_positive_domain {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => -Real.log (δ (x : M))) := by
  have hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => δ (x : M)) :=
    hδ.comp contMDiff_subtype_val
  have hlog : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => Real.log (δ (x : M))) := by
    intro x
    exact (Real.contDiffAt_log.mpr ((hU x).1 x.property).ne').contMDiffAt.comp x
      hd.contMDiffAt
  exact hlog.neg

/-- The actual conformal metric on the positive domain of the original
smooth defining function. No metric or metric-existence premise is used. -/
def canonicalPositiveDomainMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {δ : M → ℝ} (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x) :
    SmoothRiemannianMetric 𝓘(ℝ, E) U :=
  DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff (g.restrictOpen U)
    (fun x : U => -Real.log (δ (x : M)))
    (contMDiff_neg_log_on_positive_domain hδ U hU)

/-- Its inner product is exactly the prescribed `δ⁻²` multiple of the
restriction of the same original metric. -/
theorem canonicalPositiveDomainMetric_inner
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (x : U) (v w : TangentSpace 𝓘(ℝ, E) x) :
    (canonicalPositiveDomainMetric g hδ U hU).inner x v w =
      (δ (x : M))⁻¹ ^ 2 * (g.restrictOpen U).inner x v w := by
  change Real.exp (2 * -Real.log (δ (x : M))) * (g.restrictOpen U).inner x v w = _
  simp only [two_mul, Real.exp_add, Real.exp_neg,
    Real.exp_log ((hU x).1 x.property), pow_two]

/-- On an open region where the defining function equals one, the constructed
metric and the restricted original metric have equal inner-product germs.
The set where `δ = 1` is not assumed to be open. -/
theorem canonicalPositiveDomainMetric_inner_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (O : TopologicalSpace.Opens M) (hO : ∀ x ∈ O, δ x = 1)
    (x : U) (hx : (x : M) ∈ O) :
    ∀ᶠ y : U in 𝓝 x,
      (canonicalPositiveDomainMetric g hδ U hU).inner y = (g.restrictOpen U).inner y := by
  filter_upwards [(O.isOpen.preimage continuous_subtype_val).mem_nhds hx] with y hy
  ext v w
  rw [canonicalPositiveDomainMetric_inner, hO y hy]
  norm_num

variable [SecondCountableTopology M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The explicitly constructed metric is simultaneously complete and
homogeneously regular. Both conclusions concern the same `δ`, domain, and
original metric; the positive domain may be empty or disconnected. -/
theorem canonicalPositiveDomainMetric_complete_homogeneous
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M))) (hdim : Module.finrank ℝ E = 3) :
    let : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
    DifferentialGeometry.Geometry.RiemannianMetricComplete
        (canonicalPositiveDomainMetric g hδ U hU) ∧
      HomogeneouslyRegularMetric (canonicalPositiveDomainMetric g hδ U hU) := by
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let G := canonicalPositiveDomainMetric g hδ U hU
  have hG := canonicalPositiveDomainMetric_inner g hδ U hU
  exact ⟨DifferentialGeometry.Geometry.riemannianMetricComplete_positive_domain
      g hδ U hU hK G hG,
    DifferentialGeometry.Geometry.Metric.PositiveDomainCharts.homogeneouslyRegularMetric_positive_domain
      g hδ U hU hK G hG hdim⟩

end DifferentialGeometry.Geometry.Metric
