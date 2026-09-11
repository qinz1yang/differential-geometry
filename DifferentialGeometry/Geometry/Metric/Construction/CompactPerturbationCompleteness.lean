import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Euclidean

set_option autoImplicit false

noncomputable section

universe u uE uH

open scoped Manifold ContDiff Topology
open TopologicalSpace
open Bundle
open Manifold

namespace DifferentialGeometry

noncomputable def flatModelMetric
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace Real E]
    :
    SmoothRiemannianMetric 𝓘(Real, E) E :=
  euclideanMetric

namespace RiemannianMetricComplete

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem of_eq_off_compact
    {g h : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {K : Set M} (hK : IsCompact K)
    (heq : ∀ x : M, x ∉ K → h.inner x = g.inner x) :
    RiemannianMetricComplete (I := I) h := by
  obtain ⟨c, hc, hlower⟩ := metric_lower_on (I := I) hK h g
  refine of_lower hg (lt_min hc one_pos) ?_
  intro x v
  have hgnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (g.pos x v hv).le
  by_cases hx : x ∈ K
  · exact (mul_le_mul_of_nonneg_right (min_le_left c 1) hgnonneg).trans
      (hlower x hx v)
  · rw [heq x hx]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_right c 1) hgnonneg

theorem bumpExtend_complete
    (R : SmoothRiemannianMetric I M)
    (hR : RiemannianMetricComplete (I := I) R)
    (U : Opens M) [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → Real)
    (hχ : ContMDiff I 𝓘(Real, Real) ∞ χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : Real) 1)
    (hχsupport : tsupport χ ⊆ (U : Set M))
    (hχcomp : IsCompact (tsupport χ)) :
    RiemannianMetricComplete (I := I)
      (R.bumpExtendOpen (I := I) U gU χ hχ hχ01 hχsupport) := by
  apply of_eq_off_compact hR hχcomp
  intro x hx
  ext v w
  exact bumpExtendOpen_inner_of_notMem_tsupport
    (I := I) R U gU χ hχ hχ01 hχsupport x hx v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem flatModel_complete
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] :
    RiemannianMetricComplete (I := 𝓘(Real, E)) (flatModelMetric E) := by
  simpa only [flatModelMetric] using euclideanMetric_complete (E := E)

end RiemannianMetricComplete
end DifferentialGeometry

end
