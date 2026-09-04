import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import DifferentialGeometry.Geometry.Metric.Completeness

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
    SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

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
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (hχcomp : IsCompact (tsupport χ)) :
    RiemannianMetricComplete (I := I)
      (R.bumpExtendOpen (I := I) U gU χ hχ hχ01 hχsupp) := by
  apply of_eq_off_compact hR hχcomp
  intro x hx
  ext v w
  exact bumpExtendOpen_inner_of_notMem_tsupport
    (I := I) R U gU χ hχ hχ01 hχsupp x hx v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem flatModel_complete
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E] :
    RiemannianMetricComplete (I := 𝓘(Real, E)) (flatModelMetric E) := by
  let sourceEMetric : EMetricSpace E := inferInstance
  let sourceComplete :
      @CompleteSpace E sourceEMetric.toPseudoEMetricSpace.toUniformSpace :=
    inferInstance
  let sourceEdist : E → E → ENNReal := fun x y => edist x y
  have hsource : ∀ x y : E,
      sourceEdist x y = riemannianEDist 𝓘(Real, E) x y := by
    intro x y
    exact IsRiemannianManifold.out (I := 𝓘(Real, E)) x y
  refine ⟨?_⟩
  let : RiemannianBundle
      (fun x : E => TangentSpace 𝓘(Real, E) x) :=
    ⟨(flatModelMetric E).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : E => TangentSpace 𝓘(Real, E) x) :=
    ⟨(flatModelMetric E).inner,
      (flatModelMetric E).contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  have hed : ∀ x y : E, edist x y = sourceEdist x y := by
    intro x y
    rw [IsRiemannianManifold.out (I := 𝓘(Real, E)) x y]
    exact (hsource x y).symm
  refine EMetric.complete_of_cauchySeq_tendsto (α := E) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n → edist (s m) (s n) < ε :=
    EMetric.cauchySeq_iff.mp hs
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  let : EMetricSpace E := sourceEMetric
  let : CompleteSpace E := sourceComplete
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := hsTarget ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change sourceEdist (s m) (s n) < ε
    rw [← hed]
    exact hN m hm n hn)
  exact cauchySeq_tendsto_of_complete hsSource

end RiemannianMetricComplete
end DifferentialGeometry

end
