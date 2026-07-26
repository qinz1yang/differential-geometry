import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false

/-!
# Completeness under a uniform lower metric bound

This file transfers completeness between two smooth Riemannian metrics on the
same pointed manifold.  A positive global lower bound makes every Cauchy
sequence for the larger metric Cauchy for the complete reference metric.
-/

noncomputable section

universe u uE uH

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry
namespace HCGCompactness
namespace MetricComplete

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A smooth metric which globally dominates a positive multiple of a complete
reference metric is complete. -/
theorem complete_of_lower
    {I : ModelWithCorners Real E H}
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hX : MetricComplete (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : IsManifold I 1 X.M :=
      IsManifold.of_le (I := I) (M := X.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    letI : TopologicalSpace.MetrizableSpace X.M :=
      Manifold.metrizableSpace I X.M
    letI : T3Space X.M := inferInstance
    ∀ (h : SmoothRiemannianMetric I X.M)
      (c : Real) (_ : 0 < c),
      (∀ x v, c * X.metric.inner x v v ≤ h.inner x v v) →
    let Y : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
      { X with metric := h }
    letI : RiemannianBundle (fun x : X.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    letI : (x : X.M) → InnerProductSpace Real (TangentSpace I x) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : X.M => TangentSpace I x) :=
      Y.riemBundle_cont (I := I)
    letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
    CompleteSpace X.M := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : TopologicalSpace.MetrizableSpace X.M :=
    Manifold.metrizableSpace I X.M
  letI : T3Space X.M := inferInstance
  intro h c hc hlower

  let Y : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { X with metric := h }
  letI : RiemannianBundle (fun x : X.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  letI : (x : X.M) → InnerProductSpace Real (TangentSpace I x) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : X.M => TangentSpace I x) :=
    Y.riemBundle_cont (I := I)
  letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M

  let a : ENNReal := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hdist : ∀ x y : X.M,
      a * riemannianEDistOf (I := I) X.metric x y ≤
        riemannianEDistOf (I := I) h x y := by
    intro x y
    rw [← edistOf_scale (I := I) c hc X.metric x y]
    exact edistOf_mono (I := I) _ _ (by
      intro z v
      simpa only [scaleMetric_inner] using hlower z v) x y

  refine EMetric.complete_of_cauchySeq_tendsto fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) h (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [Y] using hN m hm n hn

  change ∃ x, Filter.Tendsto s Filter.atTop (@nhds X.M X.topology x)
  letI : RiemannianBundle (fun x : X.M => TangentSpace I x) :=
    X.riemBundle (I := I)
  letI : (x : X.M) → InnerProductSpace Real (TangentSpace I x) :=
    X.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : X.M => TangentSpace I x) :=
    X.riemBundle_cont (I := I)
  letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
  letI : CompleteSpace X.M := by
    simpa [MetricComplete] using hX
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    have haε : 0 < a * ε := ENNReal.mul_pos ha0 (ne_of_gt hε)
    obtain ⟨N, hN⟩ := hsTarget (a * ε) haε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) X.metric (s m) (s n) < ε
    apply (ENNReal.mul_lt_mul_iff_right ha0 hatop).mp
    exact lt_of_le_of_lt (hdist (s m) (s n)) (hN m hm n hn))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  exact ⟨x, hx⟩

end MetricComplete
end HCGCompactness
end DifferentialGeometry

end
