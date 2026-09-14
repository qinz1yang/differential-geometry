import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

namespace MetricInnerPullbackTendsto

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h : MetricInnerPullbackTendsto (I := I) Φ gInf)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricInnerPullbackTendsto (I := I) (Φ.compSubseq φ hφ) gInf := by
  intro t ht x v w
  refine Filter.Tendsto.congr' ?_ ((h t ht x v w).comp hφ.tendsto_atTop)
  filter_upwards with k
  rfl

theorem limit_unique
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {g₁ g₂ : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h₁ : MetricInnerPullbackTendsto (I := I) Φ g₁)
    (h₂ : MetricInnerPullbackTendsto (I := I) Φ g₂) :
    ∀ t : Real, t ∈ X.D.carrier -> g₁ t = g₂ t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  intro t ht
  refine SmoothRiemannianMetric.ext_inner (fun x v w => ?_)
  exact tendsto_nhds_unique (h₁ t ht x v w) (h₂ t ht x v w)

end MetricInnerPullbackTendsto

namespace MetricPullbackTendsto

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : MetricPullbackTendsto (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricPullbackTendsto (I := I) (Φ.compSubseq φ hφ) :=
  MetricInnerPullbackTendsto.compSubseq (I := I) h φ hφ

end MetricPullbackTendsto

namespace MetricRicciPullbackTendsto

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h : MetricRicciPullbackTendsto (I := I) Φ gInf)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricRicciPullbackTendsto (I := I) (Φ.compSubseq φ hφ) gInf := by
  intro t ht x v w
  refine Filter.Tendsto.congr' ?_ ((h t ht x v w).comp hφ.tendsto_atTop)
  filter_upwards with k
  rfl

theorem limit_unique
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {g₁ g₂ : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (h₁ : MetricRicciPullbackTendsto (I := I) Φ g₁)
    (h₂ : MetricRicciPullbackTendsto (I := I) Φ g₂) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ t : Real, t ∈ X.D.carrier -> ∀ (x : P.M) (v w : TangentSpace I x),
      Geometry.Curvature.metricRicciAt (I := I) (g₁ t) x
        (Geometry.Curvature.vec2 v w) =
      Geometry.Curvature.metricRicciAt (I := I) (g₂ t) x
        (Geometry.Curvature.vec2 v w) := by
  intro t ht x v w
  exact tendsto_nhds_unique (h₁ t ht x v w) (h₂ t ht x v w)

end MetricRicciPullbackTendsto

namespace RicciPullbackTendsto

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : RicciPullbackTendsto (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    RicciPullbackTendsto (I := I) (Φ.compSubseq φ hφ) :=
  MetricRicciPullbackTendsto.compSubseq (I := I) h φ hφ

end RicciPullbackTendsto

namespace FunctionPullbackTendsto

theorem limit_unique
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {uSeq : ∀ k : Nat, Real -> (X.term (subseq k)).M -> Real}
    {u₁ u₂ : Real -> P.M -> Real}
    (h₁ : FunctionPullbackTendsto (I := I) Φ uSeq u₁)
    (h₂ : FunctionPullbackTendsto (I := I) Φ uSeq u₂) :
    ∀ t : Real, t ∈ X.D.carrier -> ∀ x : P.M, u₁ t x = u₂ t x := by
  intro t ht x
  exact tendsto_nhds_unique (h₁ t ht x) (h₂ t ht x)

end FunctionPullbackTendsto

namespace ScalarPullbackTendsto

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : ScalarPullbackTendsto (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    ScalarPullbackTendsto (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x
  refine Filter.Tendsto.congr' ?_ ((h t ht x).comp hφ.tendsto_atTop)
  filter_upwards with k
  rfl

end ScalarPullbackTendsto

namespace RicNormPullback

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : RicNormPullback (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    RicNormPullback (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x
  refine Filter.Tendsto.congr' ?_ ((h t ht x).comp hφ.tendsto_atTop)
  filter_upwards with k
  rfl

end RicNormPullback

namespace SourceDomainMetricData

noncomputable def compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : SourceDomainMetricData (I := I) Φ (φ k)) :
    SourceDomainMetricData (I := I) (Φ.compSubseq φ hφ) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  limitMetricFamily := D.limitMetricFamily
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

theorem compSubseq_derivNormSupOn
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : SourceDomainMetricData (I := I) Φ (φ k)) (K : Set P.M) (p : Nat) (t : Real) :
    (compSubseq (I := I) φ hφ k D).derivNormSupOn (I := I) K p t =
      D.derivNormSupOn (I := I) K p t := rfl

end SourceDomainMetricData

namespace SourceMetricConvergenceData

noncomputable def compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (Cd : SourceMetricConvergenceData (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    SourceMetricConvergenceData (I := I) (Φ.compSubseq φ hφ) where
  domain k := SourceDomainMetricData.compSubseq (I := I) φ hφ k (Cd.domain (φ k))
  converges := by
    intro K hK p t ht ε hε
    obtain ⟨k0, hk0⟩ := Cd.converges K hK p t ht ε hε
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨hsrc, hconv⟩ := hk0 (φ k) (le_trans hk (hφ.id_le k))
    exact ⟨hsrc, hconv⟩

end SourceMetricConvergenceData

namespace SourceSpacetimeConvergenceData

theorem compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : ∀ k : Nat, SourceDomainMetricData (I := I) Φ k}
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    SourceSpacetimeConvergenceData (I := I) (Φ.compSubseq φ hφ)
      (fun k => SourceDomainMetricData.compSubseq (I := I) φ hφ k (D (φ k))) where
  converges_on_windows := by
    intro K hK p a b hwin ε hε
    obtain ⟨k0, hk0⟩ := Hst.converges_on_windows K hK p a b hwin ε hε
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨hsrc, hconv⟩ := hk0 (φ k) (le_trans hk (hφ.id_le k))
    exact ⟨hsrc, hconv⟩

end SourceSpacetimeConvergenceData

namespace PointedCGConverges

noncomputable def compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (C : PointedCGConverges (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedCGConverges (I := I) X L (subseq ∘ φ) where
  maps := C.maps.compSubseq φ hφ
  metrics := C.metrics.compSubseq φ hφ

end PointedCGConverges

namespace SmoothCGHConverges

noncomputable def compSubseq
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (h : SmoothCGHConverges (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    SmoothCGHConverges (I := I) X L (subseq ∘ φ) where
  spatial := h.spatial.compSubseq φ hφ
  metric_converges := h.metric_converges.compSubseq φ hφ
  scalar_converges := h.scalar_converges.compSubseq φ hφ
  ricci_converges := h.ricci_converges.compSubseq φ hφ
  ricciNorm_converges := h.ricciNorm_converges.compSubseq φ hφ
  spacetime := h.spacetime.compSubseq φ hφ

end SmoothCGHConverges

end CheegerGromovCompactness
end DifferentialGeometry
