import DifferentialGeometry.Geometry.Metric.OnDomain
import DifferentialGeometry.Geometry.Metric.HalfSpaceExtension
import DifferentialGeometry.Geometry.Metric.LocalJoinJets

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Metric.SmoothRiemannianMetricOn
variable {E H S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S] [T2Space S]
  {A : ℝ}

private structure LocalExtension
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (q : S × ℝ) where
  domain : TopologicalSpace.Opens (S × ℝ)
  mem : q ∈ domain
  metric : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) domain
  agrees : ∀ y : domain, (y : S × ℝ).2 ∈ Ioc (-A) 0 →
    ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, metric.inner y v w = h.inner (y : S × ℝ) v w

private def localExtension
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) : LocalExtension h q := by
  have hex : Nonempty (LocalExtension h q) := by
    obtain ⟨U, hqU, _, g, hg⟩ :=
      exists_local_metric_extension_of_halfClosed_cylinder_section
        h.inner h.contMDiffOn h.symm h.pos q hq
    exact ⟨⟨U, hqU, g, fun y hy => hg y ⟨mem_univ _, hy⟩⟩⟩
  exact Classical.choice hex

def halfClosedCovDeriv
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) :
    Tensor0SBundle.Tensor0SSpace (m + 2) (I.prod 𝓘(ℝ)) q :=
  let L := localExtension h q hq
  metricCovDeriv L.metric (gRef.restrictOpen L.domain) m ⟨q, L.mem⟩

theorem halfClosedCovDeriv_eq_local_apply
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (U : TopologicalSpace.Opens (S × ℝ)) (k : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U)
    (heq : ∀ y : U, (y : S × ℝ) ∈ univ ×ˢ Ioc (-A) 0 →
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, k.inner y v w = h.inner (y : S × ℝ) v w)
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) (hqU : q ∈ U)
    (slots : Fin (m + 2) → TangentSpace (I.prod 𝓘(ℝ)) q) :
    h.halfClosedCovDeriv gRef m q hq slots =
      metricCovDeriv k (gRef.restrictOpen U) m ⟨q, hqU⟩ slots := by
  let L := localExtension h q hq
  exact metricCovDeriv_local_extensions_eq_on_halfOpen_cylinder A h.inner gRef
    L.domain U L.metric k L.agrees (fun y hy => heq y ⟨mem_univ _, hy⟩)
    q L.mem hqU hq.2 m slots

theorem halfClosedCovDeriv_eq_local
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (U : TopologicalSpace.Opens (S × ℝ)) (k : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U)
    (heq : ∀ y : U, (y : S × ℝ) ∈ univ ×ˢ Ioc (-A) 0 →
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, k.inner y v w = h.inner (y : S × ℝ) v w)
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) (hqU : q ∈ U) :
    h.halfClosedCovDeriv gRef m q hq =
      metricCovDeriv k (gRef.restrictOpen U) m ⟨q, hqU⟩ := by
  ext slots
  exact h.halfClosedCovDeriv_eq_local_apply gRef U k heq m q hq hqU slots

theorem halfClosedCovDeriv_eq_restrictOpen
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (U : TopologicalSpace.Opens (S × ℝ))
    (hU : (U : Set (S × ℝ)) ⊆ univ ×ˢ Ioc (-A) 0) (m : ℕ) (x : U) :
    h.halfClosedCovDeriv gRef m (x : S × ℝ) (hU x.2) =
      metricCovDeriv (h.restrictOpen U hU) (gRef.restrictOpen U) m x := by
  exact h.halfClosedCovDeriv_eq_local gRef U (h.restrictOpen U hU)
    (fun _ _ _ _ => rfl) m (x : S × ℝ) (hU x.2) x.2

theorem halfClosedCovDeriv_congr
    (h₁ h₂ : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (heq : ∀ y ∈ (univ ×ˢ Ioc (-A) 0 : Set (S × ℝ)),
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, h₁.inner y v w = h₂.inner y v w)
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (m : ℕ) (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) :
    h₁.halfClosedCovDeriv gRef m q hq = h₂.halfClosedCovDeriv gRef m q hq := by
  let L := localExtension h₂ q hq
  exact h₁.halfClosedCovDeriv_eq_local gRef L.domain L.metric
    (fun y hy v w => (L.agrees y hy.2 v w).trans (heq (y : S × ℝ) hy v w).symm)
    m q hq L.mem

theorem halfClosedCovDeriv_zero_apply
    (h : SmoothRiemannianMetricOn (I := I.prod 𝓘(ℝ)) ((univ : Set S) ×ˢ Ioc (-A) 0))
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (S × ℝ))
    (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0)
    (slots : Fin 2 → TangentSpace (I.prod 𝓘(ℝ)) q) :
    h.halfClosedCovDeriv gRef 0 q hq slots = h.inner q (slots 0) (slots 1) := by
  let L := localExtension h q hq
  change Tensor0SBundle.metricTensorField L.metric ⟨q, L.mem⟩ slots = _
  exact (Tensor0SBundle.metricTensorField_apply L.metric ⟨q, L.mem⟩ slots).trans
    (L.agrees ⟨q, L.mem⟩ hq.2 (slots 0) (slots 1))

end DifferentialGeometry.Geometry.Metric.SmoothRiemannianMetricOn
