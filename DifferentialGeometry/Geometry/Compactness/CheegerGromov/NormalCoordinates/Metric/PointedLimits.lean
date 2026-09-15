import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.BufferedChartCover
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.FiniteLimits
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.FiniteLimits

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_finite_pointed_covering_intrinsicBallChart_metric_limit_subsequence
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    letI : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle (I := I)
    letI : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
      fun k => (X.obj k).riemInner (I := I)
    letI : ∀ k, IsContinuousRiemannianBundle E
        (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle_cont (I := I)
    letI : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
    letI : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
    letI : ∀ k, CompleteSpace (X.obj k).M :=
      fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    let hEnorm : ∀ k (x : (X.obj k).M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner x v v)) := by
      intro k x v
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric x v
    ∃ (ρ : ℝ), 0 < ρ ∧ ρ ≤ R - r ∧ ∃ N : ℕ,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∃ (c : Fin (N + 1) → ∀ k, (X.obj (phi k)).M)
          (charts : ∀ i k, IntrinsicBallChart (I := I) (X.obj (phi k)).metric
            (hEnorm (phi k)) (c i k) ρ)
          (gInf : Fin (N + 1) → E → E →L[ℝ] E →L[ℝ] ℝ),
          (∀ k, c 0 k = (X.obj (phi k)).basepoint) ∧
          (∀ i k, riemannianEDistOf (I := I) (X.obj (phi k)).metric
            (X.obj (phi k)).basepoint (c i k) ≤ ENNReal.ofReal r) ∧
          (∀ k, ∀ y : (X.obj (phi k)).M,
            riemannianEDistOf (I := I) (X.obj (phi k)).metric
              (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r →
            ∃ i, y ∈ (charts i k).hom '' Metric.ball (0 : E) (ρ / 10)) ∧
          (∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I)
                (X.obj (phi k)).metric (hEnorm (phi k)) (c i k) z v v ∧
              intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k) z v v ≤ 2 * ‖v‖ ^ 2) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (gInf i) (Metric.ball 0 ρ) ∧
            MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
              (fun k => intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k)) (gInf i) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v w, gInf i z v w = gInf i z w v) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v,
              (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf i z v v ∧
                gInf i z v v ≤ 2 * ‖v‖ ^ 2)) := by
  classical
  let : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle (I := I)
  let : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun k => (X.obj k).riemInner (I := I)
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle_cont (I := I)
  let : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
  let : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
  let : ∀ k, CompleteSpace (X.obj k).M :=
    fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  intro hEnorm
  obtain ⟨K, hK, hKbound⟩ := hjets 0
  obtain ⟨ρ, hρ, hρR, hcovering⟩ :=
    exists_eventually_finite_pointed_intrinsicBallChart_cover_of_curvature_injectivity
      X hcomplete hr hrR hK hη hKbound hinj
  obtain ⟨N, hcover⟩ := hcovering (ρ / 10) (by positivity) (by linarith)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hcover
  let τ : ℕ → ℕ := fun k => n₀ + k
  have hτ : StrictMono τ := fun _ _ h => Nat.add_lt_add_left h n₀
  have hdata : ∀ k, ∃ (c : Fin (N + 1) → (X.obj (τ k)).M)
      (charts : ∀ i, IntrinsicBallChart (I := I) (X.obj (τ k)).metric
        (hEnorm (τ k)) (c i) ρ),
      c 0 = (X.obj (τ k)).basepoint ∧
      (∀ i, riemannianEDistOf (I := I) (X.obj (τ k)).metric
        (X.obj (τ k)).basepoint (c i) ≤ ENNReal.ofReal r) ∧
      (∀ i, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
        (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I)
            (X.obj (τ k)).metric (hEnorm (τ k)) (c i) z v v ∧
          intrinsicFrameMetric (I := I) (X.obj (τ k)).metric
            (hEnorm (τ k)) (c i) z v v ≤ 2 * ‖v‖ ^ 2) ∧
      ∀ y : (X.obj (τ k)).M,
        riemannianEDistOf (I := I) (X.obj (τ k)).metric
          (X.obj (τ k)).basepoint y ≤ ENNReal.ofReal r →
        ∃ i, y ∈ (charts i).hom '' Metric.ball (0 : E) (ρ / 10) := by
    intro k
    exact hn₀ (τ k) (Nat.le_add_right n₀ k)
  choose c charts hbase hc hell hsourcecover using hdata
  have hcompleteτ : SeqMetricComplete (I := I) (X.subseq τ) :=
    ⟨fun k => hcomplete.complete (τ k)⟩
  have hjetsτ : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        ((X.subseq τ).obj k) ((X.subseq τ).obj k).basepoint R p C := by
    intro p
    obtain ⟨C, hC, hb⟩ := hjets p
    exact ⟨C, hC, hb.filter_mono hτ.tendsto_atTop⟩
  obtain ⟨ψ, hψ, gInf, hlim⟩ :=
    exists_finite_intrinsicBallChart_metric_limit_subsequence_of_curvature_bounds
      (X.subseq τ) hcompleteτ (fun k => hconn (τ k)) hr hrR hρ hρR hjetsτ
      (fun i k => c k i) (fun i k => hc k i) (fun i k => charts k i)
      (fun i => Eventually.of_forall fun k => hell k i)
  refine ⟨ρ, hρ, hρR, N, τ ∘ ψ, hτ.comp hψ,
    (fun i k => c (ψ k) i), (fun i k => charts (ψ k) i), gInf,
    (fun k => hbase (ψ k)),
    (fun i k => hc (ψ k) i), (fun k => hsourcecover (ψ k)),
    (fun i k => hell (ψ k) i), hlim⟩

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_finite_pointed_covering_intrinsicBallChart_metric_transition_limit_subsequence
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    letI : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle (I := I)
    letI : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
      fun k => (X.obj k).riemInner (I := I)
    letI : ∀ k, IsContinuousRiemannianBundle E
        (fun x : (X.obj k).M => TangentSpace I x) :=
      fun k => (X.obj k).riemBundle_cont (I := I)
    letI : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
    letI : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
    letI : ∀ k, CompleteSpace (X.obj k).M :=
      fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    let hEnorm : ∀ k (x : (X.obj k).M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner x v v)) := by
      intro k x v
      with_unfolding_all
        exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (X.obj k).metric x v
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ R - r ∧ ∃ N : ℕ,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∃ (c : Fin (N + 1) → ∀ k, (X.obj (phi k)).M)
          (charts : ∀ i k, IntrinsicBallChart (I := I) (X.obj (phi k)).metric
            (hEnorm (phi k)) (c i k) ρ)
          (gInf : Fin (N + 1) → E → E →L[ℝ] E →L[ℝ] ℝ),
          (∀ k, c 0 k = (X.obj (phi k)).basepoint) ∧
          (∀ i k, riemannianEDistOf (I := I) (X.obj (phi k)).metric
            (X.obj (phi k)).basepoint (c i k) ≤ ENNReal.ofReal r) ∧
          (∀ k, ∀ y : (X.obj (phi k)).M,
            riemannianEDistOf (I := I) (X.obj (phi k)).metric
              (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r →
            ∃ i, y ∈ (charts i k).hom '' Metric.ball (0 : E) (ρ / 10)) ∧
          (∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I)
                (X.obj (phi k)).metric (hEnorm (phi k)) (c i k) z v v ∧
              intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k) z v v ≤ 2 * ‖v‖ ^ 2) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (gInf i) (Metric.ball 0 ρ) ∧
            MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
              (fun k => intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                (hEnorm (phi k)) (c i k)) (gInf i) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v w, gInf i z v w = gInf i z w v) ∧
            (∀ z ∈ Metric.ball 0 ρ, ∀ v,
              (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf i z v v ∧
                gInf i z v v ≤ 2 * ‖v‖ ^ 2)) ∧
          ∃ near : Fin (N + 1) → Fin (N + 1) → Bool,
            (∀ k i j,
              (near i j = true →
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k) <
                  ENNReal.ofReal (ρ / 4)) ∧
              (near i j = false → ENNReal.ofReal (ρ / 4) ≤
                riemannianEDistOf (I := I) (X.obj (phi k)).metric (c i k) (c j k))) ∧
            (∀ k i j, near i j = false →
              Disjoint ((charts i k).hom '' Metric.ball (0 : E) (ρ / 10))
                ((charts j k).hom '' Metric.ball (0 : E) (ρ / 10))) ∧
            ∃ Jinf Jbarinf : {a : Fin (N + 1) × Fin (N + 1) // near a.1 a.2 = true} → E → E,
              ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (Jinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
                ContDiffOn ℝ (⊤ : ℕ∞) (Jbarinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
                MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
                  (fun k => ((charts a.1.1 k).toNormalBallChart
                    (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.1 k) hρ).transition
                    ((charts a.1.2 k).toNormalBallChart
                      (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.2 k) hρ)) (Jinf a) ∧
                MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
                  (fun k => ((charts a.1.2 k).toNormalBallChart
                    (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.2 k) hρ).transition
                    ((charts a.1.1 k).toNormalBallChart
                      (X.obj (phi k)).metric (hEnorm (phi k)) (c a.1.1 k) hρ)) (Jbarinf a) ∧
                (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
                  Jinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jbarinf a (Jinf a z) = z) ∧
                (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
                  Jbarinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jinf a (Jbarinf a z) = z) := by
  classical
  let : ∀ k, RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle (I := I)
  let : ∀ k, (x : (X.obj k).M) → InnerProductSpace ℝ (TangentSpace I x) :=
    fun k => (X.obj k).riemInner (I := I)
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj k).M => TangentSpace I x) :=
    fun k => (X.obj k).riemBundle_cont (I := I)
  let : ∀ k, EMetricSpace (X.obj k).M := fun k => (X.obj k).emetricSpace (I := I)
  let : ∀ k, IsRiemannianManifold I (X.obj k).M := fun _ => ⟨fun _ _ => rfl⟩
  let : ∀ k, CompleteSpace (X.obj k).M :=
    fun k => MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  intro hEnorm
  obtain ⟨ρ, hρ, hρR, N, phi, hphi, c, charts, gInf, hbase, hc, hcover, hell, hmetric⟩ :=
    exists_finite_pointed_covering_intrinsicBallChart_metric_limit_subsequence
      X hcomplete hconn hr hrR hη hjets hinj
  have hbound : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal r → ∀ z : E, ‖z‖ ≤ ρ →
            ‖iteratedFDeriv ℝ p
              (intrinsicFrameMetric (I := I) (X.obj k).metric (hEnorm k) x) z‖ ≤ C := by
    intro p
    exact exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_on_ball
      X hcomplete hconn hr hrR hρR hjets p
  choose C hC hCb using hbound
  have hequiv : ∀ i k z, z ∈ Metric.ball (0 : E) ρ → ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
          ((charts i k).toNormalBallChart (X.obj (phi k)).metric (hEnorm (phi k))
            (c i k) hρ).metric (X.obj (phi k)).metric z v v ∧
        ((charts i k).toNormalBallChart (X.obj (phi k)).metric (hEnorm (phi k))
          (c i k) hρ).metric (X.obj (phi k)).metric z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro i k z hz v
    rw [(charts i k).metric_eq_intrinsicFrameMetric (I := I)
      (X.obj (phi k)).metric (hEnorm (phi k)) (c i k) hρ hz]
    exact hell i k z hz v
  have hchartjets : ∀ i p, ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) ρ,
      ‖iteratedFDeriv ℝ p
        (((charts i k).toNormalBallChart (X.obj (phi k)).metric (hEnorm (phi k))
          (c i k) hρ).metric (X.obj (phi k)).metric) z‖ ≤ C p := by
    intro i p
    filter_upwards [(hCb p).filter_mono hphi.tendsto_atTop] with k hk
    exact (charts i k).metricDerivBound_of_intrinsicFrameMetric (I := I)
      (X.obj (phi k)).metric (hEnorm (phi k)) (c i k) hρ p
      (fun z hz => hk (c i k) (hc i k) z
        (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)))
  obtain ⟨ψ, hψ, near, hnear, hfar, Jinf, Jbarinf, htrans⟩ :=
    IntrinsicBallChart.exists_finite_transition_limit_subsequence
      (fun k => (X.obj (phi k)).metric) (fun k => hEnorm (phi k)) c hρ charts
      hequiv (fun _ p => C p) (fun _ p => hC p) hchartjets
  refine ⟨ρ, hρ, hρR, N, phi ∘ ψ, hphi.comp hψ,
    (fun i k => c i (ψ k)), (fun i k => charts i (ψ k)), gInf,
    (fun k => hbase (ψ k)),
    (fun i k => hc i (ψ k)), (fun k => hcover (ψ k)),
    (fun i k => hell i (ψ k)), ?_, near, ?_, hfar, Jinf, Jbarinf, htrans⟩
  · intro i
    obtain ⟨hs, hconv, hsymm, hb⟩ := hmetric i
    exact ⟨hs, hconv.comp_subseq hψ, hsymm, hb⟩
  · intro k i j
    simpa only [Function.comp_apply, PointedRiemannianManifold.riemannianEDistOf_eq_edist (I := I)
      (X.obj (phi (ψ k)))] using hnear k i j

end DifferentialGeometry.CheegerGromovCompactness

end

end
