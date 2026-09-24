import DifferentialGeometry.Analysis.Calculus.Compactness.EventuallyBounded
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalUniformBounds
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric

section

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_finite_normalBallChart_metric_limit_subsequence
    {ι : Type*} [Finite ι]
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (c : ι → ∀ k, (X.obj k).M)
    (charts : ∀ i k, NormalBallChart (I := I) (c i k))
    {U : Set E} (hU : IsOpen U)
    (hsub : ∀ i k, U ⊆ Metric.ball (0 : E) (charts i k).radius)
    (hequiv : ∀ i, ∀ᶠ k in atTop, (charts i k).MetricEquivOn (X.obj k).metric U)
    (hjets : ∀ i p, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ k in atTop, (charts i k).MetricDerivBound (X.obj k).metric K p C) :
    ∃ (phi : ℕ → ℕ) (gInf : ι → E → E →L[ℝ] E →L[ℝ] ℝ),
      StrictMono phi ∧ ∀ i,
        ContDiffOn ℝ (⊤ : ℕ∞) (gInf i) U ∧
        MapCInfConvergenceOnCompacts U
          (fun k => (charts i (phi k)).metric (X.obj (phi k)).metric) (gInf i) ∧
        (∀ z ∈ U, ∀ v w, gInf i z v w = gInf i z w v) ∧
        ∀ z ∈ U, ∀ v,
          (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf i z v v ∧ gInf i z v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let g : ℕ → E → (ι → E →L[ℝ] E →L[ℝ] ℝ) :=
    fun k z i => (charts i k).metric (X.obj k).metric z
  have hsmooth_i : ∀ k i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => g k z i) U := by
    intro k i
    exact (charts i k).metric_cont_diff_on (X.obj k).metric hU
      ((charts i k).smooth_to.mono (hsub i k))
  have hsmooth : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) U :=
    fun k => contDiffOn_pi.mpr (hsmooth_i k)
  have hbounded : ∀ p, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ p (g k) z‖ ≤ C := by
    intro p K hK hKU
    choose C hC using fun i => hjets i p K hK hKU
    refine ⟨∑ i, max (C i) 0, ?_⟩
    have hcall : ∀ᶠ k in atTop, ∀ i, (charts i k).MetricDerivBound (X.obj k).metric K p (C i) :=
      Filter.eventually_all.mpr hC
    filter_upwards [hcall] with k hk
    intro z hz
    have hcd : ∀ i, ContDiffAt ℝ (p : ℕ∞) (fun y => g k y i) z := fun i =>
      ((hsmooth_i k i).contDiffAt (hU.mem_nhds (hKU hz))).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right (C i) 0)]
    intro i
    exact (hk i z hz).trans ((le_max_left (C i) 0).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))
  obtain ⟨phi, G, hphi, hG, hconv⟩ :=
    exists_cInf_subseq_on_of_eventually_bdd hU g hsmooth hbounded
  refine ⟨phi, fun i z => G z i, hphi, fun i => ?_⟩
  have hc := mapCInf_apply hU hconv (fun k => hsmooth (phi k)) hG i
  refine ⟨contDiffOn_pi.mp hG i, hc, ?_, ?_⟩
  · intro z hz v w
    have hlim := tendsto_of_cInf hc hz
    have hvw : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) := by fun_prop
    have hwv : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A w v) := by fun_prop
    apply tendsto_nhds_unique ((hvw.tendsto _).comp hlim)
    convert (hwv.tendsto _).comp hlim using 1
    ext k
    dsimp only [g, Function.comp_apply]
    rw [NormalBallChart.metric_apply, NormalBallChart.metric_apply]
    exact (X.obj (phi k)).metric.symm _ _ _
  · intro z hz v
    have hlim := tendsto_of_cInf hc hz
    have heval : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v) := by fun_prop
    have htend := (heval.tendsto _).comp hlim
    have he := (hequiv i).filter_mono hphi.tendsto_atTop
    exact ⟨ge_of_tendsto htend (he.mono fun k hk => (hk z hz v).1),
      le_of_tendsto htend (he.mono fun k hk => (hk z hz v).2)⟩

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
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

omit [CompleteSpace E] in
theorem exists_finite_intrinsicBallChart_metric_limit_subsequence_of_curvature_bounds
    {ι : Type*} [Finite ι]
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r ρ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hρ : 0 < ρ) (hρR : ρ ≤ R - r)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (c : ι → ∀ k, (X.obj k).M)
    (hc : ∀ i k, riemannianEDistOf (I := I) (X.obj k).metric
      (X.obj k).basepoint (c i k) ≤ ENNReal.ofReal r) :
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
    ∀ charts : ∀ i k, IntrinsicBallChart (I := I) (X.obj k).metric
        (hEnorm k) (c i k) ρ,
      (∀ i, ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
        (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (X.obj k).metric
          (hEnorm k) (c i k) z v v ∧
        intrinsicFrameMetric (I := I) (X.obj k).metric (hEnorm k) (c i k) z v v ≤
          2 * ‖v‖ ^ 2) →
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
          ∃ gInf : ι → E → E →L[ℝ] E →L[ℝ] ℝ,
            ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (gInf i) (Metric.ball 0 ρ) ∧
              MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
                (fun k => intrinsicFrameMetric (I := I) (X.obj (phi k)).metric
                  (hEnorm (phi k)) (c i (phi k))) (gInf i) ∧
              (∀ z ∈ Metric.ball 0 ρ, ∀ v w, gInf i z v w = gInf i z w v) ∧
              (∀ z ∈ Metric.ball 0 ρ, ∀ v,
                (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf i z v v ∧
                  gInf i z v v ≤ 2 * ‖v‖ ^ 2) := by
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
  intro hEnorm charts helliptic
  let nc : ∀ i k, NormalBallChart (I := I) (c i k) := fun i k =>
    (charts i k).toNormalBallChart (I := I) (X.obj k).metric
      (hEnorm k) (c i k) hρ
  have hnrad : ∀ i k, (nc i k).radius = ρ := fun _ _ => rfl
  have hne : ∀ i, ∀ᶠ k in atTop,
      (nc i k).MetricEquivOn (X.obj k).metric (Metric.ball 0 ρ) := by
    intro i
    filter_upwards [helliptic i] with k hk
    exact (charts i k).metricEquivOn_of_intrinsicFrameMetric (I := I)
        (X.obj k).metric (hEnorm k) (c i k) hρ
        hk
  have hnb : ∀ i p, ∀ A : Set E, IsCompact A → A ⊆ Metric.ball 0 ρ →
      ∃ C : ℝ, ∀ᶠ k in atTop,
        (nc i k).MetricDerivBound (X.obj k).metric A p C := by
    intro i p A _ hA
    obtain ⟨C, _, hC⟩ :=
      exists_eventually_intrinsicFrameMetric_iteratedFDeriv_norm_le_on_ball
        X hcomplete hconn hr hrR hρR hjets p
    refine ⟨C, ?_⟩
    filter_upwards [hC] with k hk
    have hball := (charts i k).metricDerivBound_of_intrinsicFrameMetric (I := I)
      (X.obj k).metric (hEnorm k) (c i k) hρ p
      (fun z hz => hk (c i k) (hc i k) z
        (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)))
    exact fun z hz => hball z (hA hz)
  obtain ⟨phi, gInf, hphi, hlim⟩ :=
    exists_finite_normalBallChart_metric_limit_subsequence X
      (fun i k => c i k) nc Metric.isOpen_ball
      (fun i k => by rw [hnrad]) hne hnb
  refine ⟨phi, hphi, gInf, ?_⟩
  intro i
  obtain ⟨hsm, hconv, hsymm, hb⟩ := hlim i
  refine ⟨hsm, ?_, hsymm, hb⟩
  refine hconv.congr Metric.isOpen_ball ?_ (fun _ _ => rfl)
  intro k z hz
  exact ((charts i (phi k)).metric_eq_intrinsicFrameMetric (I := I)
    (X.obj (phi k)).metric (hEnorm (phi k)) (c i (phi k)) hρ hz).symm

end DifferentialGeometry.CheegerGromovCompactness

end

end
