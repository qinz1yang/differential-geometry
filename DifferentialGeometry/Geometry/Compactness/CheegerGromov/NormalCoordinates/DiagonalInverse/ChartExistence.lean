import DifferentialGeometry.Geometry.Exponential.NormalBall.MetricBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.ChartEndpoint
import DifferentialGeometry.Geometry.Exponential.NormalBall.Identity
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Smallness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.SymmetricFlow

noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
theorem exists_chart_diagonal_inverse_with_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {p : M} (c : NormalBallChart (I := I) p) (b : c.MetricBounds g) {r : ℝ}
    (hrMetric : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (q : NNReal) (hq : 0 < q) (hqWide : 6 * (q : ℝ) < r)
    (hqAccel : 3 * b.C 1 * (2 * (q : ℝ)) ^ 2 ≤ (2 / 3 : ℝ) * (q : ℝ))
    (herr : PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊⁻¹) :
    ∃ (Φ : (E × E) → ℝ → E × E) (δ : ℝ)
        (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[ℝ] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (chartPhaseK g b (2 * q)) : NNReal) : ℝ) * ((q : ℝ) / 2) ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z => (z.1, (Φ z 1).1)) ∧
      e 0 = 0 ∧
      Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
      ContDiffOn ℝ ∞ (e : E × E → E × E) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        c.pair (e z) = diagExp g hEnorm (c.tangent z)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        z.1 ∈ Metric.ball (0 : E) c.radius ∧
        (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
        (e z).2 ∈ Metric.ball (0 : E) c.radius) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc (-1) 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        HasDerivWithinAt (Φ z) (PhaseFlow.phaseField (c.accel g) (Φ z t)) (Icc (-1) 1) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      ApproximatesLinearOn (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) e.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (chartPhaseK g b (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK g b (2 * q))) := by
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, _, hΦbox, hΦzero, happrox, hΦsmooth⟩ :=
    exists_chartBiflow g c b hrMetric hrQuarter q hq hqWide hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hdeltaEq, hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq happrox herr
  have happroxOpen : ApproximatesLinearOn (fun z => (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E))
      (Metric.ball (0 : E × E) q) (PhaseFlow.phaseErr (chartPhaseK g b (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn ℝ ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr) Metric.isOpen_ball hΦsmooth e hsource hcoe
  have heZero : e 0 = 0 := by
    rw [hcoe]
    simp only [Prod.fst_zero, hΦzero]
    rfl
  have heSmooth : ContDiffOn ℝ ∞ (e : E × E → E × E) e.source := by
    rw [hsource, hcoe]
    exact hΦsmooth
  have htarget' : Metric.closedBall (0 : E × E) δ ⊆ e.target := by
    have htargetE : Metric.closedBall (e 0) δ ⊆ e.target := by
      simpa only [hcoe] using htarget
    simpa only [heZero] using htargetE
  have hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      c.pair (e z) = diagExp g hEnorm (c.tangent z) := by
    intro z hz
    have hend := c.phase_endpoint_eq_expMapIntrinsic g hEnorm hrQuarter
      (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
    rw [hΦ0 z hz] at hend
    rw [hcoe]
    exact Prod.ext rfl hend
  have hrChart : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) c.radius := by
    intro z hz
    exact Metric.ball_subset_ball (by nlinarith [c.radius_pos]) (hrQuarter hz)
  have hfence : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      z.1 ∈ Metric.ball (0 : E) c.radius ∧
      (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
      (e z).2 ∈ Metric.ball (0 : E) c.radius := by
    intro z hz
    have hzNorm : ‖z‖ ≤ (q : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hqr : (q : ℝ) < r := by nlinarith [hqWide]
    have hzFirst : z.1 ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_fst_le z).trans_lt (hzNorm.trans_lt hqr)
    have hzEnd : (Φ z 1).1 ∈ Metric.ball (0 : E) r := (hΦbox z hz 1 (by norm_num)).1
    rw [hcoe]
    exact ⟨hrChart hzFirst, hrChart hzFirst, hrChart hzEnd⟩
  exact ⟨Φ, δ, e, hδ, hdeltaEq, hsource, hcoe, heZero, htarget', heSmooth, hinvSmooth,
    hdiag, hfence, hΦ0, hΦcont, hΦwithin, hΦbox, hinvApprox⟩

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem exists_uniform_chart_diagonal_inverse
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    (b : ∀ k, (c k).MetricBounds (g k))
    (hC : ∀ k, (b k).C = (b 0).C)
    {r : ℝ} (hr : 0 < r)
    (hrMetric : ∀ k, Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (b k).radius)
    (hrQuarter : ∀ k, Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) ((c k).radius / 4)) :
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : ℕ → (E × E) → ℝ → E × E)
        (e : ℕ → OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ 6 * (q : ℝ) < r ∧ 0 < δ ∧ η < 1 / 24 ∧
      ∀ k,
        (e k).source = Metric.ball (0 : E × E) q ∧
        (e k : E × E → E × E) = (fun z => (z.1, (Φ k z 1).1)) ∧
        e k 0 = 0 ∧
        Metric.closedBall (0 : E × E) δ ⊆ (e k).target ∧
        ContDiffOn ℝ ∞ (e k : E × E → E × E) (e k).source ∧
        ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) (e k).target ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          (c k).pair (e k z) = diagExp (g k) (hEnorm k) ((c k).tangent z)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          z.1 ∈ Metric.ball (0 : E) (c k).radius ∧
          (e k z).1 ∈ Metric.ball (0 : E) (c k).radius ∧
          (e k z).2 ∈ Metric.ball (0 : E) (c k).radius) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ k z 0 = z) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          IsIntegralCurveOn (Φ k z) (fun _ => MetricKoszul.metricSpray ((c k).metric (g k)))
            (Icc 0 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (0 : ℝ) 1,
          (Φ k z t).1 ∈ Metric.ball (0 : E) r) ∧
        ApproximatesLinearOn ((e k).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))
          (e k).target η := by
  classical
  obtain ⟨q, hq, hqWide, hqAccel, herr, hinvErr⟩ := exists_chart_biq_inv (g 0) (b 0) hr
  have hphase : ∀ k R, chartPhaseK (g k) (b k) R = chartPhaseK (g 0) (b 0) R := by
    intro k R
    apply NNReal.eq
    simp only [chartPhaseK, hC k]
  have haccel : ∀ k, 3 * (b k).C 1 * (2 * (q : ℝ)) ^ 2 ≤ (2 / 3 : ℝ) * (q : ℝ) := by
    intro k
    simpa only [hC k] using hqAccel
  have herrStage : ∀ k, PhaseFlow.phaseErr (chartPhaseK (g k) (b k) (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊⁻¹ := by
    intro k
    simpa only [hphase k] using herr
  choose Φ delta e hdelta hdeltaEq hsource he hzero htarget hsmooth hinvSmooth hdiag hfence
      hinit hcont hwithin hbox happrox using fun k =>
    exists_chart_diagonal_inverse_with_radius (g k) (hEnorm k) (c k) (b k)
      (hrMetric k) (hrQuarter k) q hq hqWide (haccel k) (herrStage k)
  let δ := delta 0
  let η : NNReal := ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[ℝ] (E × E))‖₊ *
      (‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊⁻¹ -
        PhaseFlow.phaseErr (chartPhaseK (g 0) (b 0) (2 * q)))⁻¹ *
      PhaseFlow.phaseErr (chartPhaseK (g 0) (b 0) (2 * q))
  have hdEq : ∀ k, delta k = δ := by
    intro k
    dsimp only [δ]
    rw [hdeltaEq k, hdeltaEq 0, hphase k]
  refine ⟨q, δ, η, Φ, e, hq, hqWide, hdelta 0, hinvErr, ?_⟩
  intro k
  refine ⟨hsource k, he k, hzero k, ?_, hsmooth k, hinvSmooth k,
    hdiag k, hfence k, hinit k, ?_, ?_, ?_⟩
  · simpa only [hdEq k] using htarget k
  · intro z hz
    exact (c k).isIntegralCurveOn_metricSpray_of_phase (g k) (b k)
      (hrMetric k) (hrQuarter k) (hwithin k z hz) (hbox k z hz)
  · intro z hz t ht
    exact (hbox k z hz t ⟨by linarith [ht.1], ht.2⟩).1
  · simpa only [η, hphase k] using happrox k

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem chart_diagonal_inverse_zero_section
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {p : M} (c : NormalBallChart (I := I) p)
    (e : OpenPartialHomeomorph (E × E) (E × E)) {q : ℝ}
    (hsource : e.source = Metric.ball (0 : E × E) q)
    (hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      c.pair (e z) = diagExp g hEnorm (c.tangent z))
    (hfence : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      z.1 ∈ Metric.ball (0 : E) c.radius ∧
      (e z).1 ∈ Metric.ball (0 : E) c.radius ∧ (e z).2 ∈ Metric.ball (0 : E) c.radius)
    {x : E} (hx : x ∈ Metric.ball (0 : E) q) :
    (x, x) ∈ e.target ∧ e.symm (x, x) = (x, 0) := by
  have hx0 : (x, (0 : E)) ∈ Metric.ball (0 : E × E) q := by
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg x)] using hx
  have hxClosed := Metric.ball_subset_closedBall hx0
  have hf := hfence (x, 0) hxClosed
  have hd := hdiag (x, 0) hxClosed
  have hp : c.pair (e (x, 0)) = (c.hom x, c.hom x) := by
    have hvel : mfderiv 𝓘(ℝ, E) I (fun u : E => c.hom u) x (0 : E) =
        (0 : TangentSpace I (c.hom x)) := map_zero _
    simpa only [NormalBallChart.tangent, diagExp, hvel, expMapIntrinsic_zero] using hd
  have he : e (x, 0) = (x, x) := by
    apply Prod.ext
    · exact c.hom.injOn (c.ball_subset hf.2.1) (c.ball_subset hf.1) (congrArg Prod.fst hp)
    · exact c.hom.injOn (c.ball_subset hf.2.2) (c.ball_subset hf.1) (congrArg Prod.snd hp)
  have hsrc : (x, (0 : E)) ∈ e.source := by rwa [hsource]
  exact ⟨he ▸ e.map_source hsrc, by simpa only [he] using e.left_inv hsrc⟩

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Set Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal NNReal
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

theorem exists_metric_diagonal_inverse_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (hg : RiemannianMetricComplete g)
    {r R qStage : ℝ} (hr : 0 < r) (hrR : r < R) (hqStage : 0 < qStage)
    (hbound : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner z v v ∧ g.inner z v v ≤ 2 * ‖v‖ ^ 2) :
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : (E × E) → ℝ → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ (q : ℝ) < qStage ∧ 6 * (q : ℝ) < r ∧ 0 < δ ∧ η < 1 / 24 ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z => (z.1, (Φ z 1).1)) ∧
      e 0 = 0 ∧ Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
      ContDiffOn ℝ ∞ (e : E × E → E × E) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (Φ z) (fun _ => MetricKoszul.metricSpray (fun z => g.inner z))
          (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (0 : ℝ) 1,
        (Φ z t).1 ∈ Metric.ball (0 : E) r) ∧
      (∀ x ∈ Metric.ball (0 : E) q,
        (x, x) ∈ e.target ∧ e.symm (x, x) = (x, 0)) ∧
      ApproximatesLinearOn (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) e.target η := by
  let : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let metricSpace : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : PseudoEMetricSpace E := metricSpace.toPseudoEMetricSpace
  let : @CompleteSpace E metricSpace.toUniformSpace := hg.complete
  have hnorm : IsMetricNorm (I := 𝓘(ℝ, E)) g :=
    isMetricNorm_of_riemannianBundle g
  let rChart := max R (4 * r)
  have hChart : 0 < rChart := (hr.trans hrR).trans_le (le_max_left _ _)
  let c := NormalBallChart.identity (E := E) hChart
  obtain ⟨b, hb⟩ := NormalBallChart.exists_metricBounds_identity_of_inner_bounds
    g hChart hr hrR (le_max_left _ _) hbound
  have hrMetric : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius := by rw [hb]
  have hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4) := by
    apply Metric.ball_subset_ball
    change r ≤ max R (4 * r) / 4
    linarith [le_max_right R (4 * r)]
  have hsmall : 0 < min r (6 * qStage) := lt_min hr (mul_pos (by norm_num) hqStage)
  obtain ⟨q, hq, hqWideSmall, hqAccel, herr, hinvErr⟩ := exists_chart_biq_inv g b hsmall
  have hqWide : 6 * (q : ℝ) < r := hqWideSmall.trans_le (min_le_left _ _)
  have hqLt : (q : ℝ) < qStage := by
    have h := hqWideSmall.trans_le (min_le_right _ _)
    linarith
  obtain ⟨Φ, δ, e, hδ, _, hsource, hcoe, hzero, htarget, hsmooth, hinv,
      hdiag, hfence, hinit, _, hwithin, hbox, happrox⟩ :=
    exists_chart_diagonal_inverse_with_radius g hnorm c b hrMetric hrQuarter q hq hqWide hqAccel herr
  let η : NNReal := ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[ℝ] (E × E))‖₊ *
      (‖((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))‖₊⁻¹ -
        PhaseFlow.phaseErr (chartPhaseK g b (2 * q)))⁻¹ *
      PhaseFlow.phaseErr (chartPhaseK g b (2 * q))
  refine ⟨q, δ, η, Φ, e, hq, hqLt, hqWide, hδ, hinvErr, hsource, hcoe, hzero, htarget,
    hsmooth, hinv, hinit, ?_, ?_, ?_, happrox⟩
  · intro z hz
    have hcurve := c.isIntegralCurveOn_metricSpray_of_phase g b hrMetric hrQuarter
      (hwithin z hz) (hbox z hz)
    simpa only [c, NormalBallChart.metric_identity] using hcurve
  · intro z hz t ht
    exact (hbox z hz t ⟨by linarith [ht.1], ht.2⟩).1
  · intro x hx
    exact chart_diagonal_inverse_zero_section g hnorm c e hsource hdiag hfence hx

end DifferentialGeometry.CheegerGromovCompactness

end
