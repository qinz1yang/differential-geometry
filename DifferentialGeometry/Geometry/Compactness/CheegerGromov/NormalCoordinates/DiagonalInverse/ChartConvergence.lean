import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.ChartExistence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.ChartConvergence
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.InverseConvergence
import DifferentialGeometry.Geometry.Metric.Construction.CompleteExtension

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

theorem exists_uniform_chart_diagonal_inverse_of_metric_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRadius : ∀ k, R ≤ (c k).radius)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) R))
    (hrQuarter : ∀ k, Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) ((c k).radius / 4))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R))
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) R)
      (fun k => (c k).metric (g k)) B) :
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
  obtain ⟨C, b, hb⟩ := NormalBallChart.exists_metricBounds_of_convergence
    g c hr hrR hRadius hell hB hconv
  apply exists_uniform_chart_diagonal_inverse g hEnorm c b
    (fun k => (hb k).2.trans (hb 0).2.symm) hr
  · intro k
    rw [(hb k).1]
  · exact hrQuarter

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter
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

theorem exists_chart_diagonal_inverse_convergence_of_metric_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRadius : ∀ k, R ≤ (c k).radius)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) R))
    (hrQuarter : ∀ k, Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) ((c k).radius / 4))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R))
    (hBsymm : ∀ z ∈ Metric.ball (0 : E) R, ∀ v w : E, B z v w = B z w v)
    (hBell : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ 2 * ‖v‖ ^ 2)
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) R)
      (fun k => (c k).metric (g k)) B) :
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : ℕ → (E × E) → ℝ → E × E)
        (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
        (qInf : NNReal) (δInf : ℝ) (etaInf : NNReal)
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ 6 * (q : ℝ) < r ∧ 0 < δ ∧ η < 1 / 24 ∧
      (∀ k,
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
          (e k).target η) ∧
      0 < qInf ∧ qInf < q ∧ 0 < δInf ∧ etaInf < 1 / 24 ∧
      eInf.source = Metric.ball (0 : E × E) qInf ∧
      Metric.closedBall (0 : E × E) δInf ⊆ eInf.target ∧
      ContDiffOn ℝ ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) eInf.target ∧
      (∀ x ∈ Metric.ball (0 : E) qInf,
        (x, x) ∈ eInf.target ∧ eInf.symm (x, x) = (x, 0)) ∧
      ApproximatesLinearOn (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) eInf.target etaInf ∧
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun k => (e k : E × E → E × E)) eInf ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < min δ δInf ∧
        eInf.symm '' Metric.closedBall (0 : E × E) ε ⊆ Metric.ball 0 qInf ∧
        (∀ᶠ k in Filter.atTop, MapsTo (e k).symm (Metric.closedBall 0 ε) (Metric.ball 0 qInf)) ∧
        MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) ε)
          (fun k => ((e k).symm : E × E → E × E)) eInf.symm := by
  obtain ⟨q, δ, η, Φ, e, hq, hqWide, hδ, hη, hstage⟩ :=
    exists_uniform_chart_diagonal_inverse_of_metric_convergence g hEnorm c hr hrR
      hRadius hell hrQuarter hB hconv
  let Rmid := (r + R) / 2
  have hrMid : r < Rmid := by dsimp only [Rmid]; linarith
  have hmidR : Rmid < R := by dsimp only [Rmid]; linarith
  have hBpos : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E, v ≠ 0 → 0 < B z v v := by
    intro z hz v hv
    exact (mul_pos (by norm_num) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le
      (hBell z hz v).1
  obtain ⟨gInf, hgInf, _, hinner⟩ :=
    Geometry.exists_complete_metric_extension_of_contDiffOn_bilinearField_on_ball
      B (hr.trans hrMid) hmidR hBsymm hBpos hB
  let BInf : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => gInf.inner z
  have hinnerR : ∀ z ∈ Metric.ball (0 : E) Rmid, BInf z = B z := by
    intro z hz
    ext v w
    exact hinner z ((by exact le_of_lt (show ‖z‖ < Rmid by simpa only [Metric.mem_ball, dist_zero_right] using hz))) v w
  have hInfBound : ∀ z ∈ Metric.ball (0 : E) Rmid, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf.inner z v v ∧ gInf.inner z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro z hz v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ BInf z v v ∧ BInf z v v ≤ 2 * ‖v‖ ^ 2
    rw [hinnerR z hz]
    exact hBell z (Metric.ball_subset_ball hmidR.le hz) v
  obtain ⟨qInf, δInf, etaInf, ΦInf, eInf, hqInf, hqInfLt, _, hδInf, hEtaInf,
      hsourceInf, heInf, hzeroInf, htargetInf, hInfC, hInvC, hinitInf, hcurveInf,
      hstayInf, hdiagInf, happroxInf⟩ :=
    exists_metric_diagonal_inverse_lt gInf hgInf hr hrMid
      (show (0 : ℝ) < q from hq) hInfBound
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ ((c k).metric (g k)) (Metric.ball (0 : E) r) := by
    intro k
    exact ((c k).metric_cont_diff_on (g k) Metric.isOpen_ball (c k).smooth_to).mono
      (Metric.ball_subset_ball (hrR.le.trans (hRadius k)))
  have hUsub : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) R := Metric.ball_subset_ball hrR.le
  have hUrMid : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) Rmid := Metric.ball_subset_ball hrMid.le
  have hinnerU : EqOn BInf B (Metric.ball (0 : E) r) :=
    fun z hz => hinnerR z (hUrMid hz)
  have hBInfC : ContDiffOn ℝ ∞ BInf (Metric.ball (0 : E) r) :=
    (hB.mono hUsub).congr (fun z hz => hinnerU hz)
  have hconvSmall : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) r)
      (fun k => (c k).metric (g k)) B := fun K hK hKU => hconv K hK (hKU.trans hUsub)
  have hconvInner : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) r)
      (fun k => (c k).metric (g k)) BInf :=
    hconvSmall.congr Metric.isOpen_ball (fun _ _ _ => rfl) hinnerU
  have hco : ∀ k z, z ∈ Metric.ball (0 : E) r → IsCoercive ((c k).metric (g k) z) :=
    fun k z hz => (hell k).coercive (g k) (hUsub hz)
  have hcoInf : ∀ z, z ∈ Metric.ball (0 : E) r → IsCoercive (BInf z) := by
    intro z hz
    rw [hinnerU hz]
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using (hBell z (hUsub hz) v).1
  have hqSubset : Metric.ball (0 : E × E) qInf ⊆ Metric.closedBall 0 q :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hqInfLt.le)
  have hqInfSubset : Metric.ball (0 : E × E) qInf ⊆ Metric.closedBall 0 qInf :=
    Metric.ball_subset_closedBall
  obtain ⟨hforward, ε, hε, hεlt, hInfMap, hstageMap, hinvConv⟩ :=
    exists_metricSpray_diagonal_inverse_convergence Metric.isOpen_ball hsmooth hBInfC hco hcoInf
      hconvInner (show (0 : ℝ) < qInf from hqInf) hqInfLt hδ hδInf
      (fun k z hz => ⟨(hstage k).2.2.2.2.2.2.2.2.1 z (hqSubset hz),
        (hstage k).2.2.2.2.2.2.2.2.2.1 z (hqSubset hz)⟩)
      (fun z hz => ⟨hinitInf z (hqInfSubset hz), hcurveInf z (hqInfSubset hz)⟩)
      (fun k z hz t ht => (hstage k).2.2.2.2.2.2.2.2.2.2.1 z (hqSubset hz) t ht)
      (fun z hz t ht => hstayInf z (hqInfSubset hz) t ht)
      (fun k => (hstage k).2.1) heInf (fun k => (hstage k).1) hsourceInf hzeroInf
      (fun k => (hstage k).2.2.2.2.1) hInfC hInvC
      (fun k => (hstage k).2.2.2.1) htargetInf
  exact ⟨q, δ, η, Φ, e, qInf, δInf, etaInf, eInf, hq, hqWide, hδ, hη, hstage,
    hqInf, hqInfLt, hδInf, hEtaInf, hsourceInf, htargetInf, hInfC, hInvC,
    hdiagInf, happroxInf, hforward, ε, hε, hεlt, hInfMap, hstageMap, hinvConv⟩

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem exists_recentered_chart_diagonal_inverse_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    (a : E) {r R : ℝ} (hr : 0 < r)
    (hchart : ∀ k, R ≤ (c k).radius)
    (htranslate : Metric.ball a (8 * r) ⊆ Metric.ball (0 : E) R)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) R))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R))
    (hBsymm : ∀ z ∈ Metric.ball (0 : E) R, ∀ v w : E, B z v w = B z w v)
    (hBell : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ 2 * ‖v‖ ^ 2)
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) R)
      (fun k => (c k).metric (g k)) B) :
    let hr8 : 0 < 8 * r := by positivity
    let hball : ∀ k, Metric.ball a (8 * r) ⊆ Metric.ball (0 : E) (c k).radius :=
      fun k => htranslate.trans (Metric.ball_subset_ball (hchart k))
    let cc := fun k => (c k).recenter a hr8 (hball k)
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : ℕ → (E × E) → ℝ → E × E)
        (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
        (qInf : NNReal) (δInf : ℝ) (etaInf : NNReal)
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ 6 * (q : ℝ) < r ∧ 0 < δ ∧ η < 1 / 24 ∧
      (∀ k,
        (e k).source = Metric.ball (0 : E × E) q ∧
        (e k : E × E → E × E) = (fun z => (z.1, (Φ k z 1).1)) ∧
        e k 0 = 0 ∧
        Metric.closedBall (0 : E × E) δ ⊆ (e k).target ∧
        ContDiffOn ℝ ∞ (e k : E × E → E × E) (e k).source ∧
        ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) (e k).target ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          (cc k).pair (e k z) = diagExp (g k) (hEnorm k) ((cc k).tangent z)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          z.1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).2 ∈ Metric.ball (0 : E) (cc k).radius) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ k z 0 = z) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          IsIntegralCurveOn (Φ k z) (fun _ => MetricKoszul.metricSpray ((cc k).metric (g k)))
            (Icc 0 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (0 : ℝ) 1,
          (Φ k z t).1 ∈ Metric.ball (0 : E) r) ∧
        ApproximatesLinearOn ((e k).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))
          (e k).target η) ∧
      0 < qInf ∧ qInf < q ∧ 0 < δInf ∧ etaInf < 1 / 24 ∧
      eInf.source = Metric.ball (0 : E × E) qInf ∧
      Metric.closedBall (0 : E × E) δInf ⊆ eInf.target ∧
      ContDiffOn ℝ ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) eInf.target ∧
      (∀ x ∈ Metric.ball (0 : E) qInf,
        (x, x) ∈ eInf.target ∧ eInf.symm (x, x) = (x, 0)) ∧
      ApproximatesLinearOn (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) eInf.target etaInf ∧
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun k => (e k : E × E → E × E)) eInf ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < min δ δInf ∧
        eInf.symm '' Metric.closedBall (0 : E × E) ε ⊆ Metric.ball 0 qInf ∧
        (∀ᶠ k in Filter.atTop, MapsTo (e k).symm (Metric.closedBall 0 ε) (Metric.ball 0 qInf)) ∧
        MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) ε)
          (fun k => ((e k).symm : E × E → E × E)) eInf.symm := by
  intro hr8 hball cc
  have hccconv := NormalBallChart.metric_recenter_convergence g c a hr8 hball hchart
    htranslate hB hconv
  have hccequiv := NormalBallChart.metricEquivOn_recenter g c a hr8 hball htranslate hell
  have hmap : MapsTo (fun z : E => a + z) (Metric.ball (0 : E) (8 * r))
      (Metric.ball (0 : E) R) := by
    intro z hz
    apply htranslate
    simpa only [Metric.mem_ball, dist_zero_right, dist_add_left, dist_self_add_left] using hz
  have hBC : ContDiffOn ℝ ∞ (fun z => B (a + z)) (Metric.ball (0 : E) (8 * r)) :=
    hB.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  exact exists_chart_diagonal_inverse_convergence_of_metric_convergence g hEnorm cc
    hr (by linarith : r < 8 * r) (fun _ => le_rfl) hccequiv
    (fun k => Metric.ball_subset_ball (by change r ≤ (8 * r) / 4; linarith)) hBC
    (fun z hz => hBsymm (a + z) (hmap hz))
    (fun z hz => hBell (a + z) (hmap hz)) hccconv

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem exists_recentered_diagonal_inverse_convergence_of_metric_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))
    (a : E) {r R : ℝ} (hr : 0 < r)
    (hchart : ∀ k, R ≤ (c k).radius)
    (htranslate : Metric.ball a (8 * r) ⊆ Metric.ball (0 : E) R)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) R))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R))
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) R)
      (fun k => (c k).metric (g k)) B) :
    let hr8 : 0 < 8 * r := by positivity
    let hball : ∀ k, Metric.ball a (8 * r) ⊆ Metric.ball (0 : E) (c k).radius :=
      fun k => htranslate.trans (Metric.ball_subset_ball (hchart k))
    let cc := fun k => (c k).recenter a hr8 (hball k)
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : ℕ → (E × E) → ℝ → E × E)
        (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
        (qInf : NNReal) (δInf : ℝ) (etaInf : NNReal)
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ 6 * (q : ℝ) < r ∧ 0 < δ ∧ η < 1 / 24 ∧
      (∀ k,
        (e k).source = Metric.ball (0 : E × E) q ∧
        (e k : E × E → E × E) = (fun z => (z.1, (Φ k z 1).1)) ∧
        e k 0 = 0 ∧
        Metric.closedBall (0 : E × E) δ ⊆ (e k).target ∧
        ContDiffOn ℝ ∞ (e k : E × E → E × E) (e k).source ∧
        ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) (e k).target ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          (cc k).pair (e k z) = diagExp (g k) (hEnorm k) ((cc k).tangent z)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          z.1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).2 ∈ Metric.ball (0 : E) (cc k).radius) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ k z 0 = z) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          IsIntegralCurveOn (Φ k z) (fun _ => MetricKoszul.metricSpray ((cc k).metric (g k)))
            (Icc 0 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (0 : ℝ) 1,
          (Φ k z t).1 ∈ Metric.ball (0 : E) r) ∧
        ApproximatesLinearOn ((e k).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))
          (e k).target η) ∧
      0 < qInf ∧ qInf < q ∧ 0 < δInf ∧ etaInf < 1 / 24 ∧
      eInf.source = Metric.ball (0 : E × E) qInf ∧
      Metric.closedBall (0 : E × E) δInf ⊆ eInf.target ∧
      ContDiffOn ℝ ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) eInf.target ∧
      (∀ x ∈ Metric.ball (0 : E) qInf,
        (x, x) ∈ eInf.target ∧ eInf.symm (x, x) = (x, 0)) ∧
      ApproximatesLinearOn (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) eInf.target etaInf ∧
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun k => (e k : E × E → E × E)) eInf ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < min δ δInf ∧
        eInf.symm '' Metric.closedBall (0 : E × E) ε ⊆ Metric.ball 0 qInf ∧
        (∀ᶠ k in Filter.atTop, MapsTo (e k).symm (Metric.closedBall 0 ε) (Metric.ball 0 qInf)) ∧
        MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) ε)
          (fun k => ((e k).symm : E × E → E × E)) eInf.symm := by
  obtain ⟨hBsymm, hBell⟩ := NormalBallChart.metric_limit_symmetric_and_bounds g c hell hconv
  exact exists_recentered_chart_diagonal_inverse_convergence g hEnorm c a hr hchart htranslate
    hell hB hBsymm hBell hconv

end DifferentialGeometry.CheegerGromovCompactness

end
