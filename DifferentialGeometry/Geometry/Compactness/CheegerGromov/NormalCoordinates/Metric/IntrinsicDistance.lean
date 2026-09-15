import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.IntrinsicLipschitz
import DifferentialGeometry.Topology.UniformConvergence
import Mathlib.Topology.MetricSpace.Thickening
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic

noncomputable section
open Set Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem IntrinsicBallChart.lipschitzOnWith_of_metric_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {R s : ℝ} (c : IntrinsicBallChart (I := I) g hEnorm p R)
    (hsR : s < R) {C : ℝ≥0}
    (hmetric : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ (C : ℝ) ^ 2 * ‖v‖ ^ 2) :
    LipschitzOnWith C c.hom (Metric.closedBall (0 : E) s) := by
  have hsub : Metric.closedBall (0 : E) s ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hsR
  have hexp := lipschitzOnWith_intrinsicFramedExp_of_metric_bound g hEnorm p
    (r := s) (C := C) (fun z hz v => by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨mul_nonneg C.coe_nonneg (norm_nonneg v), ?_⟩
      simpa only [mul_pow] using hmetric z (hsub hz) v)
  intro x hx y hy
  rw [c.hom_eq (hsub hx), c.hom_eq (hsub hy)]
  exact hexp hx hy

theorem IntrinsicBallChart.riemannianEDist_lt_of_dist_lt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {R s r : ℝ} (c : IntrinsicBallChart (I := I) g hEnorm p R)
    (hsR : s < R) {C : ℝ≥0}
    (hmetric : ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ (C : ℝ) ^ 2 * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ Metric.closedBall 0 s) (hy : y ∈ Metric.closedBall 0 s)
    (hxy : (C : ℝ) * dist x y < r) :
    riemannianEDist I (c.hom x) (c.hom y) < ENNReal.ofReal r := by
  have hh := c.lipschitzOnWith_of_metric_bound g hEnorm p hsR hmetric hx hy
  rw [← IsRiemannianManifold.out (I := I)]
  apply hh.trans_lt
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt
    (mul_nonneg C.coe_nonneg dist_nonneg) hxy) |>.mpr hxy

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

noncomputable section
open Bundle Set Filter Manifold
open scoped ContDiff Manifold Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E P H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace P] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.eventually_riemannianEDist_lt_of_tendstoUniformlyOn
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (M := M k) (g k))
    (p : ∀ k, M k) {R s : ℝ}
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) R)
    (hsR : s < R) {C : ℝ≥0}
    (hmetric : ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ≤
        (C : ℝ) ^ 2 * ‖v‖ ^ 2)
    {ι : Type*} [Finite ι] {K : Set P}
    {Phi : ℕ → P → E} {xi : ℕ → P → ι → E} {center : P → E}
    (hPhi : TendstoUniformlyOn Phi center atTop K)
    (hxi : ∀ i, TendstoUniformlyOn (fun k z => xi k z i) center atTop K)
    (hK : IsCompact K) (hcenter : ContinuousOn center K)
    (hmap : MapsTo center K (Metric.ball 0 s)) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, ∀ z ∈ K, ∀ i,
      riemannianEDist I ((c k).hom (Phi k z)) ((c k).hom (xi k z i)) <
        ENNReal.ofReal eps := by
  obtain ⟨delta, hdelta, hthick⟩ := (hK.image_of_continuousOn hcenter).exists_thickening_subset_open Metric.isOpen_ball (image_subset_iff.mpr hmap)
  let eta := min delta (eps / (2 * ((C : ℝ) + 1)))
  have hden : 0 < 2 * ((C : ℝ) + 1) := by positivity
  have heta : 0 < eta := lt_min hdelta (div_pos heps hden)
  have heta_delta : eta ≤ delta := min_le_left _ _
  have heta_eps : (2 * ((C : ℝ) + 1)) * eta ≤ eps := by
    have hh : eta * (2 * ((C : ℝ) + 1)) ≤ eps :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  have hxiall : ∀ᶠ k in atTop, ∀ i, ∀ z ∈ K, dist (center z) (xi k z i) < eta :=
    Filter.eventually_all.mpr fun i => (Metric.tendstoUniformlyOn_iff.mp (hxi i)) eta heta
  filter_upwards [hmetric, (Metric.tendstoUniformlyOn_iff.mp hPhi) eta heta, hxiall]
    with k hk hpk hxk z hz i
  have hPhiBall : Phi k z ∈ Metric.ball (0 : E) s := by
    apply hthick
    rw [Metric.mem_thickening_iff]
    exact ⟨center z, mem_image_of_mem center hz,
      by simpa only [dist_comm] using (hpk z hz).trans_le heta_delta⟩
  have hxiBall : xi k z i ∈ Metric.ball (0 : E) s := by
    apply hthick
    rw [Metric.mem_thickening_iff]
    exact ⟨center z, mem_image_of_mem center hz,
      by simpa only [dist_comm] using (hxk i z hz).trans_le heta_delta⟩
  apply (c k).riemannianEDist_lt_of_dist_lt (g k) (hEnorm k) (p k) hsR hk
    (Metric.ball_subset_closedBall hPhiBall) (Metric.ball_subset_closedBall hxiBall)
  have hdist : dist (Phi k z) (xi k z i) < eta + eta :=
    (dist_triangle (Phi k z) (center z) (xi k z i)).trans_lt
      (add_lt_add (by simpa only [dist_comm] using hpk z hz) (hxk i z hz))
  nlinarith [C.coe_nonneg, dist_nonneg (x := Phi k z) (y := xi k z i)]

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

noncomputable section
open Bundle Set Filter Manifold
open scoped ContDiff Manifold Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open DifferentialGeometry.CheegerGromovCompactness

variable {E P H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.eventually_riemannianEDist_lt_of_configuration_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (M := M k) (g k))
    (p : ∀ k, M k) {R s : ℝ}
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) R)
    (hsR : s < R) {C : ℝ≥0}
    (hmetric : ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) R, ∀ v : E,
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ≤
        (C : ℝ) ^ 2 * ‖v‖ ^ 2)
    {ι : Type*} [Fintype ι] {U K : Set P}
    {Phi : ℕ → P → E} {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
    {mu : P → ι → ℝ} {center : P → E}
    (hPhi : MapCInfConvergenceOnCompacts U Phi center)
    (hcfg : MapCInfConvergenceOnCompacts U configuration
      (fun z => (mu z, fun _ => center z)))
    (hK : IsCompact K) (hKU : K ⊆ U) (hcenter : ContinuousOn center K)
    (a : E) (hmap : MapsTo (fun z => a + center z) K (Metric.ball 0 s))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, ∀ z ∈ K, ∀ i,
      riemannianEDist I ((c k).hom (a + Phi k z))
        ((c k).hom (a + (configuration k z).2 i)) < ENNReal.ofReal eps := by
  have hPhiU : TendstoUniformlyOn (fun k z => a + Phi k z)
      (fun z => a + center z) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro delta hdelta
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_of_cPConvergence (hPhi K hK hKU 0))) delta hdelta]
      with k hk z hz
    simpa only [dist_add_left] using hk z hz
  have hxiU : ∀ i, TendstoUniformlyOn
      (fun k z => a + (configuration k z).2 i) (fun z => a + center z) atTop K := by
    intro i
    rw [Metric.tendstoUniformlyOn_iff]
    intro delta hdelta
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_of_cPConvergence (hcfg K hK hKU 0))) delta hdelta]
      with k hk z hz
    rw [dist_add_left]
    have hi : dist (center z) ((configuration k z).2 i) ≤
        dist (fun _ : ι => center z) (configuration k z).2 :=
      dist_le_pi_dist (fun _ : ι => center z) (configuration k z).2 i
    have hp : dist (fun _ : ι => center z) (configuration k z).2 ≤
        dist (mu z, fun _ : ι => center z) (configuration k z) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact (hi.trans hp).trans_lt (hk z hz)
  exact IntrinsicBallChart.eventually_riemannianEDist_lt_of_tendstoUniformlyOn
    g hEnorm p c hsR hmetric hPhiU hxiU hK (continuousOn_const.add hcenter) hmap heps

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
