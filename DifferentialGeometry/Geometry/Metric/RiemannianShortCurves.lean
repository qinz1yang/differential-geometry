import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimizing_unitInterval_curve
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (x y : M) :
    ∃ c : unitInterval → M, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ = ENNReal.ofReal (dist x y) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have : IsRiemannianManifold I M := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  have hdist (a b : M) : riemannianEDist I a b = ENNReal.ofReal (dist a b) := by
    rw [← IsRiemannianManifold.out, edist_dist]
  obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
    g hEnorm x y (by rw [hdist]; exact ENNReal.ofReal_ne_top)
  rw [hdist, ENNReal.toReal_ofReal dist_nonneg] at hlen
  let γ := intrinsicGeodesic g hEnorm x v
  have hupper (s t : ℝ) (hst : s ≤ t) : dist (γ s) (γ t) ≤ dist x y * (t - s) := by
    have h := intrinsicGeodesic_riemannianEDist_le g hEnorm x v hst
    rw [hdist, hlen, ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg dist_nonneg (sub_nonneg.mpr hst))] at h
    exact h
  let c : unitInterval → M := fun t => γ t
  have hc0 : c 0 = x := intrinsicGeodesic_zero g hEnorm x v
  have hc1 : c 1 = y := hv
  have hLip : LipschitzWith (nndist x y) c := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change dist (γ s) (γ t) ≤ dist x y * dist s t
    rw [Subtype.dist_eq, Real.dist_eq]
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      exact hupper s t hst
    · rw [dist_comm (γ s) (γ t), abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hupper t s hts
  refine ⟨c, hLip.continuous, hc0, hc1, le_antisymm ?_ ?_⟩
  · rw [← coe_nndist x y, ENNReal.ofReal_coe_nnreal]
    exact hLip.eVariationOn_unitInterval_le
  · have h := eVariationOn.edist_le c (mem_univ (0 : unitInterval)) (mem_univ 1)
    simpa only [hc0, hc1, edist_dist] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_arbitrarily_short_riemannian_curve
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (x y : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : unitInterval → M, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) := by
  obtain ⟨c, hc, h0, h1, hlength⟩ := exists_minimizing_unitInterval_curve g hmetric x y
  refine ⟨c, hc, h0, h1, ?_⟩
  rw [hlength]
  exact ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos dist_nonneg hε) |>.mpr
    (by linarith)

end DifferentialGeometry.Geometry.Metric
