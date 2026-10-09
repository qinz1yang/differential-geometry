import DifferentialGeometry.Geometry.Metric.Approximation.ConeRadialExtensionBounds
import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

/-!
# LC25 on a complete Riemannian manifold

Blueprint 207A, LC25 (`lem:collapse-cone-outward-point`, A:20953). The metric lemma needs a
geodesic source. On a complete Riemannian manifold (metric distance = `g`-length distance,
`IsRiemannianManifold`), every pair of points is joined by a minimizing unit geodesic
(Hopf–Rinow, `exists_unit_intrinsic_vector_of_pos_distance`); reparametrized on `[0,1]` it is a
metric segment (`exists_riemannian_metric_segment`). This discharges the geodesic hypothesis of
the LC25 kernel.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [IsManifold I ∞ M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- On a Riemannian manifold the metric distance is the `g`-length distance. -/
theorem toReal_riemannianEDist_eq_dist (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- A geodesic of initial velocity `v` has displacement at most `|v| (t - s)` on `[s, t]`. -/
theorem dist_intrinsicGeodesic_le_mul (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    dist (intrinsicGeodesic g hEnorm p v s) (intrinsicGeodesic g hEnorm p v t) ≤
      Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm p v hst
  rw [← IsRiemannianManifold.out (I := I), edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hst))).mp h

/-- A complete Riemannian manifold is a geodesic space: every pair of points is joined by a
metric segment parametrized proportionally to arclength on `[0, 1]`. -/
theorem exists_riemannian_metric_segment (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (a b : M) :
    ∃ c : Icc (0 : ℝ) 1 → M, Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (c s) (c t) = dist a b * dist s t := by
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨fun _ => a, continuous_const, rfl, rfl, fun s t => by simp⟩
  have hd : 0 < dist a b := dist_pos.mpr hab
  obtain ⟨w, hw, hend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm a b
    (by rw [toReal_riemannianEDist_eq_dist]; exact hd)
  rw [toReal_riemannianEDist_eq_dist] at hend
  set d := dist a b with hd_def
  let γ := intrinsicGeodesic g hEnorm a w
  have hwn : Real.sqrt (g.inner a w w) = 1 := by rw [hw, Real.sqrt_one]
  have hγ0 : γ 0 = a := intrinsicGeodesic_zero g hEnorm a w
  have hγd : γ d = b := hend
  have hγle (s t : ℝ) (hst : s ≤ t) : dist (γ s) (γ t) ≤ t - s := by
    simpa only [hwn, one_mul] using dist_intrinsicGeodesic_le_mul g hEnorm a w hst
  have hseg (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ d) : dist (γ s) (γ t) = t - s := by
    refine le_antisymm (hγle s t hst) ?_
    have h1 := hγle 0 s hs
    have h2 := hγle t d ht
    rw [hγ0] at h1
    rw [hγd] at h2
    have htri := dist_triangle4 a (γ s) (γ t) b
    linarith
  have hcont : Continuous γ := (intrinsicGeodesic_contMDiff g hEnorm a w).continuous
  refine ⟨fun s => γ (d * s), hcont.comp (continuous_const.mul continuous_subtype_val), ?_, ?_, ?_⟩
  · simp only [mul_zero, hγ0]
  · simp only [mul_one]
    exact hγd
  · intro s t
    rw [Subtype.dist_eq, Real.dist_eq]
    rcases le_total (s : ℝ) t with hst | hts
    · rw [hseg _ _ (mul_nonneg hd.le s.2.1) (mul_le_mul_of_nonneg_left hst hd.le)
        (mul_le_of_le_one_right hd.le t.2.2), abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    · rw [dist_comm, hseg _ _ (mul_nonneg hd.le t.2.1) (mul_le_mul_of_nonneg_left hts hd.le)
        (mul_le_of_le_one_right hd.le s.2.2), abs_of_nonneg (sub_nonneg.mpr hts)]
      ring

/-- LC25 on a complete Riemannian manifold: an actual pointed Kleiner–Lott `δ`-map from
`(M, p)` to an AC82 cone, with `0 < a ≤ b`, `δ < min {a/10, 1/(4b+20)}` and `15 δ < μ a`, gives
for every `q` with `a ≤ d(p,q) ≤ b` an outward point `q'` with `d(p,q') = 2 d(p,q)`,
`d(p,q) ≤ d(q,q') < d(p,q) + 15 δ` and `d(q,q') < (1 + μ) d(p,q)`. -/
theorem exists_riemannian_outward_point (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o) {a b μ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδa : δ < a / 10) (hδb : δ < 1 / (4 * b + 20)) (hμ : 15 * δ < μ * a) {q : M}
    (hq : a ≤ dist p q ∧ dist p q ≤ b) :
    ∃ q', dist p q' = 2 * dist p q ∧ dist p q ≤ dist q q' ∧
      dist q q' < dist p q + 15 * δ ∧ dist q q' < (1 + μ) * dist p q :=
  φ.exists_outward_point_on_annulus_lt_mul H (exists_riemannian_metric_segment g hEnorm) ha hab
    hδa hδb hμ hq

end DifferentialGeometry.Geometry.Collapse
