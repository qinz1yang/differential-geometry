import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornTwoScale
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

theorem rescaled_distance_eq_radial_scale_mul
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) (x y : W) :
    metricDistance (scaleMetric Q hQ g) x y =
      Real.sqrt (Q * r ^ 2) * (dist x y / r) := by
  rw [metricDistance, edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg Q)]
  change Real.sqrt Q * metricDistance g x y = _
  rw [← H.intrinsic, Real.sqrt_mul hQ.le, Real.sqrt_sq hr.le]
  field_simp

theorem rescaled_distance_to_ray_le_of_radial_le
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    {Q r b : ℝ} (hQ : 0 < Q) (hr : r ∈ Ioc 0 ray.length) (w : W)
    (hw : dist (w : UniformSpace.Completion W) H.endpoint / r ≤ b) :
    metricDistance (scaleMetric Q hQ g) (ray.point r) w ≤
      (1 + b) * Real.sqrt (Q * r ^ 2) := by
  have hrad : dist (w : UniformSpace.Completion W) H.endpoint ≤ b * r :=
    (div_le_iff₀ hr.1).mp hw
  have ht := dist_triangle (ray.point r : UniformSpace.Completion W) H.endpoint
    (w : UniformSpace.Completion W)
  rw [UniformSpace.Completion.dist_eq, ray.radial r hr,
    dist_comm H.endpoint (w : UniformSpace.Completion W)] at ht
  have hbound : dist (ray.point r) w / r ≤ 1 + b := by
    rw [div_le_iff₀ hr.1]
    nlinarith
  rw [rescaled_distance_eq_radial_scale_mul H hQ hr.1]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (Q * r ^ 2))

theorem radial_ratio_sub_one_le_rescaled_distance
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    {Q r : ℝ} (hQ : 0 < Q) (hr : r ∈ Ioc 0 ray.length) (w : W) :
    |dist (w : UniformSpace.Completion W) H.endpoint / r - 1| ≤
      metricDistance (scaleMetric Q hQ g) (ray.point r) w / Real.sqrt (Q * r ^ 2) := by
  have hroot : 0 < Real.sqrt (Q * r ^ 2) := Real.sqrt_pos.mpr (mul_pos hQ (sq_pos_of_pos hr.1))
  have ht := abs_dist_sub_le (w : UniformSpace.Completion W)
    (ray.point r : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq, ray.radial r hr, dist_comm w (ray.point r)] at ht
  rw [rescaled_distance_eq_radial_scale_mul H hQ hr.1,
    mul_div_cancel_left₀ _ hroot.ne']
  rw [show dist (w : UniformSpace.Completion W) H.endpoint / r - 1 =
    (dist (w : UniformSpace.Completion W) H.endpoint - r) / r by
      field_simp [hr.1.ne'],
    abs_div, abs_of_pos hr.1]
  exact div_le_div_of_nonneg_right ht hr.1.le

theorem radial_ratio_mem_Ioo_of_rescaled_distance_lt
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    {Q r c η : ℝ} (hQ : 0 < Q) (hr : r ∈ Ioc 0 ray.length)
    (hη : 0 < η) (hlower : c ≤ Q * r ^ 2) (w : W)
    (hw : metricDistance (scaleMetric Q hQ g) (ray.point r) w < η * Real.sqrt c) :
    dist (w : UniformSpace.Completion W) H.endpoint / r ∈ Ioo (1 - η) (1 + η) := by
  have hroot : 0 < Real.sqrt (Q * r ^ 2) := Real.sqrt_pos.mpr (mul_pos hQ (sq_pos_of_pos hr.1))
  have hsmall : metricDistance (scaleMetric Q hQ g) (ray.point r) w /
      Real.sqrt (Q * r ^ 2) < η := by
    rw [div_lt_iff₀ hroot]
    exact hw.trans_le (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlower) hη.le)
  have h := (radial_ratio_sub_one_le_rescaled_distance H ray hQ hr w).trans_lt hsmall
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  exact ⟨by linarith, by linarith⟩

theorem AnnularConvergence.eventually_rescaled_relation_distance_le
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (C : AnnularConvergence H angles ray d)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hupper : ∀ᶠ i in atTop, metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ B) :
    ∀ᶠ i in atTop, ∀ x w, (x, w) ∈ C.relation a b i →
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) w ≤ (1 + b) * Real.sqrt B := by
  have hb : 0 ≤ 1 + b := by linarith
  filter_upwards [C.annuli a b ha hab, hupper] with i hi hBi
  intro x w hxw
  exact (rescaled_distance_to_ray_le_of_radial_le H ray (hQ i) (hd i) w
    ((hi.2.1 x w hxw).2.2)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBi) hb)

theorem AnnularConvergence.eventually_rescaled_relation_distortion
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (C : AnnularConvergence H angles ray d)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hupper : ∀ᶠ i in atTop, metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ B) :
    ∀ᶠ i in atTop, ∀ hQ : 0 < metricScalarAt g (ray.point (d i)),
      ∀ x w y z, (x, w) ∈ C.relation a b i → (y, z) ∈ C.relation a b i →
      |Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) * openConeDistance x y -
        metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) hQ g) w z| <
          Real.sqrt B * C.error a b i := by
  filter_upwards [C.annuli a b ha hab, hupper] with i hi hBi
  intro hQ x w y z hxw hyz
  have hroot : 0 < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) :=
    Real.sqrt_pos.mpr (mul_pos hQ (sq_pos_of_pos (hd i).1))
  rw [rescaled_distance_eq_radial_scale_mul H hQ (hd i).1, ← mul_sub,
    abs_mul, abs_of_pos hroot]
  exact (mul_lt_mul_of_pos_left (hi.2.2.2.2.1 x w y z hxw hyz) hroot).trans_le
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hBi) (C.error_pos a b i).le)

theorem AnnularConvergence.exists_rescaled_annular_capture_bounds
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (C : AnnularConvergence H angles ray d)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length) (hzero : Tendsto d atTop (𝓝 0))
    (hupper : ∀ᶠ i in atTop, metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop,
      ∃ hQ : 0 < metricScalarAt g (ray.point (d i)),
        (∀ x w, (x, w) ∈ C.relation a b i →
          metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) hQ g)
            (ray.point (d i)) w ≤ (1 + b) * Real.sqrt B) ∧
        (∀ η : ℝ, 0 < η → ∀ w : W,
          metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) hQ g)
            (ray.point (d i)) w < η * Real.sqrt c →
          dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Ioo (1 - η) (1 + η)) ∧
        (∀ x, x.1 ∈ Icc a b → ∃ y w, (y, w) ∈ C.relation a b i ∧
          openConeDistance x y < C.error a b i ∧
          metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) hQ g)
            (ray.point (d i)) w ≤ (1 + b) * Real.sqrt B) := by
  obtain ⟨c, hc, hlower⟩ := finite_horn_two_scale_lower_bound H ray d hd hzero
  refine ⟨c, hc, ?_⟩
  filter_upwards [C.annuli a b ha hab, hlower, hupper] with i hi hci hBi
  have hQ : 0 < metricScalarAt g (ray.point (d i)) :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos (hd i).1)).mp (hc.trans_le hci)
  have hbound : ∀ x w, (x, w) ∈ C.relation a b i →
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) hQ g)
        (ray.point (d i)) w ≤ (1 + b) * Real.sqrt B := by
    intro x w hxw
    exact (rescaled_distance_to_ray_le_of_radial_le H ray hQ (hd i) w
      ((hi.2.1 x w hxw).2.2)).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBi) (by linarith))
  refine ⟨hQ, hbound, ?_, ?_⟩
  · intro η hη w hw
    exact radial_ratio_mem_Ioo_of_rescaled_distance_lt H ray hQ (hd i) hη hci w hw
  · intro x hx
    obtain ⟨y, w, hyw, hnear⟩ := hi.2.2.1 x hx
    exact ⟨y, w, hyw, hnear, hbound y w hyw⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
