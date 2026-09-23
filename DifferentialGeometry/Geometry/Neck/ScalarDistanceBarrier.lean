import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem SpatialNeck.edist_lower_of_scalar_gt
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {z x : M}
    (N : SpatialNeck g eps z)
    (hscalar : (1 + 4323 * eps) * metricScalarAt g z < metricScalarAt g x) :
    ENNReal.ofReal (Real.sqrt (1-eps) / Real.sqrt (metricScalarAt g z)) ≤
      riemannianEDistOf g z x := by
  by_contra hn
  have hx : x ∈ riemannianBallOf g z
      (Real.sqrt (1-eps) / Real.sqrt (metricScalarAt g z)) := lt_of_not_ge hn
  have hi : (1 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) N.eps_pos).mpr
    (by linarith [N.eps_small])
  have hcap := N.ball_subset_image_slab (by norm_num : (0 : ℝ) < 1) hi
  rw [one_mul] at hcap
  have hx' := hcap hx
  have hwindow : x ∈ N.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    apply image_mono _ hx'
    intro q hq
    exact ⟨hq.1,by constructor <;> linarith [hq.2.1,hq.2.2]⟩
  exact (not_lt_of_ge (N.scalar_bounds_on_image_window hwindow).2) hscalar

theorem edist_lower_of_scalar_gt_on_neck_centers
    {g : SmoothRiemannianMetric I3 M} {eps B : ℝ}
    (Z : Set M) (hneck : ∀ z ∈ Z, Nonempty (SpatialNeck g eps z))
    (hscalar : ∀ z ∈ Z, metricScalarAt g z ≤ B)
    (x : M) (hx : (1 + 4323 * eps) * B < metricScalarAt g x) :
    ∀ z ∈ Z, ENNReal.ofReal (Real.sqrt (1-eps)/Real.sqrt B) ≤ riemannianEDistOf g x z := by
  intro z hz
  obtain ⟨N⟩ := hneck z hz
  have hc : 0 ≤ 1 + 4323 * eps := by linarith [N.eps_pos]
  have hxs : (1 + 4323 * eps)*metricScalarAt g z < metricScalarAt g x :=
    (mul_le_mul_of_nonneg_left (hscalar z hz) hc).trans_lt hx
  have hb := N.edist_lower_of_scalar_gt hxs
  rw [riemannianEDistOf_comm] at hb
  exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    (Real.sqrt_pos.mpr N.Q_pos) (Real.sqrt_le_sqrt (hscalar z hz)))).trans hb

theorem eventually_scaled_ball_disjoint_neck_centers
    {A : ℕ → Type*} [∀ n, TopologicalSpace (A n)] [∀ n, ChartedSpace ThreeSpace (A n)]
    [∀ n, IsManifold I3 ∞ (A n)] [∀ n, T2Space (A n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (A n)) (x : ∀ n, A n)
    (Z : ∀ n, Set (A n)) {eps B : ℝ} (heps : eps < 1) (hB : 0 < B)
    (hneck : ∀ n z, z ∈ Z n → Nonempty (SpatialNeck (g n) eps z))
    (hscalar : ∀ n z, z ∈ Z n → metricScalarAt (g n) z ≤ B)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hQeq : ∀ n, Q n = metricScalarAt (g n) (x n))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop, Disjoint (riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (x n) R)
      (Z n) := by
  let c := Real.sqrt (1-eps)/Real.sqrt B
  have hc : 0 < c := div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hB)
  have hscaled : Tendsto (fun n => Real.sqrt (Q n) * c) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hQlim).atTop_mul_const hc
  filter_upwards [hQlim.eventually_gt_atTop ((1 + 4323 * eps) * B), hscaled.eventually_gt_atTop R]
    with n hn hr
  apply disjoint_left.mpr
  intro z hz hZ
  have hb := edist_lower_of_scalar_gt_on_neck_centers (Z n) (hneck n) (hscalar n)
    (x n) (by rwa [← hQeq n]) z hZ
  have hr0 : 0 < Real.sqrt (Q n) * c := mul_pos (Real.sqrt_pos.mpr (hQ n)) hc
  have hfar : ENNReal.ofReal R <
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (x n) z := by
    rw [edistOf_scale]
    calc ENNReal.ofReal R < ENNReal.ofReal (Real.sqrt (Q n)*c) :=
        (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hr
      _ = ENNReal.ofReal (Real.sqrt (Q n)) * ENNReal.ofReal c :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)
      _ ≤ ENNReal.ofReal (Real.sqrt (Q n)) * riemannianEDistOf (g n) (x n) z :=
        mul_le_mul' le_rfl hb
  exact (not_lt_of_ge hz) hfar

theorem eventually_scaled_ball_disjoint_spatial_neck_sphere
    {A : ℕ → Type*} [∀ n, TopologicalSpace (A n)] [∀ n, ChartedSpace ThreeSpace (A n)]
    [∀ n, IsManifold I3 ∞ (A n)] [∀ n, T2Space (A n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (A n)) (p x : ∀ n, A n)
    {eps B : ℝ} (heps : eps ≤ 1 / 156000) (hB : 0 < B)
    (neck : ∀ n, SpatialNeck (g n) eps (p n))
    (level : ℕ → ℝ) (hlevel : ∀ n, |level n| ≤ 4)
    (hbase : ∀ n, metricScalarAt (g n) (p n) ≤ B)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hQeq : ∀ n, Q n = metricScalarAt (g n) (x n))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop,
      Disjoint (riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (x n) R)
        (range fun q : Sphere 2 => (neck n).map (q, level n)) := by
  have hepspos : 0 < eps := (neck 0).eps_pos
  have halpha : 13000 * eps < 1 := by linarith
  have hB' : 0 < (1 + 4323 * eps) * B := by positivity
  apply eventually_scaled_ball_disjoint_neck_centers g x
    (fun n => range fun q : Sphere 2 => (neck n).map (q, level n)) halpha hB' _ _
    Q hQ hQeq hQlim R
  · intro n z hz
    obtain ⟨q,rfl⟩ := hz
    obtain ⟨_,N,_,_⟩ := (neck n).exists_at_coordinate_mul heps q (hlevel n)
    exact ⟨N⟩
  · intro n z hz
    obtain ⟨q,rfl⟩ := hz
    have hi : (4 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) hepspos).mpr (by linarith)
    have hsrc : (q,level n) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
      exact ⟨mem_univ _, abs_lt.mp ((hlevel n).trans_lt hi)⟩
    exact ((neck n).scalar_bounds_on_image_window ⟨(q,level n),hsrc,rfl⟩).2.trans
      (mul_le_mul_of_nonneg_left (hbase n) (by positivity))

theorem eventually_scaled_closedBall_subset_of_frontier_necks
    {A : ℕ → Type*} [∀ n, TopologicalSpace (A n)] [∀ n, ChartedSpace ThreeSpace (A n)]
    [∀ n, IsManifold I3 ∞ (A n)] [∀ n, T2Space (A n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (A n)) (x : ∀ n, A n)
    (U : ∀ n, Set (A n)) (hx : ∀ n, x n ∈ interior (U n))
    {eps B : ℝ} (heps : eps < 1) (hB : 0 < B)
    (hneck : ∀ n z, z ∈ frontier (U n) → Nonempty (SpatialNeck (g n) eps z))
    (hscalar : ∀ n z, z ∈ frontier (U n) → metricScalarAt (g n) z ≤ B)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hQeq : ∀ n, Q n = metricScalarAt (g n) (x n))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop,
      riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (x n) R ⊆ interior (U n) := by
  let R' := max R 0 + 1
  have hR' : 0 < R' := by dsimp only [R']; positivity
  have hRR : R < R' := by dsimp only [R']; linarith [le_max_left R 0]
  filter_upwards [eventually_scaled_ball_disjoint_neck_centers g x
    (fun n => frontier (U n)) heps hB hneck hscalar Q hQ hQeq hQlim R'] with n hn
  have hfront : ∀ z ∈ frontier (U n), ENNReal.ofReal R' ≤
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (g n)) (x n) z := by
    intro z hz
    exact le_of_not_gt fun hh => (disjoint_left.mp hn) (le_of_lt hh) hz
  have hb := Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (scaleMetric (Q n) (hQ n) (g n)) (hx n) hfront
  intro y hy
  exact hb (hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR').mpr hRR))

theorem eventually_scaled_closedBall_subset_of_spatial_neck_frontier
    {A : ℕ → Type*} [∀ n, TopologicalSpace (A n)] [∀ n, ChartedSpace ThreeSpace (A n)]
    [∀ n, IsManifold I3 ∞ (A n)] [∀ n, T2Space (A n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (A n)) (p x : ∀ n, A n)
    {eps B : ℝ} (heps : eps ≤ 1 / 156000) (hB : 0 < B)
    (neck : ∀ n, SpatialNeck (g n) eps (p n))
    (level : ℕ → ℝ) (hlevel : ∀ n, |level n| ≤ 4)
    (hbase : ∀ n, metricScalarAt (g n) (p n) ≤ B)
    (U : ∀ n, Set (A n)) (hx : ∀ n, x n ∈ interior (U n))
    (hfront : ∀ n, frontier (U n) = range fun q : Sphere 2 => (neck n).map (q, level n))
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (hQeq : ∀ n, Q n = metricScalarAt (g n) (x n))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ n in atTop,
      riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (x n) R ⊆ interior (U n) := by
  have hepspos : 0 < eps := (neck 0).eps_pos
  apply eventually_scaled_closedBall_subset_of_frontier_necks g x U hx
    (by linarith : 13000 * eps < 1) (by positivity : 0 < (1 + 4323 * eps) * B) _ _
    Q hQ hQeq hQlim R
  · intro n z hz
    rw [hfront n] at hz
    obtain ⟨q,rfl⟩ := hz
    obtain ⟨_,N,_,_⟩ := (neck n).exists_at_coordinate_mul heps q (hlevel n)
    exact ⟨N⟩
  · intro n z hz
    rw [hfront n] at hz
    obtain ⟨q,rfl⟩ := hz
    have hi : (4 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) hepspos).mpr (by linarith)
    have hsrc : (q,level n) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨mem_univ _,abs_lt.mp ((hlevel n).trans_lt hi)⟩
    exact ((neck n).scalar_bounds_on_image_window ⟨(q,level n),hsrc,rfl⟩).2.trans
      (mul_le_mul_of_nonneg_left (hbase n) (by positivity))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
