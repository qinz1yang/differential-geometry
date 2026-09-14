import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem isConnected_roundSphereTwo :
    IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  apply isConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank]
  norm_num

omit [SigmaCompactSpace W] in
theorem isCompact_range_hornBarrierSphere {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g}
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (b : HornBarriers H ray d) (i : ℕ) :
    IsCompact (Set.range (b.sphere i)) := by
  have h : IsCompact (Set.image (b.sphere i) Set.univ) :=
    (Topology.IsEmbedding.isCompact_iff (b.embedding i)).mp isCompact_univ
  rwa [Set.image_univ] at h

omit [SigmaCompactSpace W] in
theorem isConnected_range_hornBarrierSphere {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {ray : EndRay H.endpoint} {d : ℕ → ℝ}
    (b : HornBarriers H ray d) (i : ℕ) : IsConnected (Set.range (b.sphere i)) := by
  let : ConnectedSpace (Sphere 2) := Subtype.connectedSpace isConnected_roundSphereTwo
  exact isConnected_range (b.embedding i).continuous

theorem hornBarrier_div_sqrt_lt_scale_of_diverges {d s : ℕ → ℝ} (hd : ∀ i, 0 < d i)
    (hlarge : Filter.Tendsto (fun i => s i * d i ^ 2) Filter.atTop Filter.atTop)
    {L delta : ℝ} (hL : 0 < L) (hdelta : 0 < delta) :
    ∀ᶠ i in Filter.atTop, L / Real.sqrt (s i) < delta * d i := by
  have hLd : 0 < L / delta := div_pos hL hdelta
  have hd2 : ∀ i, 0 < d i ^ 2 := fun i => pow_pos (hd i) 2
  filter_upwards [hlarge.eventually_gt_atTop ((L / delta) ^ 2),
    hlarge.eventually_ge_atTop 1] with i hsq hone
  have hs_pos : 0 < s i := by nlinarith [hone, hd2 i]
  have hlt : L / delta < Real.sqrt (s i * d i ^ 2) := by
    rw [Real.lt_sqrt hLd.le]
    exact hsq
  have hsqrt : Real.sqrt (s i * d i ^ 2) = Real.sqrt (s i) * d i := by
    rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq (hd i).le]
  rw [hsqrt] at hlt
  have hmain : L < delta * (Real.sqrt (s i) * d i) := by
    have h := mul_lt_mul_of_pos_left hlt hdelta
    have heq : delta * (L / delta) = L := by field_simp
    rwa [heq] at h
  have hsqrt_pos : 0 < Real.sqrt (s i) := Real.sqrt_pos.mpr hs_pos
  rw [div_lt_iff₀ hsqrt_pos]
  calc L < delta * (Real.sqrt (s i) * d i) := hmain
    _ = delta * d i * Real.sqrt (s i) := by ring

omit [SigmaCompactSpace W] in
def endDistance (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x : W) : ℝ :=
  dist (x : UniformSpace.Completion W) H.endpoint

omit [SigmaCompactSpace W] in
def hornScaleAnnulus (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (delta d : ℝ) :
    Set W :=
  {x : W | (1 - delta) * d < endDistance g H x ∧ endDistance g H x < (1 + delta) * d}

omit [SigmaCompactSpace W] in
theorem eventually_range_hornBarrierSphere_subset_annulus {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {ray : EndRay H.endpoint} {d : ℕ → ℝ} (b : HornBarriers H ray d)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ i in Filter.atTop, Set.range (b.sphere i) ⊆ hornScaleAnnulus g H delta (d i) := by
  obtain ⟨L, hL, hb⟩ := b.diameter_bound
  filter_upwards [hb, hornBarrier_div_sqrt_lt_scale_of_diverges
    (fun i => (hd i).1) hlarge hL hdelta] with i hi hsmall
  intro x hx
  have hcenter : dist (ray.point (d i)) x ≤
      L / Real.sqrt (metricScalarAt g (ray.point (d i))) := hi x hx
  have hle : dist (ray.point (d i)) x < delta * d i := lt_of_le_of_lt hcenter hsmall
  have hdpos : 0 < d i := (hd i).1
  have hrad : dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint = d i :=
    ray.radial (d i) (hd i)
  have hdist_px : dist (ray.point (d i) : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) = dist (ray.point (d i)) x :=
    UniformSpace.Completion.dist_eq _ _
  have hdist_xp : dist (x : UniformSpace.Completion W)
      (ray.point (d i) : UniformSpace.Completion W) = dist (ray.point (d i)) x := by
    rw [UniformSpace.Completion.dist_eq, dist_comm]
  constructor
  · rw [endDistance]
    have htri := dist_triangle (ray.point (d i) : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [hdist_px, hrad] at htri
    nlinarith [htri, hle]
  · rw [endDistance]
    have htri := dist_triangle (x : UniformSpace.Completion W)
      (ray.point (d i) : UniformSpace.Completion W) H.endpoint
    rw [hdist_xp, hrad] at htri
    linarith

omit [SigmaCompactSpace W] in
theorem eventually_hornBarrierSphere_separates_paths {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {ray : EndRay H.endpoint} {d : ℕ → ℝ} (b : HornBarriers H ray d)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta10 : delta < 1 / 10) :
    ∀ᶠ i in Filter.atTop, ∀ c : C(Set.Icc (0 : ℝ) 1, W),
      dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint < (1 - delta) * d i →
      (1 + delta) * d i < dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint →
      ∃ t, c t ∈ Set.range (b.sphere i) := by
  filter_upwards [b.radial_barrier delta hdelta hdelta10] with i hi
  intro c hc0 hc1
  refine hi c ?_ ?_
  · rw [div_lt_iff₀ (hd i).1]
    exact hc0
  · rw [lt_div_iff₀ (hd i).1]
    exact hc1

omit [SigmaCompactSpace W] in
theorem eventually_exists_compact_connected_hornBarrier_in_annulus
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {ray : EndRay H.endpoint}
    {d : ℕ → ℝ} (b : HornBarriers H ray d) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta10 : delta < 1 / 10) :
    ∀ᶠ i in Filter.atTop, ∃ K : Set W,
      IsCompact K ∧ IsConnected K ∧ K.Nonempty ∧
      K ⊆ hornScaleAnnulus g H delta (d i) ∧
      (∀ c : C(Set.Icc (0 : ℝ) 1, W),
        dist (c ⟨0, by simp⟩ : UniformSpace.Completion W) H.endpoint < (1 - delta) * d i →
        (1 + delta) * d i < dist (c ⟨1, by simp⟩ : UniformSpace.Completion W) H.endpoint →
        ∃ t, c t ∈ K) := by
  filter_upwards [eventually_range_hornBarrierSphere_subset_annulus b hd hlarge hdelta,
    eventually_hornBarrierSphere_separates_paths b hd hdelta hdelta10]
    with i hann hsep
  exact ⟨Set.range (b.sphere i), isCompact_range_hornBarrierSphere b i,
    isConnected_range_hornBarrierSphere b i,
    (isConnected_range_hornBarrierSphere b i).nonempty, hann, hsep⟩

theorem exists_compact_connected_nonempty_sphere_three :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K ∧ IsConnected K ∧ K.Nonempty := by
  have hconn : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_roundSphereTwo
  exact ⟨Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
    isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, hconn, hconn.nonempty⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
