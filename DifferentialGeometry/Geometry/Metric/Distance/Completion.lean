import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Metric.Distance.PathLength
import DifferentialGeometry.Topology.MetricSpace.GeodesicCompactness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_sphere_point_near_completion_point
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (q : UniformSpace.Completion M) (x : M) {rho : ℝ} (hrho : 0 ≤ rho)
    (hr : rho < dist (x : UniformSpace.Completion M) q) :
    ∃ y : M, dist x y = rho ∧ dist (y : UniformSpace.Completion M) q <
      2 * (dist (x : UniformSpace.Completion M) q - rho) := by
  have hdist (u v : M) : riemannianEDistOf g u v = ENNReal.ofReal (dist u v) :=
    (hmetric u v).symm.trans (edist_dist u v)
  let r := dist (x : UniformSpace.Completion M) q
  change rho < r at hr
  let s : ℝ := (r - rho) / 4
  have hs : 0 < s := div_pos (sub_pos.mpr hr) (by norm_num)
  have hsgap : 3 * s < r - rho := by dsimp only [s]; linarith only [hr]
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := M)).exists_dist_lt q hs
  have hzq : dist (z : UniformSpace.Completion M) q < s := by simpa only [dist_comm] using hz
  have hupper : dist x z ≤ r + s := by
    have h := dist_triangle (x : UniformSpace.Completion M) q (z : UniformSpace.Completion M)
    rw [UniformSpace.Completion.dist_eq, dist_comm q] at h
    change dist x z ≤ r + dist (z : UniformSpace.Completion M) q at h
    linarith only [h, hzq]
  have hcross : rho < dist x z := by
    have h := dist_triangle (x : UniformSpace.Completion M) (z : UniformSpace.Completion M) q
    rw [UniformSpace.Completion.dist_eq] at h
    change r ≤ dist x z + dist (z : UniformSpace.Completion M) q at h
    linarith only [h, hzq, hsgap, hs]
  have hedist : riemannianEDistOf g x z < ENNReal.ofReal (r + 2 * s) := by
    rw [hdist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hrho, hr, hs])).mpr
      (by linarith only [hupper, hs])
  obtain ⟨gamma, hstart, hend, hsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hedist
  have hc : ContinuousOn (fun t => dist x (gamma t)) (Icc (0 : ℝ) 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hsmooth.continuousOn
  obtain ⟨t, ht, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
    (show rho ∈ Icc (dist x (gamma 0)) (dist x (gamma 1)) by
      simpa only [hstart, hend, dist_self, mem_Icc] using And.intro hrho hcross.le)
  change dist x (gamma t) = rho at hxt
  have hleft : ENNReal.ofReal rho ≤ metricPathELength g gamma 0 t := by
    have h := edistOf_le_metricPathELength g ht.1
      (hsmooth.mono (Icc_subset_Icc le_rfl ht.2))
    rw [hstart, hdist, hxt] at h
    exact h
  have hright : ENNReal.ofReal (dist (gamma t) z) ≤ metricPathELength g gamma t 1 := by
    have h := edistOf_le_metricPathELength g ht.2
      (hsmooth.mono (Icc_subset_Icc ht.1 le_rfl))
    rw [hend, hdist] at h
    exact h
  have hadd : metricPathELength g gamma 0 t + metricPathELength g gamma t 1 =
      metricPathELength g gamma 0 1 := by
    let _ : RiemannianBundle (fun u : M => TangentSpace I u) := ⟨g.toRiemannianMetric⟩
    exact Manifold.pathELength_add (I := I) (γ := gamma) ht.1 ht.2
  have hshort := ((add_le_add hleft hright).trans_eq hadd).trans_lt hlength
  rw [← ENNReal.ofReal_add hrho dist_nonneg] at hshort
  have hreal : rho + dist (gamma t) z < r + 2 * s :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hrho, hr, hs])).mp hshort
  refine ⟨gamma t, hxt, ?_⟩
  have h := dist_triangle (gamma t : UniformSpace.Completion M) (z : UniformSpace.Completion M) q
  rw [UniformSpace.Completion.dist_eq] at h
  change dist (gamma t : UniformSpace.Completion M) q < 2 * (r - rho)
  linarith only [h, hzq, hreal, hsgap]

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M]

theorem exists_completion_segment_of_punctured_compact_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {q : UniformSpace.Completion M} {R : ℝ}
    (hcompact : IsCompact (Metric.closedBall q R))
    (hcover : Metric.closedBall q R ⊆ insert q (range (fun x : M => (x : UniformSpace.Completion M))))
    (x : M) (hx : dist (x : UniformSpace.Completion M) q < R / 2) :
    ∃ f : C(Icc (0 : ℝ) 1, UniformSpace.Completion M),
      f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = q ∧
      (∀ s, f s ∈ Metric.closedBall q R) ∧
      ∀ s t, dist (f s) (f t) = dist (x : UniformSpace.Completion M) q * dist s t := by
  classical
  by_cases hz : dist (x : UniformSpace.Completion M) q = 0
  · have heq : (x : UniformSpace.Completion M) = q := dist_eq_zero.mp hz
    refine ⟨ContinuousMap.const _ q, heq.symm, rfl, ?_, ?_⟩
    · intro s
      change dist q q ≤ R
      rw [dist_self]
      linarith only [hx, hz]
    · intro s t
      change dist q q = dist (x : UniformSpace.Completion M) q * dist s t
      rw [dist_self, hz, zero_mul]
  let r : ℝ := dist (x : UniformSpace.Completion M) q
  have hr : 0 < r := lt_of_le_of_ne dist_nonneg (Ne.symm hz)
  let rho (n : ℕ) : ℝ := r * (n : ℝ) / ((n : ℝ) + 1)
  have hrho (n : ℕ) : 0 ≤ rho n := by positivity
  have hrhol (n : ℕ) : rho n < r := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hrhot : Tendsto rho atTop (𝓝 r) := by
    simpa only [rho, mul_div_assoc, mul_one] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul r
  have hspheres (n : ℕ) : ∃ y : M, dist x y = rho n ∧
      dist (y : UniformSpace.Completion M) q < 2 * (r - rho n) :=
    exists_sphere_point_near_completion_point g hmetric q x (hrho n) (hrhol n)
  choose y hyDist hyEnd using hspheres
  have hcurves (n : ℕ) := exists_smooth_geodesic_minimizer_of_punctured_compact_ball
    g hmetric UniformSpace.Completion.coe_isometry hcompact hcover
    (p := x) (q := y n)
    (by rw [hyDist n]; exact (hrhol n).trans_le (le_add_of_nonneg_right dist_nonneg))
    (by rw [hyDist n]; have h := hrhol n; change r < R / 2 at hx; linarith only [hx, h])
  choose gamma hg0 hg1 hgSmooth hgMem hgLength hgSub hgGeo hgSpeed using hcurves
  let L : ℝ≥0 := ⟨r, hr.le⟩
  have hLip (n : ℕ) : LipschitzOnWith L (gamma n) (Icc (0 : ℝ) 1) := by
    apply lipschitzOnWith_of_subinterval_lengths (L := L) g hmetric
      ((hgSmooth n).of_le (by decide)).contMDiffOn (hrho n) (hrhol n).le
    intro a ha b hb
    simpa only [hyDist n] using hgSub n a ha b hb
  let c (n : ℕ) (s : ℝ) : UniformSpace.Completion M := gamma n s
  have hc (n : ℕ) : ContinuousOn (c n) (Icc (0 : ℝ) 1) :=
    ((UniformSpace.Completion.continuous_coe M).comp (hgSmooth n).continuous).continuousOn
  have hcLip (n : ℕ) : LipschitzOnWith L (c n) (Icc (0 : ℝ) 1) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro a ha b hb
    simpa only [c, UniformSpace.Completion.dist_eq] using
      (lipschitzOnWith_iff_dist_le_mul.mp (hLip n)) a ha b hb
  have hc0 : Tendsto (fun n => c n 0) atTop (𝓝 (x : UniformSpace.Completion M)) := by
    simpa only [c, hg0] using (tendsto_const_nhds (x := (x : UniformSpace.Completion M)))
  have hyT : Tendsto (fun n => (y n : UniformSpace.Completion M)) atTop (𝓝 q) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hgap : Tendsto (fun n => 2 * (r - rho n)) atTop (𝓝 (0 : ℝ)) := by
      simpa using ((tendsto_const_nhds (x := r)).sub hrhot).const_mul 2
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hyEnd n).le) hgap
  have hc1 : Tendsto (fun n => c n 1) atTop (𝓝 q) := by
    simpa only [c, hg1] using hyT
  obtain ⟨f, hf, hf0, hf1, hfK, hfDist⟩ :=
    Metric.exists_metric_segment_of_compact_lipschitz_curves hcompact
      (L := L) (p := (x : UniformSpace.Completion M)) (q := q) rfl
      c hc hgMem hcLip hc0 hc1
  exact ⟨⟨f, hf⟩, hf0, hf1, hfK, hfDist⟩

theorem exists_radial_segment_of_punctured_compact_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {q : UniformSpace.Completion M}
    {R : ℝ} (hcompact : IsCompact (Metric.closedBall q R))
    (hcover : Metric.closedBall q R ⊆ insert q (range (fun x : M => (x : UniformSpace.Completion M))))
    (x : M) (hx : dist (x : UniformSpace.Completion M) q < R / 2) :
    ∃ gamma : C(ℝ, UniformSpace.Completion M),
      gamma 0 = q ∧ gamma (dist (x : UniformSpace.Completion M) q) = x ∧
      ∀ s ∈ Icc 0 (dist (x : UniformSpace.Completion M) q),
        ∀ t ∈ Icc 0 (dist (x : UniformSpace.Completion M) q),
          dist (gamma s) (gamma t) = |s - t| := by
  obtain ⟨f, hf0, hf1, _, hf⟩ :=
    exists_completion_segment_of_punctured_compact_ball g hmetric hcompact hcover x hx
  let L := dist (x : UniformSpace.Completion M) q
  by_cases hz : L = 0
  · have heq : (x : UniformSpace.Completion M) = q := dist_eq_zero.mp hz
    refine ⟨ContinuousMap.const _ q, rfl, heq.symm, ?_⟩
    intro s hs t ht
    have hs0 : s = 0 := le_antisymm (hz ▸ hs.2) hs.1
    have ht0 : t = 0 := le_antisymm (hz ▸ ht.2) ht.1
    simp only [ContinuousMap.const_apply, dist_self, hs0, ht0, sub_self, abs_zero]
  have hL : 0 < L := lt_of_le_of_ne dist_nonneg (Ne.symm hz)
  let c : C(ℝ, Icc (0 : ℝ) 1) :=
    ⟨fun t => projIcc 0 1 zero_le_one (1 - t / L),
      continuous_projIcc.comp (continuous_const.sub (continuous_id.div_const L))⟩
  refine ⟨f.comp c, ?_, ?_, ?_⟩
  · simpa only [ContinuousMap.comp_apply, c, ContinuousMap.coe_mk, zero_div, sub_zero,
      projIcc_right] using hf1
  · change f (c L) = x
    simpa only [c, ContinuousMap.coe_mk, div_self hL.ne', sub_self,
      projIcc_left] using hf0
  · intro s hs t ht
    have hs' : 1 - s / L ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact sub_nonneg.mpr ((div_le_one hL).mpr hs.2)
      · exact sub_le_self _ (div_nonneg hs.1 hL.le)
    have ht' : 1 - t / L ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact sub_nonneg.mpr ((div_le_one hL).mpr ht.2)
      · exact sub_le_self _ (div_nonneg ht.1 hL.le)
    simp only [ContinuousMap.comp_apply, c, ContinuousMap.coe_mk, hf, Subtype.dist_eq,
      Real.dist_eq, projIcc_of_mem zero_le_one hs', projIcc_of_mem zero_le_one ht']
    change L * |(1 - s / L) - (1 - t / L)| = |s - t|
    rw [show (1 - s / L) - (1 - t / L) = (t - s) / L by ring,
      abs_div, abs_of_pos hL, mul_div_cancel₀ _ hL.ne', abs_sub_comm]


theorem exists_smooth_geodesic_minimizer_of_completion_point_avoidance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p q : M} (hp : dist (p : UniformSpace.Completion M) z < r / 3)
    (hq : dist (q : UniformSpace.Completion M) z < r / 3) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (gamma s : UniformSpace.Completion M) ∈ Metric.closedBall z r) ∧
      metricPathELength g gamma 0 1 = ENNReal.ofReal (dist p q) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        metricPathELength g gamma a b = ENNReal.ofReal (b - a) * ENNReal.ofReal (dist p q)) ∧
      Riemannian.Geodesic.IsGeodesicOn (I := I) g gamma (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
          (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = dist p q ^ 2 := by
  have hr : 0 < r := by linarith only [hp, dist_nonneg (x := (p : UniformSpace.Completion M)) (y := z)]
  have hpz : 0 < dist (p : UniformSpace.Completion M) z :=
    dist_pos.mpr (fun h => hz ⟨p, h⟩)
  have hqz : 0 < dist (q : UniformSpace.Completion M) z :=
    dist_pos.mpr (fun h => hz ⟨q, h⟩)
  obtain ⟨a, ha0, ha1, _, ha⟩ := exists_completion_segment_of_punctured_compact_ball
    g hmetric hcompact hcover p (by linarith only [hp, hr])
  obtain ⟨b, hb0, hb1, _, hb⟩ := exists_completion_segment_of_punctured_compact_ball
    g hmetric hcompact hcover q (by linarith only [hq, hr])
  have hgap := dist_lt_dist_add_dist_of_geodesic_avoidance hpz hqz
    a b ha0 ha1 hb0 hb1 ha hb havoid
  rw [UniformSpace.Completion.dist_eq, dist_comm z] at hgap
  have htri := dist_triangle (p : UniformSpace.Completion M) z (q : UniformSpace.Completion M)
  rw [UniformSpace.Completion.dist_eq, dist_comm z] at htri
  exact exists_smooth_geodesic_minimizer_of_punctured_compact_ball g hmetric
    UniformSpace.Completion.coe_isometry hcompact hcover hgap
    (by linarith only [hp, hq, htri])

end DifferentialGeometry.Geometry
