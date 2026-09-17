import DifferentialGeometry.Topology.PiecewiseLinear.HeightProjection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_pos_ray_interval_subset {x d : E} {U : Set E}
    (hU : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc (-ε) ε, x + t • d ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ / 2, by positivity, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  simp only [sub_zero]
  exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem eventually_exists_eq_image_height_of_mem_ray_nhds
    {H : E → E} (hH : Continuous H) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ y, ℓ (H y) = ℓ y) {x p d : E}
    (hlevel : ℓ x = ℓ p) (hd : 0 < ℓ d) {U : Set E}
    (hU : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ y ∈ U, f (H y) = f (H p) := by
  obtain ⟨ε, hε, hinterval⟩ := exists_pos_ray_interval_subset hU
  have hleft : ℓ (H (x + (-ε) • d)) < ℓ (H p) := by
    rw [hheight, hheight, map_add, map_smul, smul_eq_mul, hlevel]
    nlinarith
  have hright : ℓ (H p) < ℓ (H (x + ε • d)) := by
    rw [hheight, hheight, map_add, map_smul, smul_eq_mul, hlevel]
    nlinarith
  have hleft' := (ContinuousLinearMap.apply ℝ ℝ (H (x + (-ε) • d))).continuous.continuousAt.eventually_lt
    (ContinuousLinearMap.apply ℝ ℝ (H p)).continuous.continuousAt hleft
  have hright' := (ContinuousLinearMap.apply ℝ ℝ (H p)).continuous.continuousAt.eventually_lt
    (ContinuousLinearMap.apply ℝ ℝ (H (x + ε • d))).continuous.continuousAt hright
  filter_upwards [hleft', hright'] with f hfleft hfright
  have hcont : Continuous (fun t : ℝ => f (H (x + t • d))) :=
    f.continuous.comp (hH.comp (continuous_const.add (continuous_id.smul continuous_const)))
  obtain ⟨t, ht, hft⟩ := isPreconnected_Icc.intermediate_value
    (show -ε ∈ Icc (-ε) ε from ⟨le_rfl, by linarith⟩)
    (show ε ∈ Icc (-ε) ε from ⟨by linarith, le_rfl⟩)
    hcont.continuousOn ⟨hfleft.le, hfright.le⟩
  exact ⟨x + t • d, hinterval t ht, hft⟩

theorem eventually_exists_lt_height_eq_image_height_of_mem_ray_nhds
    {H : E → E} (hH : Continuous H) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ y, ℓ (H y) = ℓ y) {x p d : E}
    (hlevel : ℓ x = ℓ p) (hd : 0 < ℓ d) {U : Set E}
    (hU : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ U) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f (H p) < f (H x) →
      ∃ y ∈ U, ℓ y < ℓ p ∧ f (H y) = f (H p) := by
  obtain ⟨ε, hε, hinterval⟩ := exists_pos_ray_interval_subset hU
  have hleft : ℓ (H (x + (-ε) • d)) < ℓ (H p) := by
    rw [hheight, hheight, map_add, map_smul, smul_eq_mul, hlevel]
    nlinarith
  have hleft' := (ContinuousLinearMap.apply ℝ ℝ (H (x + (-ε) • d))).continuous.continuousAt.eventually_lt
    (ContinuousLinearMap.apply ℝ ℝ (H p)).continuous.continuousAt hleft
  filter_upwards [hleft'] with f hfleft
  intro hfright
  have hcont : Continuous (fun t : ℝ => f (H (x + t • d))) :=
    f.continuous.comp (hH.comp (continuous_const.add (continuous_id.smul continuous_const)))
  obtain ⟨t, ht, hft⟩ := isPreconnected_Icc.intermediate_value
    (show -ε ∈ Icc (-ε) 0 from ⟨le_rfl, by linarith⟩)
    (show (0 : ℝ) ∈ Icc (-ε) 0 from ⟨by linarith, le_rfl⟩)
    hcont.continuousOn (show f (H p) ∈ Icc (f (H (x + (-ε) • d))) (f (H (x + 0 • d))) by
      refine ⟨hfleft.le, ?_⟩
      simpa only [zero_smul, add_zero] using hfright.le)
  have htneg : t < 0 := lt_of_le_of_ne ht.2 (by
    intro heq
    have hfx : f (H x) = f (H p) := by simpa only [heq, zero_smul, add_zero] using hft
    exact hfright.ne' hfx)
  refine ⟨x + t • d, hinterval t ⟨ht.1, ht.2.trans hε.le⟩, ?_, hft⟩
  rw [map_add, map_smul, smul_eq_mul, hlevel]
  nlinarith

theorem exists_pos_height_direction_of_mem_openSimplex
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) {s : Finset E}
    (hs : s ∈ K.faces) {x p : E} (hx : x ∈ openSimplex s) (hxp : x ≠ p)
    (hlevel : ℓ x = ℓ p) (hunique : ∀ v ∈ K.vertices, ℓ v = ℓ p → v = p) :
    ∃ d ∈ vectorSpan ℝ (s : Set E), 0 < ℓ d := by
  have hex : ∃ v ∈ s, ℓ v ≠ ℓ p := by
    by_contra! hz
    have hsub : (s : Set E) ⊆ {p} := by
      intro v hv
      exact hunique v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)) (hz v hv)
    exact hxp (convexHull_min hsub (convex_singleton p) (openSimplex_subset_convexHull _ hx))
  obtain ⟨v, hv, hvheight⟩ := hex
  have hdir : v - x ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [direction_affineSpan, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hv)
        (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hx))
  have hnonzero : ℓ (v - x) ≠ 0 := by
    rw [map_sub, hlevel]
    exact sub_ne_zero.mpr hvheight
  refine ⟨(ℓ (v - x))⁻¹ • (v - x), (vectorSpan ℝ (s : Set E)).smul_mem _ hdir, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hnonzero]
  exact zero_lt_one

end DifferentialGeometry.Topology.PiecewiseLinear
