import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_face_of_affineMap_le_of_lt_other_vertices
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) {p x : E} {r : ℝ}
    (hother : ∀ v ∈ K.vertices, v ≠ p → r < a v) {s : Finset E} (hs : s ∈ K.faces)
    (hxs : x ∈ convexHull ℝ (s : Set E)) (hxr : a x ≤ r) : p ∈ s := by
  by_contra hp
  have hgt : r < a x := convexHull_min (fun v hv => hother v
    (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
    (fun h => hp (h ▸ hv))) ((convex_Ioi r).affine_preimage a) hxs
  exact hgt.not_ge hxr

theorem exists_radial_fiber_of_affineMap_le_of_lt_other_vertices
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) {p x : E} {r : ℝ}
    (hpr : a p < r) (hother : ∀ v ∈ K.vertices, v ≠ p → r < a v)
    (hx : x ∈ K.space) (hxr : a x ≤ r) :
    x = p ∨ ∃ z ∈ K.space ∩ {y | a y = r}, ∃ t : ℝ,
      0 < t ∧ t ≤ 1 ∧ x = p + t • (z - p) := by
  classical
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hp := mem_face_of_affineMap_le_of_lt_other_vertices K a hother hs hxs hxr
  rw [← Finset.insert_erase hp] at hxs
  rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase p s) hxs with
    hxp | ⟨z, hz, t, ht, -, hxt⟩
  · exact Or.inl hxp
  have hzr : r < a z := by
    apply convexHull_min _ ((convex_Ioi r).affine_preimage a) hz
    intro v hv
    exact hother v (K.down_closed hs (Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hv))
      (Finset.singleton_nonempty v)) (Finset.ne_of_mem_erase hv)
  have hden : 0 < a z - a p := sub_pos.mpr (hpr.trans hzr)
  let u := (r - a p) / (a z - a p)
  have hu : 0 < u := div_pos (sub_pos.mpr hpr) hden
  have hu1 : u ≤ 1 := (div_le_one hden).mpr (by linarith)
  have humul : u * (a z - a p) = r - a p := div_mul_cancel₀ _ hden.ne'
  have htu : t ≤ u := by
    rw [hxt, affineMap_apply_add_smul_sub] at hxr
    nlinarith
  let y := p + u • (z - p)
  have hyK : y ∈ K.space := by
    apply K.convexHull_subset_space hs
    rw [← Finset.insert_erase hp]
    exact mem_convexHull_insert_of_combo hz hu.le hu1
  have hyr : a y = r := by
    rw [show y = p + u • (z - p) from rfl, affineMap_apply_add_smul_sub, humul]
    ring
  refine Or.inr ⟨y, ⟨hyK, hyr⟩, t / u, div_pos ht hu, (div_le_one hu).mpr htu, ?_⟩
  rw [show y = p + u • (z - p) from rfl, add_sub_cancel_left, smul_smul,
    div_mul_cancel₀ _ hu.ne']
  exact hxt

open Classical in
theorem inter_le_eq_coneComplex_space_of_lt_other_vertices
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) {p : E} {r : ℝ}
    (hp : p ∈ K.vertices) (hpr : a p < r)
    (hother : ∀ v ∈ K.vertices, v ≠ p → r < a v)
    (L : Geometry.SimplicialComplex ℝ E) (hpL : IsConeBase p L)
    (hL : L.space = K.space ∩ {x | a x = r}) :
    K.space ∩ {x | a x ≤ r} = (coneComplex hpL).space := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hxr⟩
    rw [mem_coneComplex_space_iff, hL]
    exact exists_radial_fiber_of_affineMap_le_of_lt_other_vertices K a hpr hother hx hxr
  · intro x hx
    rcases (mem_coneComplex_space_iff hpL).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact ⟨K.subset_space hp (Finset.mem_singleton_self _), hpr.le⟩
    · have hz' := hL.subset hz
      obtain ⟨s, hs, hzs⟩ := K.mem_space_iff.mp hz'.1
      have hps := mem_face_of_affineMap_le_of_lt_other_vertices K a hother hs hzs hz'.2.le
      have hxK : p + t • (z - p) ∈ K.space := by
        apply K.convexHull_subset_space hs
        rw [add_smul_sub_eq_combo]
        exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ hps) hzs
          (sub_nonneg.mpr ht1) ht.le (by ring)
      refine ⟨hxK, ?_⟩
      change a (p + t • (z - p)) ≤ r
      rw [affineMap_apply_add_smul_sub, hz'.2]
      nlinarith

end DifferentialGeometry.Topology.PiecewiseLinear
