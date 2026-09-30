import DifferentialGeometry.Geometry.Metric.IsometricGeodesicRepresentative

set_option autoImplicit false

open Set Metric

namespace Metric.GeodesicRepresentative

theorem exists_lift_shorten {X : Type*} [MetricSpace X] {U : Set X}
    (hU : IsOpen U) (p : U) (σ : GeodesicRepresentative (p : X)) :
    ∃ (r : ℝ) (hr : 0 < r) (hle : r ≤ σ.length),
      ∃ τ : GeodesicRepresentative p,
        τ.map (Subtype.val : U → X) isometry_subtype_coe = σ.shorten hr hle := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU p p.property
  let r : ℝ := min σ.length (R / 2)
  have hr : 0 < r := lt_min σ.length_pos (half_pos hR)
  have hle : r ≤ σ.length := min_le_left _ _
  have hmem (t : Icc (0 : ℝ) r) : σ.curve ⟨t, t.property.1, t.property.2.trans hle⟩ ∈ U := by
    apply hball
    rw [mem_ball, dist_comm, ← σ.path_of_mem ⟨t.property.1, t.property.2.trans hle⟩,
      σ.dist_base_path ⟨t.property.1, t.property.2.trans hle⟩]
    exact t.property.2.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hR))
  let τ : GeodesicRepresentative p :=
    { length := r
      length_pos := hr
      curve := fun t => ⟨σ.curve ⟨t, t.property.1, t.property.2.trans hle⟩, hmem t⟩
      isometry := by
        apply Isometry.of_dist_eq
        intro s t
        change dist (σ.curve _) (σ.curve _) = _
        rw [σ.isometry.dist_eq]
        rfl
      start := Subtype.ext σ.start }
  exact ⟨r, hr, hle, τ, rfl⟩

end Metric.GeodesicRepresentative
