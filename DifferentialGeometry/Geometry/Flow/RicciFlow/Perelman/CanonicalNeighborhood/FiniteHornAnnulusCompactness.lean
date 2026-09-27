import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_mem_range_of_mem_closure_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) {z : UniformSpace.Completion W}
    (hz : z ∈ closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i))
    (hne : z ≠ H.endpoint) : z ∈ range (fun x : W => (x : UniformSpace.Completion W)) := by
  have hd : 0 < dist z H.endpoint := dist_pos.mpr hne
  obtain ⟨j, hsmall⟩ := finiteHorn_subend_radial_small g H (half_pos hd)
  let K : Set W := H.tube.map '' (univ ×ˢ Icc (H.cut_height j) (H.cut_height i))
  have hK : IsCompact K := H.tube.isCompact_slab (H.cut_height_mem j).1 (H.cut_height_mem i).2
  have hKC : IsCompact ((fun x : W => (x : UniformSpace.Completion W)) '' K) :=
    hK.image (UniformSpace.Completion.continuous_coe W)
  have hcover : (fun x : W => (x : UniformSpace.Completion W)) '' H.subend i ⊆
      ((fun x : W => (x : UniformSpace.Completion W)) '' K) ∪
        Metric.closedBall H.endpoint (dist z H.endpoint / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxj : x ∈ H.subend j
    · exact Or.inr (hsmall x hxj).le
    · apply Or.inl
      refine ⟨x, ?_, rfl⟩
      have hxlow : H.cut_height j ≤ H.tube.height x := by
        apply le_of_not_gt
        intro hlt
        apply hxj
        rw [H.subend_eq j]
        exact hlt
      have hxhigh : H.tube.height x ≤ H.cut_height i := by
        rw [H.subend_eq i] at hx
        exact hx.le
      refine ⟨H.tube.map.symm x, ⟨mem_univ _, hxlow, hxhigh⟩, ?_⟩
      exact H.tube.map.right_inv' (by rw [H.tube.target_eq]; trivial)
  have hclosed := closure_minimal hcover (hKC.isClosed.union Metric.isClosed_closedBall)
  rcases hclosed hz with hzK | hzball
  · obtain ⟨x, _hx, hxeq⟩ := hzK
    exact ⟨x, hxeq⟩
  · change dist z H.endpoint ≤ dist z H.endpoint / 2 at hzball
    linarith

theorem finiteHorn_isCompact_radial_annulus (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) {a : ℝ} (ha : 0 < a) :
    IsCompact {x : W |
      (x : UniformSpace.Completion W) ∈
        closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend i) ∧
      a ≤ dist (x : UniformSpace.Completion W) H.endpoint} := by
  let A : Set (UniformSpace.Completion W) :=
    closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend i) ∩
      {z | a ≤ dist z H.endpoint}
  have hclosed : IsClosed {z : UniformSpace.Completion W | a ≤ dist z H.endpoint} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hA : IsCompact A := (finiteHorn_isCompact_closure_subend g H i).inter_right hclosed
  have hArange : A ⊆ range (fun x : W => (x : UniformSpace.Completion W)) := by
    intro z hz
    apply finiteHorn_mem_range_of_mem_closure_subend g H i hz.1
    intro heq
    have hlow : a ≤ dist z H.endpoint := hz.2
    rw [heq, dist_self] at hlow
    exact (not_le_of_gt ha) hlow
  change IsCompact ((fun x : W => (x : UniformSpace.Completion W)) ⁻¹' A)
  exact ((UniformSpace.Completion.isUniformInducing_coe W).isInducing.isCompact_preimage_iff
    hArange).mpr hA

theorem finiteHorn_exists_isCompact_closedBall_endpoint (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ r : ℝ, 0 < r ∧ IsCompact (Metric.closedBall H.endpoint r) := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨delta / 2, half_pos hdelta, ?_⟩
  apply (finiteHorn_isCompact_closure_subend g H 0).of_isClosed_subset Metric.isClosed_closedBall
  intro z hz
  change dist z H.endpoint ≤ delta / 2 at hz
  apply Metric.mem_closure_iff.mpr
  intro eta heta
  obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := W)).exists_dist_lt z
    (lt_min heta (half_pos hdelta))
  have hxd : dist (x : UniformSpace.Completion W) z < delta / 2 := by
    rw [dist_comm]
    exact hx.trans_le (min_le_right _ _)
  have hxend : dist (x : UniformSpace.Completion W) H.endpoint < delta := by
    have htri := dist_triangle (x : UniformSpace.Completion W) z H.endpoint
    linarith
  exact ⟨(x : UniformSpace.Completion W), ⟨x, hball x hxend, rfl⟩,
    hx.trans_le (min_le_left _ _)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
