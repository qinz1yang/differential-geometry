import DifferentialGeometry.Geometry.Metric.CloudCoverBindings
import DifferentialGeometry.Geometry.Metric.AffineCloudBindings
import DifferentialGeometry.Geometry.Metric.LargeCloudCoverBindings
import DifferentialGeometry.Geometry.Metric.LargeCloudNearestBindings
import DifferentialGeometry.Geometry.Metric.RetainedMarkerBindings

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry.CloudBindingExamples
open NearestJetsExamples

private theorem tangent_dimension : Module.finrank ℝ tangent = 1 := by
  have hn : ‖tangentVector‖ = 1 := by
    simp [tangentVector, EuclideanSpace.single, PiLp.norm_single]
  apply finrank_span_singleton
  intro hz
  rw [hz, norm_zero] at hn
  norm_num at hn

private theorem centers_in_line : range center ⊆ (AffineSubspace.mk' offset tangent : Set H) := by
  rintro x ⟨b, rfl⟩
  cases b with
  | false => exact AffineSubspace.self_mem_mk' offset tangent
  | true =>
    change offset + tangentVector - offset ∈ tangent
    rw [add_sub_cancel_left]
    exact Submodule.subset_span (mem_singleton tangentVector)

private theorem exact_line_cloud (δ : ℝ) (x : H) (hx : x ∈ range center) :
    hausdorffEDist ((AffineSubspace.mk' offset tangent : Set H) ∩ ball x (2 / δ))
      ((AffineSubspace.mk' x tangent : Set H) ∩ ball x (2 / δ)) ≤ ENNReal.ofReal (δ * 2) := by
  have ha : AffineSubspace.mk' x tangent = AffineSubspace.mk' offset tangent := by
    simpa only [AffineSubspace.direction_mk'] using
      (AffineSubspace.mk'_eq (s := AffineSubspace.mk' offset tangent) (centers_in_line hx))
  rw [ha, hausdorffEDist_self]
  exact zero_le

theorem two_center_small_cover :
    ∃ I : Set H, I ⊆ range center ∧ I.Finite ∧
      ((⋃ x ∈ range center, ball x (1 / 50 : ℝ)) ⊆
        ⋃ i ∈ I, ball i (1 / 10 : ℝ)) := by
  obtain ⟨I, hIS, hI, _, hcover, _⟩ := exists_coherent_cloud_cover
    (range center) (AffineSubspace.mk' offset tangent : Set H) centers_in_line
    (finite_range center).totallyBounded (fun _ => 2) (fun _ => tangent)
    1 (fun _ => tangent_dimension) 2 2 0 (1 / 1000)
    (by norm_num) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (by norm_num)
    (by norm_num) (by norm_num) (by intro x hx y hy; simp)
    (fun x => exact_line_cloud _ x x.property)
  exact ⟨I, hIS, hI, by norm_num at hcover ⊢; exact hcover⟩

theorem two_center_large_cover :
    ∃ I : Set H, I ⊆ range center ∧ I.Finite ∧
      ((⋃ x ∈ range center, ball x (16 : ℝ)) ⊆ ⋃ i ∈ I, ball i (40 : ℝ)) := by
  obtain ⟨I, hIS, hI, _, _, hcover, _⟩ := exists_large_cloud_cover_of_blueprint_smallness
    (range center) (AffineSubspace.mk' offset tangent : Set H) centers_in_line
    (finite_range center).totallyBounded (fun _ => 2) (fun _ => tangent)
    1 (fun _ => tangent_dimension) 2 2 1 1 (1 / 10000)
    (by norm_num) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx y hy hxy; constructor <;> norm_num)
    (fun x => exact_line_cloud _ x x.property)
  exact ⟨I, hIS, hI, by norm_num at hcover ⊢; exact hcover⟩

theorem two_center_affine_normal_offset :
    ‖tangentᗮ.starProjection (center true - center false)‖ ≤ (1 / 500 : ℝ) := by
  have hh := normal_coherence_of_max_radius_cloud_tests tangent tangent rfl
    (AffineSubspace.mk' offset tangent : Set H) (center false) (center true)
    (centers_in_line (mem_range_self true)) 2 2 1 1 (1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dist_comm, distinct_centers_and_nonempty_overlap.1]; norm_num)
    (by norm_num) (by norm_num)
    (exact_line_cloud _ _ (mem_range_self false)) (exact_line_cloud _ _ (mem_range_self true))
  have he := hh.1
  norm_num at he
  rw [Submodule.starProjection_orthogonal_val, map_sub]
  exact he

theorem retained_constant_image_radius :
    ∀ x : range (fun p : H => p),
      0 < ((1 / 100 : ℝ) * (fun _ : H => (2 : ℝ)) (Classical.choose x.property)) := by
  have hh := retained_marker_image_radius (fun p : H => p) (fun _ => 2)
    (fun (_ : Unit) (_ : H) => (2 : ℝ)) (fun _ => 2)
    (fun _ => by norm_num) (fun _ => (LipschitzWith.const 2).weaken (by norm_num))
    (fun _ => ⟨(), rfl⟩) (by intro i p hp; constructor <;> norm_num)
    (1 / 100) 1 (by norm_num) (by norm_num) (by norm_num)
  exact hh.1

theorem two_center_retained_cloud_manifold :
    ∃ Z : Set H, Nonempty Z ∧ ∃ cs : ChartedSpace (Fin 1 → ℝ) Z,
      let _ := cs
      IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ Z ∧
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, H) ∞
          (Subtype.val : Z → H) := by
  classical
  let S : Set H := range center
  let T : Set H := (AffineSubspace.mk' offset tangent : Set H)
  obtain ⟨F, hF, C, hC, δ₀, hδ₀, _, hproduce⟩ :=
    exists_uniform_retained_marker_cloud_nearest_finite_budget 1 2 (1 / 20)
      (by norm_num) (by norm_num)
  let δ : ℝ := min δ₀ (1 / 10000)
  have hi : δ * ((80 * (5 / 3 : ℝ) + 31) * (1 / 20 : ℝ)⁻¹ + 2) < 1 := by
    have hs : δ ≤ 1 / 10000 := min_le_right _ _
    norm_num
    linarith
  obtain ⟨I, hI, _, _, _, _, hrest⟩ := hproduce H S T centers_in_line
    (finite_range center).totallyBounded (fun _ => 2) (fun _ => tangent)
    (fun x hx => tangent_dimension) 2 2 δ (by norm_num)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (lt_min hδ₀ (by norm_num))
    (min_le_left _ _) hi H Unit id (fun _ => 25600)
    (fun _ _ => 25600) (fun _ => 25600) id (1 / 12800)
    (fun _ => by norm_num) (fun _ => (LipschitzWith.const 25600).weaken (by norm_num))
    (fun _ => ⟨(), rfl⟩) (by intro i p hp; constructor <;> norm_num)
    (by intro x hx; rfl) (by intro x hx; norm_num) (by norm_num) (by norm_num)
    (fun x hx => exact_line_cloud δ x hx)
  dsimp only at hrest
  rcases hrest.1.2 with ⟨cs, hcs, hemb, p, _, _, _, _, _, _, _⟩
  let x₀ : S := ⟨center false, mem_range_self false⟩
  have hz : center false ∈ ⋃ x : S, ball (x : H) (2 : ℝ) :=
    mem_iUnion.mpr ⟨x₀, mem_ball_self (by norm_num)⟩
  refine ⟨_, ⟨p ⟨center false, hz⟩⟩, cs, hcs, hemb⟩

end GC.MetricGeometry.CloudBindingExamples
