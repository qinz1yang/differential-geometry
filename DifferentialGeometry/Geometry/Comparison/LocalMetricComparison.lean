import DifferentialGeometry.Geometry.Comparison.MetricTransfer

set_option autoImplicit false

open Set Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_local_fourPointComparison_preimage
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ : ℝ}
    {f : Y → X} (hf : Continuous f) {p : Y}
    (hlocal : ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ f p ∈ Ω)
    (hmetric : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ ball p r, ∀ b ∈ ball p r,
      dist (f a) (f b) = dist a b) :
    ∃ Ω : Set Y, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω := by
  obtain ⟨Ω, hΩ, hcomp, hp⟩ := hlocal
  obtain ⟨r, hr, hdist⟩ := hmetric
  refine ⟨f ⁻¹' Ω ∩ ball p r, (hΩ.preimage hf).inter isOpen_ball, ?_,
    ⟨hp, by simpa only [mem_ball, dist_self] using hr⟩⟩
  apply (fourPointComparison_image_iff_of_dist_eq
    (fun a ha b hb => hdist a ha.2 b hb.2)).mp
  apply hcomp.mono
  rintro _ ⟨a, ha, rfl⟩
  exact ha.1

theorem exists_local_fourPointComparison_iff_of_isOpenEmbedding
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {κ : ℝ}
    {f : Y → X} (hf : IsOpenEmbedding f) {p : Y}
    (hmetric : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ ball p r, ∀ b ∈ ball p r,
      dist (f a) (f b) = dist a b) :
    (∃ Ω : Set Y, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω) ↔
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ f p ∈ Ω :=
  ⟨fun h => exists_local_fourPointComparison_image hf h hmetric,
    fun h => exists_local_fourPointComparison_preimage hf.continuous h hmetric⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
