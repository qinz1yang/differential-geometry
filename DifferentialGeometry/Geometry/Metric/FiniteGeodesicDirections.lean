import DifferentialGeometry.Geometry.Metric.CompactDirections

set_option autoImplicit false

open Set Metric Filter Topology

namespace Metric

theorem exists_finite_representative_net_with_common_length
    {X : Type*} [MetricSpace X] (q : X) [HasAnglesAt q]
    [CompactSpace (SpaceOfDirections q)] {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (GeodesicRepresentative q), ∃ S : ℝ, 0 < S ∧
      (∀ σ ∈ F, S ≤ σ.length) ∧
      ∀ v : SpaceOfDirections q, ∃ σ ∈ F, dist v σ.direction < ε := by
  classical
  obtain ⟨T, _, hT⟩ := exists_finset_net_of_isCompact
    (isCompact_univ : IsCompact (univ : Set (SpaceOfDirections q))) (half_pos hε)
  choose σ hσ using fun v : T => v.val.exists_representative_dist_lt (half_pos hε)
  let F : Finset (GeodesicRepresentative q) := Finset.univ.image σ
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ v : T, s ≤ (σ v).length := by
    apply eventually_all.mpr
    intro v
    filter_upwards [Ioc_mem_nhdsGT (σ v).length_pos] with s hs using hs.2
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨S, hS, hlength⟩ := (hpos.and hsmall).exists
  refine ⟨F, S, hS, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hτ
    exact hlength v
  · intro v
    obtain ⟨w, hw, hvw⟩ := hT v (mem_univ _)
    refine ⟨σ ⟨w, hw⟩, Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    have ht := dist_triangle v w (σ ⟨w, hw⟩).direction
    have ha := hσ ⟨w, hw⟩
    linarith

end Metric
