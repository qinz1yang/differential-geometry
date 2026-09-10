import DifferentialGeometry.Topology.PlanarJordan.Regions
import DifferentialGeometry.Topology.Flow.PeriodicOrbit

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem invariant_of_orbit_complement_partition
    (φ : _root_.Flow ℝ ℂ) {x : ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (φ.orbit x)ᶜ) : IsInvariant φ U := by
  intro t y hy
  have hyout : y ∉ φ.orbit x := by
    change y ∈ (φ.orbit x)ᶜ
    rw [← hcover]
    exact Or.inl hy
  have hsub : range (fun s ↦ φ s y) ⊆ U ∪ V := by
    rintro z ⟨s, rfl⟩
    rw [hcover]
    intro hmem
    have hback := φ.mem_orbit_of_mem_orbit (-s) hmem
    apply hyout
    simpa only [← φ.map_add, neg_add_cancel, φ.map_zero_apply] using hback
  have hconn : IsPreconnected (range (fun s ↦ φ s y)) :=
    isPreconnected_range (φ.continuous continuous_id continuous_const)
  have hmeet : (range (fun s ↦ φ s y) ∩ U).Nonempty :=
    ⟨y, ⟨0, φ.map_zero_apply y⟩, hy⟩
  exact hconn.subset_left_of_subset_union hU hV hdisj hsub hmeet ⟨t, rfl⟩

theorem exists_invariant_regions_of_periodic_orbit
    (φ : _root_.Flow ℝ ℂ) {x : ℂ}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (φ.orbit x)ᶜ ∧
      frontier U = φ.orbit x ∧ frontier V = φ.orbit x ∧
      IsCompact (closure U) ∧ ¬ IsCompact (closure V) ∧
      IsInvariant φ U ∧ IsInvariant φ V := by
  obtain ⟨γ, hγ, hclose, hsimple, himage⟩ :=
    DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit φ hnon hreturn
  obtain ⟨U, V, hU, hV, hUc, hVc, hdisj, hcover, hUf, hVf, hcompact, hunbounded⟩ :=
    exists_regions_of_simple_closed_curve hγ.continuousOn hclose hsimple
  rw [himage] at hcover hUf hVf
  exact ⟨U, V, hU, hV, hUc, hVc, hdisj, hcover, hUf, hVf, hcompact, hunbounded,
    invariant_of_orbit_complement_partition φ hU hV hdisj hcover,
    invariant_of_orbit_complement_partition φ hV hU hdisj.symm
      (by rw [union_comm]; exact hcover)⟩

end DifferentialGeometry.Topology.PlanarJordan
