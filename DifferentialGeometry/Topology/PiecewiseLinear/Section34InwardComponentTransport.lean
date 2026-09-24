import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentTrapping

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem Homeomorph.mapsTo_inter_interior_of_push_frontier {M : Type*}
    [TopologicalSpace M] (ψ : M ≃ₜ M) {T B : Set M}
    (hmap : MapsTo ψ T T) (hpush : MapsTo ψ (frontier T ∩ B) (interior T)) :
    MapsTo ψ (T ∩ B) (interior T) := by
  intro x hx
  by_cases hxi : x ∈ interior T
  · have hi : ψ '' interior T ⊆ interior T := by
      rw [ψ.image_interior]
      exact interior_mono hmap.image_subset
    exact hi ⟨x, hxi, rfl⟩
  · exact hpush ⟨⟨subset_closure hx.1, hxi⟩, hx.2⟩

theorem Homeomorph.exists_component_containing_outside_new_region {M : Type*}
    [TopologicalSpace M] (ψ : M ≃ₜ M) {S T T' : Set M}
    (hcomponent : ∃ y₀ ∈ S, ∀ z ∈ S, z ∉ T → z ∈ connectedComponentIn S y₀)
    (hmap : MapsTo ψ (T ∩ S) T') :
    ∃ y₀ ∈ ψ '' S, ∀ z ∈ ψ '' S, z ∉ T' →
      z ∈ connectedComponentIn (ψ '' S) y₀ := by
  obtain ⟨y₀, hy₀, hc⟩ := hcomponent
  refine ⟨ψ y₀, ⟨y₀, hy₀, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ hn
  rw [← ψ.image_connectedComponentIn hy₀]
  exact ⟨z, hc z hz (fun hzT => hn (hmap ⟨hzT, hz⟩)), rfl⟩

theorem Homeomorph.closure_components_image_subset {M : Type*}
    [TopologicalSpace M] (ψ : M ≃ₜ M) {S B T T' : Set M}
    (hSB : S ⊆ B) (hB : IsClosed B) {a : M} (ha : a ∈ S)
    (htrap : ∀ y ∈ S, y ∉ connectedComponentIn S a →
      closure (connectedComponentIn S y) ⊆ T)
    (hmap : MapsTo ψ (T ∩ B) T') :
    ∀ y ∈ ψ '' S, y ∉ connectedComponentIn (ψ '' S) (ψ a) →
      closure (connectedComponentIn (ψ '' S) y) ⊆ T' := by
  rintro _ ⟨y, hy, rfl⟩ hne
  have hyne : y ∉ connectedComponentIn S a := by
    intro hya
    apply hne
    rw [← ψ.image_connectedComponentIn ha]
    exact ⟨y, hya, rfl⟩
  rw [← ψ.image_connectedComponentIn hy, ← ψ.image_closure]
  rintro _ ⟨z, hz, rfl⟩
  exact hmap ⟨htrap y hy hyne hz,
    closure_minimal ((connectedComponentIn_subset S y).trans hSB) hB hz⟩

theorem Homeomorph.exists_piercing_components_interior_trapped {M : Type*}
    [TopologicalSpace M] (ψ : M ≃ₜ M) {A B T : Set M}
    (hA : ψ '' A = A) (hB : IsClosed B)
    (hmap : MapsTo ψ T T) (hpush : MapsTo ψ (frontier T ∩ B) (interior T))
    {a b : M} (ha : a ∈ B ∩ A) (hb : b ∈ B \ A)
    (hin : ∀ y ∈ B ∩ A, y ∉ connectedComponentIn (B ∩ A) a →
      closure (connectedComponentIn (B ∩ A) y) ⊆ T)
    (hout : ∀ y ∈ B \ A, y ∉ connectedComponentIn (B \ A) b →
      closure (connectedComponentIn (B \ A) y) ⊆ T) :
    ∃ a' ∈ ψ '' B ∩ A, ∃ b' ∈ ψ '' B \ A,
      (∀ y ∈ ψ '' B ∩ A, y ∉ connectedComponentIn (ψ '' B ∩ A) a' →
        closure (connectedComponentIn (ψ '' B ∩ A) y) ⊆ interior T) ∧
      ∀ y ∈ ψ '' B \ A, y ∉ connectedComponentIn (ψ '' B \ A) b' →
        closure (connectedComponentIn (ψ '' B \ A) y) ⊆ interior T := by
  have hpush' := Homeomorph.mapsTo_inter_interior_of_push_frontier ψ hmap hpush
  have hin' := Homeomorph.closure_components_image_subset ψ inter_subset_left hB ha hin hpush'
  have hout' := Homeomorph.closure_components_image_subset ψ sdiff_subset hB hb hout hpush'
  have ha' : ψ a ∈ ψ '' (B ∩ A) := ⟨a, ha, rfl⟩
  have hb' : ψ b ∈ ψ '' (B \ A) := ⟨b, hb, rfl⟩
  rw [image_inter ψ.injective, hA] at ha' hin'
  rw [image_sdiff ψ.injective, hA] at hb' hout'
  exact ⟨ψ a, ha', ψ b, hb', hin', hout'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
