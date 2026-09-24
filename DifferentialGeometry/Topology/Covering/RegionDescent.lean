import DifferentialGeometry.Topology.Covering.DeckGroup
import DifferentialGeometry.Topology.Connected.CoverBySides

section

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

variable {E M S : Type*} [TopologicalSpace E] [PreconnectedSpace E]
  [TopologicalSpace M] [Nonempty S]
  {p : E → M} {e : S → M} {lift : S → E}

theorem coveringDeckGroup_eq_one_of_preserves_lift_range
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    (gamma : coveringDeckGroup p)
    (hgamma : (fun y => gamma • y) '' range lift = range lift) : gamma = 1 := by
  obtain ⟨z⟩ := (inferInstance : Nonempty S)
  have hz : gamma • lift z ∈ range lift := hgamma ▸ mem_image_of_mem _ (mem_range_self z)
  obtain ⟨w, hw⟩ := hz
  have hwz : w = z := he (by rw [← hlift w, hw, coveringDeckGroup_map (p := p) gamma (lift z), hlift z])
  subst w
  exact coveringDeckGroup_eq_one_of_apply_eq hp gamma (lift z) hw.symm

theorem coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    {B : Set E} (hfrontier : frontier B = range lift) (gamma : coveringDeckGroup p)
    (hgamma : (fun y => gamma • y) '' B = B) : gamma = 1 := by
  apply coveringDeckGroup_eq_one_of_preserves_lift_range hp he hlift gamma
  change (coveringDeckGroupHomeomorph gamma) '' range lift = range lift
  rw [← hfrontier, Homeomorph.image_frontier]
  exact congrArg frontier hgamma

end DifferentialGeometry

end

end

section

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

variable {E M S : Type*} [TopologicalSpace E] [SimplyConnectedSpace E]
  [LocallyPathConnectedSpace E] [TopologicalSpace M] [Nonempty S]
  {p : E → M} {e : S → M} {lift : S → E}

theorem IsCoveringMap.injOn_closure_of_lifted_frontier
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    {B : Set E} (hBopen : IsOpen B) (hBconn : IsPreconnected B)
    (hfrontier : frontier B = range lift) (havoid : Disjoint B (p ⁻¹' range e)) :
    InjOn p (closure B) := by
  have hnot (y : E) (hy : y ∈ B) : p y ∉ range e := fun hs => havoid.le_bot ⟨hy, hs⟩
  have hproj (y : E) (hy : y ∈ frontier B) : p y ∈ range e := by
    obtain ⟨z, rfl⟩ := hfrontier ▸ hy
    exact ⟨z, (hlift z).symm⟩
  intro x hx y hy hxy
  by_cases hxB : x ∈ B
  · have hyB : y ∈ B := by
      by_contra hyB
      have hyF : y ∈ frontier B := ⟨hy, by simpa only [hBopen.interior_eq] using hyB⟩
      exact hnot x hxB (hxy ▸ hproj y hyF)
    obtain ⟨gamma, hgamma⟩ := (coveringDeckGroup_apply_eq_iff hp).mp hxy.symm
    let H := coveringDeckGroupHomeomorph gamma
    have hHproj (z : E) : p (H z) = p z := coveringDeckGroup_map gamma z
    have hmeet : (H '' B ∩ B).Nonempty := ⟨y, ⟨x, hxB, hgamma⟩, hyB⟩
    have hdis : Disjoint (H '' B) (frontier B) := by
      rw [Set.disjoint_left]
      rintro z ⟨w, hw, rfl⟩ hz
      exact hnot w hw (hHproj w ▸ hproj (H w) hz)
    have hsub : H '' B ⊆ B :=
      (Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        (hBconn.image H H.continuous.continuousOn) hmeet hdis).trans interior_subset
    have hdis' : Disjoint B (frontier (H '' B)) := by
      rw [← H.image_frontier, Set.disjoint_left]
      rintro z hz ⟨w, hw, rfl⟩
      exact hnot (H w) hz ((hHproj w).symm ▸ hproj w hw)
    have hsub' : B ⊆ H '' B :=
      (Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        hBconn (by simpa only [inter_comm] using hmeet) hdis').trans interior_subset
    have hgamma' : gamma = 1 := coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier
      hp he hlift hfrontier gamma (hsub.antisymm hsub')
    simpa only [hgamma', one_smul] using hgamma
  · have hxF : x ∈ frontier B := ⟨hx, by simpa only [hBopen.interior_eq] using hxB⟩
    have hyB : y ∉ B := fun hyB => hnot y hyB (hxy ▸ hproj x hxF)
    have hyF : y ∈ frontier B := ⟨hy, by simpa only [hBopen.interior_eq] using hyB⟩
    obtain ⟨a, rfl⟩ := hfrontier ▸ hxF
    obtain ⟨b, rfl⟩ := hfrontier ▸ hyF
    exact congrArg lift (he ((hlift a).symm.trans (hxy.trans (hlift b))))

end DifferentialGeometry

end

end
