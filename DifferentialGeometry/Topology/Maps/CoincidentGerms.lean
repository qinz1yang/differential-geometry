import Mathlib.Topology.SeparatedMap

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology

/-- A continuous closed map from a preconnected Hausdorff space is injective
if it is locally injective, equal-image points have the same actual image
germ, and one fiber is a singleton. Compactness of the source and separation
of the target are not needed once closedness of the map is supplied. -/
theorem injective_of_isClosedMap_of_isLocallyInjective_of_coincident_germs
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [PreconnectedSpace X]
    {f : X → Y} (hf : Continuous f) (hclosed : IsClosedMap f)
    (hloc : IsLocallyInjective f)
    (hgerm : ∀ x y : X, f x = f y → Filter.map f (𝓝 x) = Filter.map f (𝓝 y))
    (hsingle : ∃ x₀ : X, ∀ x : X, f x = f x₀ → x = x₀) :
    Function.Injective f := by
  classical
  let S : Set X := {x | ∀ y : X, f y = f x → y = x}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hinj⟩ := hloc x
    let V : Set Y := (f '' Uᶜ)ᶜ
    have hV : IsOpen V := (hclosed _ hU.isClosed_compl).isOpen_compl
    have hxV : f x ∈ V := by
      rintro ⟨y, hy, hfy⟩
      exact hy ((hx y hfy).symm ▸ hxU)
    apply Filter.mem_of_superset ((hV.preimage hf).mem_nhds hxV)
    intro z hz w hfw
    have hzU : z ∈ U := by
      by_contra h
      exact hz ⟨z, h, rfl⟩
    have hwU : w ∈ U := by
      by_contra h
      exact hz ⟨w, h, hfw⟩
    exact hinj hwU hzU hfw
  have hScomplOpen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change ¬ ∀ y : X, f y = f x → y = x at hx
    simp only [not_forall] at hx
    obtain ⟨y, hfy, hyx⟩ := hx
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
      t2_separation (show x ≠ y from fun h => hyx h.symm)
    have hpre : f ⁻¹' (f '' V) ∈ 𝓝 x := by
      apply Filter.mem_map.mp
      rw [hgerm x y hfy.symm]
      exact Filter.image_mem_map (hV.mem_nhds hyV)
    apply Filter.mem_of_superset (inter_mem (hU.mem_nhds hxU) hpre)
    rintro z ⟨hzU, w, hwV, hfw⟩ hz
    have hwz : w = z := hz w hfw
    exact Set.disjoint_left.mp hUV hzU (hwz ▸ hwV)
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hScomplOpen, hSopen⟩).eq_univ hsingle
  intro x y hxy
  have hy : y ∈ S := hSuniv.symm ▸ Set.mem_univ y
  exact hy x hxy

/-- A continuous locally injective map from a compact connected Hausdorff
space is injective if every pair of equal-image points has the same image
germ and some fiber is a singleton. The germ condition compares the actual
map at its actual source points; it does not assume a covering or embedding.
-/
theorem injective_of_isLocallyInjective_of_coincident_germs
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    (hgerm : ∀ x y : X, f x = f y → Filter.map f (𝓝 x) = Filter.map f (𝓝 y))
    (hsingle : ∃ x₀ : X, ∀ x : X, f x = f x₀ → x = x₀) :
    Function.Injective f := by
  exact injective_of_isClosedMap_of_isLocallyInjective_of_coincident_germs
    hf hf.isClosedMap hloc hgerm hsingle

end DifferentialGeometry.Topology
