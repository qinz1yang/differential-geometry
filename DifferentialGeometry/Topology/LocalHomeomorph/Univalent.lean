import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

section

noncomputable section
open Set Filter Topology
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem IsLocalHomeomorphOn.isOpenEmbedding_restrict_of_injOn
    {f : X → Y} {Ω : Set X} (hf : IsLocalHomeomorphOn f Ω)
    (hΩ : IsOpen Ω) (hi : InjOn f Ω) : IsOpenEmbedding (Ω.domRestrict f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
    (fun x y hxy => Subtype.ext (hi x.property y.property hxy))
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  have he : Filter.map (Ω.domRestrict f) (𝓝 x) = 𝓝 (f x) := by
    change Filter.map (f ∘ Subtype.val) (𝓝 x) = _
    rw [← Filter.map_map, hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq, hf.map_nhds_eq x.property]
  exact he.ge

theorem IsLocalHomeomorphOn.exists_openPartialHomeomorph_of_injOn [Nonempty X]
    {f : X → Y} {Ω : Set X} (hf : IsLocalHomeomorphOn f Ω)
    (hΩ : IsOpen Ω) (hi : InjOn f Ω) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = Ω ∧ e.target = f '' Ω ∧ (e : X → Y) = f := by
  let e := hi.toPartialEquiv f Ω
  let E := OpenPartialHomeomorph.ofContinuousOpenRestrict e hf.continuousOn
    (hf.isOpenEmbedding_restrict_of_injOn hΩ hi).isOpenMap hΩ
  exact ⟨E, rfl, rfl, rfl⟩

end

end
