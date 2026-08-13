import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Filter Set Uniformity UniformSpace
open scoped SetRel Topology

theorem inj_of_unif_close
    {α : Type*} [UniformSpace α] [CompactSpace α]
    (U : α → Set α) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ V ∈ 𝓤 α, ∀ (f : α → α),
      (∀ x, f x ∈ ball x V) →
      (∀ z, Set.InjOn f (U z)) → Function.Injective f := by
  obtain ⟨W, hW, hcover⟩ :=
    lebesgue_number_lemma_nhds (K := (Set.univ : Set α))
      isCompact_univ (fun x _ => hU x)
  obtain ⟨V, hV, hVsymm, hVV⟩ := comp_symm_mem_uniformity_sets hW
  refine ⟨V, hV, ?_⟩
  intro f hclose hinj x y hxy
  letI : SetRel.IsSymm V := hVsymm
  obtain ⟨z, hz⟩ := hcover x (Set.mem_univ x)
  apply hinj z
  · exact hz (mem_ball_self x hW)
  · apply hz
    apply hVV
    apply mem_ball_comp (hclose x)
    rw [hxy]
    exact (mem_ball_symmetry (V := V)).mp (hclose y)
  · exact hxy

theorem surj_of_unif_close
    {α : Type*} [UniformSpace α] [CompactSpace α]
    [LocallyConnectedSpace α] :
    ∃ V ∈ 𝓤 α, ∀ (f : α → α),
      (∀ x, f x ∈ ball x V) →
      IsClopen (Set.range f) → Function.Surjective f := by
  have hcomponent : ∀ x : α, connectedComponent x ∈ 𝓝 x := fun x =>
    isOpen_connectedComponent.mem_nhds mem_connectedComponent
  obtain ⟨V, hV, hcover⟩ :=
    lebesgue_number_lemma_nhds (K := (Set.univ : Set α))
      isCompact_univ (fun x _ => hcomponent x)
  refine ⟨V, hV, ?_⟩
  intro f hclose hrange
  rw [← Set.range_eq_univ]
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨z, hz⟩ := hcover x (Set.mem_univ x)
  have hx : x ∈ connectedComponent z := hz (mem_ball_self x hV)
  have hfx : f x ∈ connectedComponent z := hz (hclose x)
  have hsame : connectedComponent z = connectedComponent (f x) :=
    connectedComponent_eq hfx
  have hx' : x ∈ connectedComponent (f x) := hsame ▸ hx
  exact hrange.connectedComponent_subset (Set.mem_range_self x) hx'

theorem bij_of_unif_close
    {α : Type*} [UniformSpace α] [CompactSpace α]
    [LocallyConnectedSpace α]
    (U : α → Set α) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ V ∈ 𝓤 α, ∀ (f : α → α),
      (∀ x, f x ∈ ball x V) →
      (∀ z, Set.InjOn f (U z)) →
      IsClopen (Set.range f) → Function.Bijective f := by
  obtain ⟨Vinj, hVinj, hinj⟩ := inj_of_unif_close U hU
  obtain ⟨Vsurj, hVsurj, hsurj⟩ := surj_of_unif_close (α := α)
  refine ⟨Vinj ∩ Vsurj, inter_mem hVinj hVsurj, ?_⟩
  intro f hclose hlocal hrange
  have hclose_inj : ∀ x, f x ∈ ball x Vinj := fun x =>
    ball_inter_left x Vinj Vsurj (hclose x)
  have hclose_surj : ∀ x, f x ∈ ball x Vsurj := fun x =>
    ball_inter_right x Vinj Vsurj (hclose x)
  exact ⟨hinj f hclose_inj hlocal, hsurj f hclose_surj hrange⟩

theorem eventually_bijective
    {α ι : Type*} [UniformSpace α] [CompactSpace α]
    [LocallyConnectedSpace α]
    {l : Filter ι} (F : ι → α → α)
    (U : α → Set α) (hU : ∀ x, U x ∈ 𝓝 x)
    (hconv : TendstoUniformly F id l)
    (hlocal : ∀ᶠ i in l, ∀ z, Set.InjOn (F i) (U z))
    (hrange : ∀ᶠ i in l, IsClopen (Set.range (F i))) :
    ∀ᶠ i in l, Function.Bijective (F i) := by
  obtain ⟨V, hV, hbij⟩ := bij_of_unif_close U hU
  filter_upwards [hconv V hV, hlocal, hrange] with i hclose hlocal_i hrange_i
  apply hbij (F i)
  · intro x
    exact hclose x
  · exact hlocal_i
  · exact hrange_i

theorem localDiff_clopen
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [CompactSpace M] [T2Space M]
    {n : WithTop ℕ∞} {f : M → M}
    (hf : IsLocalDiffeomorph I I n f) : IsClopen (Set.range f) :=
  ⟨(isCompact_range hf.isLocalHomeomorph.continuous).isClosed,
    hf.isOpen_range⟩

end DifferentialGeometry.PDE.RicciFlow.Pullback
