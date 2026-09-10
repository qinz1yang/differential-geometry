import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
  [ConnectedSpace B]

theorem clopen_image_eq_univ {p : C → B} (hp : IsCoveringMap p) (hclosed : IsClosedMap p)
    {K : Set C} (hK : IsClopen K) (hne : K.Nonempty) : p '' K = univ := by
  have hi : IsClopen (p '' K) :=
    ⟨hclosed _ hK.isClosed, hp.isOpenMap _ hK.isOpen⟩
  exact (isClopen_iff.mp hi).resolve_left (hne.image p).ne_empty

theorem projection_homeomorph_of_clopen_split {p : C → B} (hp : IsCoveringMap p) (hclosed : IsClosedMap p)
    (τ : C → C) (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    {K : Set C} (hK : IsClopen K) (hne : K.Nonempty) (hcompl : Kᶜ.Nonempty) :
    ∃ e : K ≃ₜ B, ∀ x : K, e x = p x := by
  have hsurj : Function.Surjective (fun x : K => p x) := by
    intro b
    obtain ⟨x, hx, hpx⟩ := (clopen_image_eq_univ hp hclosed hK hne).symm ▸ (mem_univ b)
    exact ⟨⟨x, hx⟩, hpx⟩
  have hinj : Function.Injective (fun x : K => p x) := by
    intro x y hxy
    obtain ⟨z, hz, hpz⟩ :=
      (clopen_image_eq_univ hp hclosed hK.compl hcompl).symm ▸ (mem_univ (p x))
    have hzx : z ≠ x := fun he => hz (he ▸ x.property)
    have hzτ : z = τ x := (hfiber x z hpz).resolve_left hzx
    rcases hfiber x y hxy.symm with hyx | hyτ
    · exact Subtype.ext hyx.symm
    · exact False.elim (hz (by rw [hzτ, ← hyτ]; exact y.property))
  have he : IsHomeomorph (fun x : K => p x) :=
    ⟨hp.continuous.comp continuous_subtype_val,
      hp.isOpenMap.comp hK.isOpen.isOpenMap_subtype_val, hinj, hsurj⟩
  exact ⟨he.homeomorph _, fun _ => rfl⟩

theorem exists_two_projection_homeomorphs_of_not_connected [Nonempty C]
    {p : C → B} (hp : IsCoveringMap p) (hclosed : IsClosedMap p) (τ : C → C)
    (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    (hnot : ¬ ConnectedSpace C) :
    ∃ K : Set C, IsClopen K ∧ K.Nonempty ∧ Kᶜ.Nonempty ∧
      (∃ e : K ≃ₜ B, ∀ x : K, e x = p x) ∧
      (∃ e : ↥(Kᶜ) ≃ₜ B, ∀ x : ↥(Kᶜ), e x = p x) := by
  have hn : ¬ ∀ K : Set C, IsClopen K → K = ∅ ∨ K = univ :=
    fun h => hnot (connectedSpace_iff_clopen.mpr ⟨inferInstance, h⟩)
  push Not at hn
  obtain ⟨K, hK, hne, hnu⟩ := hn
  have hk : K.Nonempty := hne
  have hc : Kᶜ.Nonempty := Set.nonempty_compl.mpr hnu
  exact ⟨K, hK, hk, hc, projection_homeomorph_of_clopen_split hp hclosed τ hfiber hK hk hc,
    projection_homeomorph_of_clopen_split hp hclosed τ hfiber hK.compl hc (by simpa using hk)⟩

theorem exists_section_of_not_connected_double_cover [Nonempty C]
    {p : C → B} (hp : IsCoveringMap p) (hclosed : IsClosedMap p) (τ : C → C)
    (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    (hnot : ¬ ConnectedSpace C) :
    ∃ s : C(B, C), Function.RightInverse s p := by
  obtain ⟨K, _, _, _, ⟨e, he⟩, _⟩ :=
    exists_two_projection_homeomorphs_of_not_connected hp hclosed τ hfiber hnot
  refine ⟨⟨fun b => e.symm b, continuous_subtype_val.comp e.symm.continuous⟩, ?_⟩
  intro b
  exact (he (e.symm b)).symm.trans (e.apply_symm_apply b)

theorem exists_exactly_two_components_of_not_connected [Nonempty C]
    {p : C → B} (hp : IsCoveringMap p) (hclosed : IsClosedMap p) (τ : C → C)
    (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    (hnot : ¬ ConnectedSpace C) :
    ∃ x y : C,
      Disjoint (connectedComponent x) (connectedComponent y) ∧
      connectedComponent x ∪ connectedComponent y = univ ∧
      (∃ e : connectedComponent x ≃ₜ B, ∀ z : connectedComponent x, e z = p z) ∧
      (∃ e : connectedComponent y ≃ₜ B, ∀ z : connectedComponent y, e z = p z) := by
  obtain ⟨K, hK, ⟨x, hx⟩, ⟨y, hy⟩, ⟨e, he⟩, ⟨e', he'⟩⟩ :=
    exists_two_projection_homeomorphs_of_not_connected hp hclosed τ hfiber hnot
  have hconn : IsConnected K :=
    isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hconn' : IsConnected Kᶜ :=
    isConnected_iff_connectedSpace.mpr (e'.connectedSpace_iff.mpr inferInstance)
  have hc : connectedComponent x = K :=
    (hK.connectedComponent_subset hx).antisymm (hconn.subset_connectedComponent hx)
  have hc' : connectedComponent y = Kᶜ :=
    (hK.compl.connectedComponent_subset hy).antisymm (hconn'.subset_connectedComponent hy)
  refine ⟨x, y, ?_⟩
  rw [hc, hc']
  exact ⟨disjoint_compl_right, union_compl_self K, ⟨e, he⟩, ⟨e', he'⟩⟩

end DifferentialGeometry.Topology.Covering
