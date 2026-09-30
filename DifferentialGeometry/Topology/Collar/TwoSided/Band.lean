import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {A M : Type*} [TopologicalSpace A] [CompactSpace A] [ConnectedSpace A]
  [TopologicalSpace M] [T2Space M]
  (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ)

include hφ

omit [T2Space M] in
theorem bicollar_band_compact_connected {s t : ℝ} (hst : s ≤ t) :
    IsCompact (φ '' ((univ : Set A) ×ˢ Icc s t)) ∧
      IsConnected (φ '' ((univ : Set A) ×ˢ Icc s t)) :=
  ⟨(isCompact_univ.prod isCompact_Icc).image hφ.continuous,
    (isConnected_univ.prod (isConnected_Icc hst)).image φ hφ.continuous.continuousOn⟩


theorem bicollar_band_closure {s t : ℝ} (hst : s < t) :
    closure (φ '' ((univ : Set A) ×ˢ Ioo s t)) =
      φ '' ((univ : Set A) ×ˢ Icc s t) := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact image_mono (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
    · exact (bicollar_band_compact_connected φ hφ hst.le).1.isClosed
  · have h := image_closure_subset_closure_image hφ.continuous
      (s := (univ : Set A) ×ˢ Ioo s t)
    rw [closure_prod_eq, closure_univ, closure_Ioo hst.ne] at h
    exact h

omit [CompactSpace A] [ConnectedSpace A] [T2Space M] in
theorem bicollar_band_interior (s t : ℝ) :
    interior (φ '' ((univ : Set A) ×ˢ Icc s t)) =
      φ '' ((univ : Set A) ×ˢ Ioo s t) := by
  let C : Set (A × ℝ) := (univ : Set A) ×ˢ Icc s t
  have hCint : interior C = (univ : Set A) ×ˢ Ioo s t := by
    dsimp only [C]
    rw [interior_prod_eq, interior_univ, interior_Icc]
  have hpre : φ ⁻¹' interior (φ '' C) = interior C := by
    rw [hφ.isOpenMap.preimage_interior_eq_interior_preimage hφ.continuous,
      preimage_image_eq _ hφ.injective]
  change interior (φ '' C) = φ '' ((univ : Set A) ×ˢ Ioo s t)
  rw [← hCint]
  apply Subset.antisymm
  · intro q hq
    obtain ⟨x, _hx, rfl⟩ := interior_subset hq
    have hx : x ∈ φ ⁻¹' interior (φ '' C) := hq
    rw [hpre] at hx
    exact ⟨x, hx, rfl⟩
  · exact hφ.isOpenMap.image_interior_subset C


theorem bicollar_band_frontier {s t : ℝ} (hst : s < t) :
    frontier (φ '' ((univ : Set A) ×ˢ Icc s t)) =
      range (fun y => φ (y, s)) ∪ range (fun y => φ (y, t)) := by
  rw [frontier, (bicollar_band_compact_connected φ hφ hst.le).1.isClosed.closure_eq,
    bicollar_band_interior φ hφ s t]
  ext q
  constructor
  · rintro ⟨⟨⟨y, z⟩, ⟨_, hzlo, hzhi⟩, rfl⟩, hnot⟩
    by_cases hzs : z = s
    · exact Or.inl ⟨y, by rw [hzs]⟩
    by_cases hzt : z = t
    · exact Or.inr ⟨y, by rw [hzt]⟩
    exact False.elim (hnot ⟨(y, z), ⟨mem_univ _,
      lt_of_le_of_ne hzlo (Ne.symm hzs), lt_of_le_of_ne hzhi hzt⟩, rfl⟩)
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨⟨(y, s), ⟨mem_univ _, le_rfl, hst.le⟩, rfl⟩, ?_⟩
      rintro ⟨⟨y', z⟩, ⟨_, hzlo, _hzhi⟩, heq⟩
      have hz := congrArg Prod.snd (hφ.injective heq)
      change z = s at hz
      exact (ne_of_gt hzlo) hz
    · refine ⟨⟨(y, t), ⟨mem_univ _, hst.le, le_rfl⟩, rfl⟩, ?_⟩
      rintro ⟨⟨y', z⟩, ⟨_, _hzlo, hzhi⟩, heq⟩
      have hz := congrArg Prod.snd (hφ.injective heq)
      change z = t at hz
      exact (ne_of_lt hzhi) hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
