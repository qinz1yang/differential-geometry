import DifferentialGeometry.Topology.Compactness.Strip

open Set Function Topology Filter
set_option autoImplicit false

namespace Poincare.Manifold.BoundaryCollar

theorem exists_open_shorter_strip
    {B M : Type*} [TopologicalSpace B] [CompactSpace B] [TopologicalSpace M]
    {ε : ℝ} (hε : 0 < ε) {c : B × Icc (0 : ℝ) ε → M}
    (hc : IsEmbedding c)
    (hzero : ∀ b, range c ∈ 𝓝 (c (b, ⟨0, ⟨le_rfl, hε.le⟩⟩))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      IsOpen (c '' {q | (q.2 : ℝ) < δ}) ∧
      ∀ b, c (b, ⟨0, ⟨le_rfl, hε.le⟩⟩) ∈ c '' {q | (q.2 : ℝ) < δ} := by
  let zero : Icc (0 : ℝ) ε := ⟨0, ⟨le_rfl, hε.le⟩⟩
  let W := interior (range c)
  have hW : IsOpen W := isOpen_interior
  have hWrange : W ⊆ range c := interior_subset
  have hzW (b : B) : c (b, zero) ∈ W := mem_interior_iff_mem_nhds.mpr (hzero b)
  obtain ⟨δ, hδ, hδε, hsmall⟩ :=
    Poincare.Topology.exists_shorter_strip_image_subset hε hc.continuous hW hzW
  have hopen : IsOpen {q : B × Icc (0 : ℝ) ε | (q.2 : ℝ) < δ} :=
    isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  obtain ⟨O, hO, hOeq⟩ := hc.isInducing.image_eq_isOpen_inter_range hopen
  have heq : c '' {q | (q.2 : ℝ) < δ} = O ∩ W := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(hOeq ▸ hy).1, hsmall hy⟩
    · intro y hy
      rw [hOeq]
      exact ⟨hy.1, hWrange hy.2⟩
  refine ⟨δ, hδ, hδε, heq ▸ hO.inter hW, ?_⟩
  intro b
  exact ⟨(b, zero), hδ, rfl⟩

end Poincare.Manifold.BoundaryCollar
