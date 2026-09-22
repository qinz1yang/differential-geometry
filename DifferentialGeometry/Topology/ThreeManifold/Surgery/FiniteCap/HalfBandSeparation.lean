import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.HalfBandComponents

set_option autoImplicit false

open Set Function
open DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private theorem isCompact_negative_closed_half_band {δ : ℝ} (hδ : 0 < δ) :
    IsCompact {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} := by
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} =
      (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
        Icc (-δ⁻¹) (-1 : ℝ) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_univ _, hq⟩
    · intro hp
      have hmem : p ∈ bufferedCylinder δ := by
        change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1
        constructor <;> linarith [inv_pos.mpr hδ, hp.2.1, hp.2.2]
      exact ⟨⟨p, hmem⟩, hp.2, rfl⟩
  rw [he]
  exact isCompact_univ.prod isCompact_Icc

theorem isCompact_negative_closed_half_band_image {M : Type*} [TopologicalSpace M]
    {δ : ℝ} (hδ : 0 < δ) (f : bufferedCylinder δ → M) (hf : Continuous f) :
    IsCompact (f '' {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)}) :=
  (isCompact_negative_closed_half_band hδ).image hf

theorem negative_closed_half_band_images_disjoint {ι M : Type*} {precision : ι → ℝ}
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j))) :
    Pairwise fun i j => Disjoint
      (f i '' {q : bufferedCylinder (precision i) |
        q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)})
      (f j '' {q : bufferedCylinder (precision j) |
        q.val.2 ∈ Icc (-(precision j)⁻¹) (-1 : ℝ)}) := by
  intro i j hij
  exact (hdisj hij).mono (image_subset_range _ _) (image_subset_range _ _)

theorem negative_closed_half_band_image_disjoint_retainedCore
    {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ}
    (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (R : Set (ConnectedComponents (cutCore f))) (i : ι)
    (hi : cuttingSphereComponent hδ f hf hdisj (i, false) ∉ R) :
    Disjoint
      (f i '' {q : bufferedCylinder (precision i) |
        q.val.2 ∈ Icc (-(precision i)⁻¹) (-1 : ℝ)})
      (Subtype.val '' retainedCore f R) := by
  have hpartition : Disjoint (Subtype.val '' discardedCore f R)
      (Subtype.val '' retainedCore f R) :=
    disjoint_image_of_injective Subtype.val_injective
      (retained_discarded_partition f R).2.symm
  exact hpartition.mono_left
    (negative_closed_half_band_image_subset_discardedCore hδ f hf hdisj R i hi)

end DifferentialGeometry.Topology.ThreeManifold.Surgery
