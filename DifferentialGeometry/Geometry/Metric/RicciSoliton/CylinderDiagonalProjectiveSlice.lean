import DifferentialGeometry.Topology.ProjectiveSpace.SmoothNonembedding
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderProjectiveSlice
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition

section
open private exists_diffeomorph_orbitQuotient from DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "ThreeSpace" => EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold (𝓡 3) ∞ N]

theorem exists_projective_slice_diagonal_image
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ⊆
      Phi.source) :
    ∃ e : SphereAntipodalQuotient → N,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e ∧
      (∀ z : SphereTwo, e (SphereAntipodalQuotient.proj z) =
        Phi (d (Geometry.cylinderDiagonalQuotientMap (z, 0)))) ∧
      range e = Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
        (univ ×ˢ ({0} : Set ℝ)))) ∧
      range e ⊆ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
        (univ ×ˢ Icc (-L) L))) := by
  obtain ⟨D, hD⟩ := exists_diffeomorph_orbitQuotient
  let f : SphereAntipodalQuotient → M :=
    (D.trans d) ∘ CylinderDiagonalQuotient.projectiveSlice
  have hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    (diffeomorph_isSmoothEmbedding (D.trans d)).comp
      CylinderDiagonalQuotient.isSmoothEmbedding_projectiveSlice (by simp)
  have hfproj (z : SphereTwo) : f (SphereAntipodalQuotient.proj z) =
      d (Geometry.cylinderDiagonalQuotientMap (z, 0)) := by
    change d (D (CylinderDiagonalQuotient.projectiveSlice
      (SphereAntipodalQuotient.proj z))) = _
    rw [CylinderDiagonalQuotient.projectiveSlice_proj, hD]
  have hfrange : range f = d '' (Geometry.cylinderDiagonalQuotientMap ''
      (univ ×ˢ ({0} : Set ℝ))) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := SphereAntipodalQuotient.surjective_proj z
      exact ⟨Geometry.cylinderDiagonalQuotientMap (w, 0),
        ⟨(w, 0), ⟨mem_univ _, rfl⟩, rfl⟩, (hfproj w).symm⟩
    · rintro ⟨z, ⟨⟨w, s⟩, ⟨_, hs⟩, rfl⟩, rfl⟩
      have hs0 : s = 0 := hs
      subst s
      exact ⟨SphereAntipodalQuotient.proj w, hfproj w⟩
  have hslab : d '' (Geometry.cylinderDiagonalQuotientMap ''
      (univ ×ˢ ({0} : Set ℝ))) ⊆
      d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) := by
    apply image_mono
    apply image_mono
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨mem_univ _, hz0.symm ▸ ⟨neg_nonpos.mpr hL, hL⟩⟩
  have hfsrc : range f ⊆ Phi.source := by
    rw [hfrange]
    exact hslab.trans hsource
  refine ⟨Phi ∘ f,
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph Phi hf hfsrc,
    ?_, ?_, ?_⟩
  · intro z
    exact congrArg Phi (hfproj z)
  · rw [range_comp, hfrange]
  · rw [range_comp, hfrange]
    exact image_mono hslab

theorem not_diagonal_slab_image_subset_partialDiffeomorph_target
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ⊆
      Phi.source)
    (chart : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace N ∞) :
    ¬ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
      (univ ×ˢ Icc (-L) L))) ⊆ chart.target := by
  obtain ⟨e, he, _, _, hsub⟩ := exists_projective_slice_diagonal_image d Phi hL hsource
  intro hchart
  exact SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target e he chart
    (hsub.trans hchart)

theorem not_diagonal_slab_image_subset_partialDiffeomorph_image
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ⊆
      Phi.source)
    (chart : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace N ∞)
    {A : Set ThreeSpace} (hA : A ⊆ chart.source) :
    ¬ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
      (univ ×ˢ Icc (-L) L))) ⊆ chart '' A := by
  intro hsub
  apply not_diagonal_slab_image_subset_partialDiffeomorph_target d Phi hL hsource chart
  apply hsub.trans
  rintro y ⟨z, hz, rfl⟩
  exact chart.map_source (hA hz)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
