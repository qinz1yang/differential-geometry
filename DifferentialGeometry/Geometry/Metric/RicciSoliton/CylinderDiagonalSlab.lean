import DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab

section
open private closedSlab closedSlab_eq_image exists_normalized_slab_collar
  frontier_image_positive_tube disjoint_frontier_image_closedSlab
  from DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem exists_geometry_normalized_slab_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮CI, 𝓡 3⟯ M)
    {L R : ℝ} (hL : 0 < L) (hLR : L < R) :
    let K := d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L))
    let U := d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R))
    ∃ tube : PartialDiffeomorph CI (𝓡 3) (S × ℝ) M ∞,
      (∀ p, tube p = d (Geometry.cylinderDiagonalQuotientMap
        (p.1, L + (R - L) * p.2))) ∧
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ tube.source ∧
      tube '' (univ ×ˢ Icc (0 : ℝ) 1) =
        d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)) ∧
      tube '' (univ ×ˢ ({0} : Set ℝ)) = frontier K ∧
      tube '' (univ ×ˢ ({1} : Set ℝ)) = frontier U ∧
      K ∪ tube '' (univ ×ˢ Icc (0 : ℝ) 1) = U ∧
      K ∩ tube '' (univ ×ˢ Icc (0 : ℝ) 1) = frontier K ∧
      frontier (tube '' (univ ×ˢ Icc (0 : ℝ) 1)) = frontier K ∪ frontier U ∧
      Disjoint (frontier K) (frontier U) := by
  intro K U
  have hslabs (a : ℝ) : d '' closedSlab a =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-a) a)) :=
    congrArg (Set.image d) (closedSlab_eq_image a)
  obtain ⟨tube, htube, hdomain, himage, hin, hout, hunion, hinter⟩ :=
    exists_normalized_slab_collar d hL hLR
  refine ⟨tube, htube, hdomain, himage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hslabs, K] using hin
  · simpa only [hslabs, U] using hout
  · simpa only [hslabs, K, U] using hunion
  · simpa only [hslabs, K] using hinter
  · rw [himage]
    have h := frontier_image_positive_tube d.toHomeomorph hL hLR.le
    change frontier (d '' (proj '' (univ ×ˢ Icc L R))) =
      frontier (d '' closedSlab L) ∪ frontier (d '' closedSlab R) at h
    simpa only [hslabs, K, U] using h
  · have h := disjoint_frontier_image_closedSlab d.toHomeomorph hL (hL.trans hLR) hLR.ne
    change Disjoint (frontier (d '' closedSlab L)) (frontier (d '' closedSlab R)) at h
    simpa only [hslabs, K, U] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

end

end

section
open private closedSlab closedSlab_eq_image preimage_interior_closedSlab
  from DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open KappaSolutions.CylinderDiagonalQuotient

private theorem diagonalSlab_mem_interior_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮((𝓡 2).prod 𝓘(ℝ, ℝ)), (𝓡 3)⟯ M)
    (L : ℝ) (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) :
    d (Geometry.cylinderDiagonalQuotientMap p) ∈
      interior (d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L))) ↔
        |p.2| < L := by
  change d.toHomeomorph (proj p) ∈
    interior (d.toHomeomorph '' (proj '' (univ ×ˢ Icc (-L) L))) ↔ _
  rw [← closedSlab_eq_image, ← d.toHomeomorph.image_interior,
    d.toHomeomorph.injective.mem_set_image]
  change p ∈ proj ⁻¹' interior (closedSlab L) ↔ _
  rw [preimage_interior_closedSlab]
  simp only [mem_prod, mem_univ, true_and, mem_Ioo, abs_lt]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


private theorem diagonalSlab_subset_interior
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮((𝓡 2).prod 𝓘(ℝ, ℝ)), (𝓡 3)⟯ M)
    {L R : ℝ} (hLR : L < R) :
    d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ⊆
      interior (d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R))) := by
  rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
  apply (diagonalSlab_mem_interior_iff d R p).2
  have hab : |p.2| ≤ L := abs_le.mpr hp.2
  exact hab.trans_lt hLR

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
