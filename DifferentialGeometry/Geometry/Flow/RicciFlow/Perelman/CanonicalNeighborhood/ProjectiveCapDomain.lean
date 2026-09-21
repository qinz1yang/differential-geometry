import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

section
open private capCore_diagonalSlab from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
open private closedSlab closedSlab_eq_image isCompact_closedSlab isConnected_closedSlab
  closure_interior_closedSlab from DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_boundary_chart_closedSlab_image from DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalSlab
open private exists_diffeomorph_orbitQuotient from DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions.CylinderDiagonalQuotient

universe u

private theorem exists_projective_compactDomain_diagonalSlab
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    {L : ℝ} (hL : 0 < L) :
    ∃ K : CompactDomain M,
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) := by
  obtain ⟨e,he⟩ := exists_diffeomorph_orbitQuotient
  let D := e.trans d
  have hr : D '' closedSlab L =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) := by
    rw [closedSlab_eq_image, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro p hp
    change d (e (proj p)) = d (Geometry.cylinderDiagonalQuotientMap p)
    rw [he p]
  let K : CompactDomain M :=
    { carrier := D '' closedSlab L
      compact := (isCompact_closedSlab L).image D.continuous
      connected := (isConnected_closedSlab hL.le).image D D.continuous.continuousOn
      regular_closed := by
        change closure (interior (D.toHomeomorph '' closedSlab L)) = D.toHomeomorph '' closedSlab L
        rw [← D.toHomeomorph.image_interior, ← D.toHomeomorph.image_closure,
          closure_interior_closedSlab hL]
      boundary_chart := fun x hx => exists_boundary_chart_closedSlab_image D hL x hx }
  refine ⟨K, hr, ?_⟩
  change Nonempty (CapCore (D '' closedSlab L))
  rw [hr]
  exact capCore_diagonalSlab d hL

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
open private diagonalSlab_mem_interior_iff from DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_projective_compactDomain_around_diagonalPoint
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    {L : ℝ} (hL : 0 < L) (p : Cylinder) (hp : |p.2| < L) :
    ∃ K : CompactDomain M,
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) ∧
      d (Geometry.cylinderDiagonalQuotientMap p) ∈ interior K.carrier := by
  obtain ⟨K,hK,hcore⟩ := exists_projective_compactDomain_diagonalSlab d hL
  refine ⟨K,hK,hcore,?_⟩
  rw [hK]
  exact (diagonalSlab_mem_interior_iff d L p).2 hp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
open private diagonalSlab_subset_interior from DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab
open private exists_geometry_normalized_slab_collar from DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalSlab

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions.CylinderDiagonalQuotient

private theorem exists_projective_diagonal_slab_with_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (p : Cylinder) {L R : ℝ} (hp : |p.2| < L) (hLR : L < R) :
    let U := d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-R) R))
    ∃ (K : CompactDomain M) (tube : PartialDiffeomorph IC I3 Cylinder M ∞),
      K.carrier = d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
      Nonempty (CapCore K.carrier) ∧
      d (Geometry.cylinderDiagonalQuotientMap p) ∈ interior K.carrier ∧
      K.carrier ⊆ interior U ∧
      (∀ q, tube q = d (Geometry.cylinderDiagonalQuotientMap
        (q.1, L + (R - L) * q.2))) ∧
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ tube.source ∧
      tube '' (univ ×ˢ Icc (0 : ℝ) 1) =
        d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)) ∧
      tube '' (univ ×ˢ ({0} : Set ℝ)) = frontier K.carrier ∧
      tube '' (univ ×ˢ ({1} : Set ℝ)) = frontier U ∧
      K.carrier ∪ tube '' (univ ×ˢ Icc (0 : ℝ) 1) = U ∧
      K.carrier ∩ tube '' (univ ×ˢ Icc (0 : ℝ) 1) = frontier K.carrier ∧
      frontier (tube '' (univ ×ˢ Icc (0 : ℝ) 1)) = frontier K.carrier ∪ frontier U ∧
      Disjoint (frontier K.carrier) (frontier U) := by
  intro U
  have hL : 0 < L := lt_of_le_of_lt (abs_nonneg p.2) hp
  obtain ⟨K,hK,hcore,hpK⟩ := exists_projective_compactDomain_around_diagonalPoint d hL p hp
  obtain ⟨tube,htube,hdom,himage,hin,hout,hunion,hover,hfront,hdisj⟩ :=
    exists_geometry_normalized_slab_collar d hL hLR
  refine ⟨K,tube,hK,hcore,hpK,?_,htube,hdom,himage,?_,hout,?_,?_,?_,?_⟩
  · rw [hK]
    exact diagonalSlab_subset_interior d hLR
  · rw [hK]
    exact hin
  · rw [hK]
    exact hunion
  · rw [hK]
    exact hover
  · rw [hK]
    exact hfront
  · rw [hK]
    exact hdisj

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
