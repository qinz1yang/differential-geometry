import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonRestriction
import Mathlib.Topology.Constructions.SumProd
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [T2Space M] in
theorem SpatialNeck.isCompact_image_slab
    {g : SmoothRiemannianMetric I3 M} {eps a b : ℝ} {x : M}
    (nk : SpatialNeck g eps x) (ha : -eps⁻¹ < a) (hb : b < eps⁻¹) :
    IsCompact (nk.map '' (univ ×ˢ Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply nk.map.contMDiffOn_toFun.continuousOn.mono
  intro y hy
  exact nk.domain ⟨hy.1, ha.trans_le hy.2.1, hy.2.2.trans_lt hb⟩

omit [T2Space M] in
theorem SpatialNeck.isOpen_image_openSlab
    {g : SmoothRiemannianMetric I3 M} {eps a b : ℝ} {x : M}
    (nk : SpatialNeck g eps x) (ha : -eps⁻¹ ≤ a) (hb : b ≤ eps⁻¹) :
    IsOpen (nk.map '' (univ ×ˢ Ioo a b)) := by
  apply nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo)
  intro y hy
  exact nk.domain ⟨hy.1, ha.trans_lt hy.2.1, hy.2.2.trans_le hb⟩

theorem SpatialNeck.frontier_image_slab
    {g : SmoothRiemannianMetric I3 M} {eps a b : ℝ} {x : M}
    (nk : SpatialNeck g eps x) (ha : -eps⁻¹ < a) (hb : b < eps⁻¹) (hab : a ≤ b) :
    frontier (nk.map '' (univ ×ˢ Icc a b)) = nk.map '' (univ ×ˢ ({a, b} : Set ℝ)) := by
  have hsub : univ ×ˢ Icc a b ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨hy.1, ha.trans_le hy.2.1, hy.2.2.trans_lt hb⟩
  have h := nk.map.toOpenPartialHomeomorph.image_frontier_of_subset_source hsub
    (isClosed_univ.prod isClosed_Icc) (nk.isCompact_image_slab ha hb).isClosed
  rw [frontier_univ_prod_eq, frontier_Icc hab] at h
  exact h.symm

def StrongNeck.region {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) : Set M :=
  nk.map '' (Set.univ ×ˢ Set.Icc (-10) 10)

theorem StrongNeck.frontier_region {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    frontier nk.region = nk.map '' (Set.univ ×ˢ ({-10, 10} : Set ℝ)) := by
  have h11 : (10 : ℝ) < eps⁻¹ := by
    have h : (1 / 11 : ℝ)⁻¹ < eps⁻¹ :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 11) nk.eps_pos).2 nk.eps_small
    norm_num at h
    linarith
  exact nk.toSpatialNeck.frontier_image_slab (by linarith) h11 (by norm_num)

def StrongNeck.toLocalNeck {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    LocalNeck S eps x t nk.region where
  strong := nk
  region_eq := rfl
  boundary_eq := nk.frontier_region

theorem canonicalAlternative_neck_of_strongNeck {eps : ℝ} {x : M} {t : ℝ} {C : ℝ}
    (nk : StrongNeck S eps x t) :
    Nonempty (CanonicalAlternative S eps C x t nk.region) :=
  ⟨CanonicalAlternative.neck nk.toLocalNeck⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
