import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import DifferentialGeometry.Topology.Manifold.CylinderSlabBoundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

open private slab_boundary_chart slab_lower_boundary_chart from DifferentialGeometry.Topology.Manifold.CylinderSlabBoundary

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem exists_compactDomain_of_cylinder_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]
    (F : PartialDiffeomorph IC I3 Cylinder M ∞) {a b : ℝ} (hab : a < b)
    (hsrc : univ ×ˢ Icc a b ⊆ F.source) :
    ∃ K : CompactDomain M, K.carrier = F '' (univ ×ˢ Icc a b) := by
  let U : Set Cylinder := univ ×ˢ Ioo a b
  let B : Set Cylinder := univ ×ˢ Icc a b
  have hUc : closure U = B := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  have hUB : U ⊆ B := prod_mono subset_rfl Ioo_subset_Icc_self
  have hBc : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hFc : IsCompact (F '' B) :=
    hBc.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hsrc)
  let : ConnectedSpace (Sphere 2) := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  have hconnected : IsConnected B := isConnected_univ.prod
    ((convex_Icc a b).isConnected ⟨a, le_rfl, hab.le⟩)
  have hregular : closure (interior (F '' B)) = F '' B := by
    apply subset_antisymm
    · exact closure_minimal interior_subset hFc.isClosed
    · have hFUopen : IsOpen (F '' U) := DifferentialGeometry.image_opens_isOpen F
        (U := ⟨U, isOpen_univ.prod isOpen_Ioo⟩) (hUB.trans hsrc)
      have hFUi : F '' U ⊆ interior (F '' B) :=
        interior_maximal (image_mono hUB) hFUopen
      have hcont : ContinuousOn F (closure U) := by
        rw [hUc]
        exact F.contMDiffOn_toFun.continuousOn.mono hsrc
      have hh : F '' closure U ⊆ closure (F '' U) := hcont.image_closure
      rw [hUc] at hh
      exact hh.trans (closure_mono hFUi)
  refine ⟨{ carrier := F '' B
            compact := hFc
            connected := hconnected.image F (F.contMDiffOn_toFun.continuousOn.mono hsrc)
            regular_closed := hregular
            boundary_chart := ?_ }, rfl⟩
  intro x hx
  have hf : frontier (F '' B) = F '' (univ ×ˢ ({a, b} : Set ℝ)) :=
    frontier_image_univ_prod_Icc hab.le F hsrc hFc.isClosed
  rw [hf] at hx
  obtain ⟨⟨p, z⟩, hz, rfl⟩ := hx
  rcases (show z = a ∨ z = b from hz.2) with rfl | rfl
  · exact slab_lower_boundary_chart F hab hsrc p
  · exact slab_boundary_chart F hab hsrc p

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}

theorem StrongNeck.exists_compactDomain_region (nk : StrongNeck S eps x t) :
    ∃ K : CompactDomain M, K.carrier = nk.region ∧ x ∈ interior K.carrier := by
  have hsmall : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  have hsrc : univ ×ˢ Icc (-10 : ℝ) 10 ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨K, hK⟩ := exists_compactDomain_of_cylinder_slab nk.map
    (by norm_num : (-10 : ℝ) < 10) hsrc
  have hU : IsOpen (nk.map '' (univ ×ˢ Ioo (-10 : ℝ) 10)) :=
    DifferentialGeometry.image_opens_isOpen nk.map
      (U := ⟨univ ×ˢ Ioo (-10 : ℝ) 10, isOpen_univ.prod isOpen_Ioo⟩)
      ((prod_mono subset_rfl Ioo_subset_Icc_self).trans hsrc)
  refine ⟨K, hK, ?_⟩
  rw [hK]
  apply interior_maximal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)) hU
  exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ} {U : Set M}

omit [SigmaCompactSpace M] in
theorem LocalCap.exists_compactDomain (cap : LocalCap S eps x t U) :
    ∃ K : CompactDomain M, K.carrier = U ∧ x ∈ interior K.carrier := by
  obtain ⟨T, hT⟩ := exists_compactDomain_of_cylinder_slab cap.tubeMap
    (by norm_num : (0 : ℝ) < 1) cap.tube_domain
  have hTtube : T.carrier = cap.tube := hT.trans cap.tube_eq
  have hU : U = cap.core.carrier ∪ T.carrier := by rw [hTtube]; exact cap.union_eq
  have hinter : (cap.core.carrier ∩ T.carrier).Nonempty := by
    let p : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    have hp : cap.tubeMap (p, 0) ∈ frontier cap.core.carrier := by
      rw [← cap.inner_boundary]
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    rw [hTtube, cap.overlap_eq]
    exact ⟨_, hp⟩
  have hc : IsCompact U := cap.isCompact_carrier
  have hcoreU : cap.core.carrier ⊆ U := cap.core_inside.trans interior_subset
  have htubeU : T.carrier ⊆ U := fun z hz => hU.symm ▸ Or.inr hz
  have hregular : closure (interior U) = U := by
    apply subset_antisymm (closure_minimal interior_subset hc.isClosed)
    intro z hz
    have hz' : z ∈ cap.core.carrier ∪ T.carrier := hU ▸ hz
    rcases hz' with hz' | hz'
    · exact (closure_mono (interior_mono hcoreU)) (cap.core.regular_closed.symm ▸ hz')
    · exact (closure_mono (interior_mono htubeU)) (T.regular_closed.symm ▸ hz')
  refine ⟨{ carrier := U
            compact := hc
            connected := by rw [hU]; exact IsConnected.union hinter cap.core.connected T.connected
            regular_closed := hregular
            boundary_chart := ?_ }, rfl, cap.core_inside (interior_subset cap.center_inside)⟩
  intro y hy
  have hyt : y ∈ frontier T.carrier := by
    rw [hTtube, cap.boundary_eq]
    exact Or.inr hy
  obtain ⟨F, hyF, hzero, hside⟩ := T.boundary_chart y hyt
  have hycore : y ∉ cap.core.carrier := by
    intro hc
    exact disjoint_interior_frontier.le_bot ⟨cap.core_inside hc, hy⟩
  let F' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict F
    cap.core.carrierᶜ cap.core.compact.isClosed.isOpen_compl
  refine ⟨F', ⟨hyF, hycore⟩, hzero, ?_⟩
  intro z hz
  change z ∈ U ↔ F z 0 ≤ 0
  rw [hU, mem_union]
  constructor
  · rintro (hcore | htube)
    · exact (hz.2 hcore).elim
    · exact (hside z hz.1).mp htube
  · intro h
    exact Or.inr ((hside z hz.1).mpr h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
