import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelRegionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeInwardMotion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_target_inward_motion
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P)
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAP : A.space ⊆ interior P)
    {Z O : Set M} (hZ : IsCompact Z) (hZB : Z ⊆ frontier (u '' A.space))
    (hO : IsOpen O) (hOcompact : IsCompact (closure O))
    (hZO : Z ⊆ O) (hOP : closure O ⊆ interior (u '' P)) :
    ∃ ψ : M ≃ₜ M, EqOn ψ id Oᶜ ∧ IsPLOn 3 3 ψ (interior (u '' P)) ∧
      MapsTo ψ (u '' A.space) (u '' A.space) ∧
      MapsTo ψ Z (interior (u '' A.space)) ∧
      ∀ x ∈ u '' A.space, ψ x ∈ frontier (u '' A.space) → ψ x = x := by
  let τ := Function.invFunOn u P
  let C := τ '' closure O
  let Z' := τ '' Z
  let O' := interior P ∩ u ⁻¹' O
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hAcompact := (isPolyhedron_space A).isCompact
  have hTcompact : IsCompact (u '' A.space) :=
    hAcompact.image_of_continuousOn (hu.continuousOn.mono (hAP.trans interior_subset))
  have hfront := hu.image_frontier_of_isCompact_subset_interior hAcompact hAP
  have hinterior := hu.image_interior_of_isCompact_subset_interior hAcompact hAP
  have hTP : u '' A.space ⊆ interior (u '' P) := by
    rw [← hu.image_interior]
    exact image_mono hAP
  have hZP : Z ⊆ interior (u '' P) :=
    hZB.trans (hTcompact.isClosed.frontier_subset.trans hTP)
  obtain ⟨hC, hCP, hbackC, -, -⟩ := hu.invFunOn_region_topology hOcompact hOP
  obtain ⟨hZ', hZ'P, hbackZ, -, -⟩ := hu.invFunOn_region_topology hZ hZP
  have hZ'B : Z' ⊆ frontier A.space := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hfront.symm.subset (hZB hx)
    rw [hleft (hAP.trans interior_subset (hAcompact.isClosed.frontier_subset hy))]
    exact hy
  have hO' : IsOpen O' :=
    (hu.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior hO
  have hZ'O : Z' ⊆ O' := by
    intro x hx
    refine ⟨hZ'P hx, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    change u (τ y) ∈ O
    rw [hright (interior_subset (hZP hy))]
    exact hZO hy
  have hOC : O' ⊆ C := by
    intro x hx
    exact ⟨u x, subset_closure hx.2, hleft (interior_subset hx.1)⟩
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    (hKspace.symm ▸ hP).isCombinatorialManifoldWithBoundary
  obtain ⟨φ, hφ, hfix, hmap, hpush, hboundary⟩ :=
    hK.exists_inward_homeomorph hA (hKspace.symm ▸ hAP) hZ' hZ'B hO' hZ'O
      (hKspace.symm ▸ inter_subset_left)
  have hfixC : EqOn φ id Cᶜ := hfix.mono (compl_subset_compl.mpr hOC)
  obtain ⟨ψ, hψfix, hconj, hψpl⟩ :=
    hu.exists_supported_model_motion hP.isPolyhedron hC hCP φ hφ hfixC
  refine ⟨ψ, ?_, hψpl, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxP : x ∈ u '' P
    · obtain ⟨y, hy, rfl⟩ := hxP
      rw [hconj y hy, hfix (fun hmem => hx hmem.2)]
      rfl
    · exact hψfix (fun hmem => hxP (image_mono (hCP.trans interior_subset) hmem))
  · rintro _ ⟨x, hx, rfl⟩
    rw [hconj x (hAP.trans interior_subset hx)]
    exact ⟨φ x, hmap hx, rfl⟩
  · intro x hx
    have hx' : τ x ∈ Z' := ⟨x, hx, rfl⟩
    have heq : x = u (τ x) := (hright (interior_subset (hZP hx))).symm
    rw [heq, hconj (τ x) (interior_subset (hZ'P hx'))]
    exact hinterior ▸ ⟨φ (τ x), hpush hx', rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hψx
    rw [hconj x (hAP.trans interior_subset hx)] at hψx ⊢
    obtain ⟨y, hy, heq⟩ := hfront.symm.subset hψx
    have hxy : y = φ x := hu.injOn
      (hAP.trans interior_subset (hAcompact.isClosed.frontier_subset hy))
      (hAP.trans interior_subset (hmap hx)) heq
    rw [hboundary x hx (hxy ▸ hy)]

end DifferentialGeometry.Topology.PiecewiseLinear
