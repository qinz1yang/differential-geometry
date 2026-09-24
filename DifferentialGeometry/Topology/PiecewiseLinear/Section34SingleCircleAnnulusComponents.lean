import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusLocalConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleBicollar
import DifferentialGeometry.Topology.Connected.BicollarSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_connected_pair_cover_annulus_sdiff_circle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ J : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (hJ : IsPLSphere 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    ∃ L R : Set E, IsConnected L ∧ IsConnected R ∧ L ∪ R = A \ J := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_two
  let _ := hchart
  let _ := hA.locallyConnectedSpace
  have hA' := hA.preimage_subtype hAS
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : S → E) ⁻¹' A)))
  have hJO : J ⊆ O := by
    intro x hx
    have hxA : (⟨x, hAS (hJA hx)⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' A := hJA hx
    have hxint := (mem_interior_iff_notMem_frontier hxA).mpr fun hfr =>
      disjoint_left.mp hends hx (hA'.frontier_subset hfr)
    exact show (⟨x, hAS (hJA hx)⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' O from
      hOeq.symm ▸ hxint
  have hOA : O ∩ S ⊆ A := by
    rintro x ⟨hxO, hxS⟩
    have hx : (⟨x, hxS⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' O := hxO
    have hxint : (⟨x, hxS⟩ : S) ∈ interior ((Subtype.val : S → E) ⁻¹' A) :=
      hOeq ▸ hx
    exact show (⟨x, hxS⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' A from
      interior_subset hxint
  obtain ⟨W, ρ, -, -, hWO, hW, hρ, hzero⟩ :=
    hS.exists_bicollar_of_isPLSphere_one hJ (hJA.trans hAS)
      (mem_nhdsSetWithin.mpr ⟨O, hO, hJO, hOA⟩)
  have hWA : W ⊆ A := hWO
  have hW' : W ∈ 𝓝ˢ[A] J := nhdsSetWithin_mono_right hAS hW
  obtain ⟨a, ha, b, hb, hpair⟩ :=
    DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_bicollar
      hA.isConnected.isPreconnected hJ.isConnected hJ.isPolyhedron.isClosed hWA hW'
      hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero
  refine ⟨connectedComponentIn (A \ J) a, connectedComponentIn (A \ J) b,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb, ?_⟩
  apply Subset.antisymm
    (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
  intro x hx
  rcases hpair x hx with hxa | hxb
  · exact Or.inl (hxa ▸ mem_connectedComponentIn hx)
  · exact Or.inr (hxb ▸ mem_connectedComponentIn hx)

theorem IsPLCellOn.exists_connected_pair_cover_annulus_sdiff_circle {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) :
    ∃ L R : Set M, IsConnected L ∧ IsConnected R ∧ L ∪ R = A \ J := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  have hJP : J ⊆ u '' P := hJA.trans hAP
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hJ' : IsPLSphere 1 (τ '' J) := hu.isPLSphere_invFunOn_image hJ hJP
  have hends' : Disjoint (τ '' J) ((τ '' A₀) ∪ (τ '' A₁)) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyP := hAP ((union_subset hA.first_subset hA.second_subset) hy)
    exact disjoint_left.mp hends hx (hτi (hJP hx) hyP hxy.symm ▸ hy)
  obtain ⟨L, R, hL, hR, hLR⟩ :=
    hP.isPLSphere_frontier.exists_connected_pair_cover_annulus_sdiff_circle
      hA' hA'S hJ' (image_mono hJA) hends'
  have hsub : L ∪ R ⊆ P := hLR ▸ sdiff_subset.trans (hA'S.trans hfront)
  refine ⟨u '' L, u '' R,
    hL.image u (hu.continuousOn.mono (subset_union_left.trans hsub)),
    hR.image u (hu.continuousOn.mono (subset_union_right.trans hsub)), ?_⟩
  rw [← image_union, hLR, ← (hτi.mono hAP).image_sdiff_subset hJA, image_image]
  exact (image_congr fun x hx => hright (hAP hx.1)).trans (image_id' (A \ J))

end DifferentialGeometry.Topology.PiecewiseLinear
