import DifferentialGeometry.Topology.PiecewiseLinear.Section34SphereDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.exists_disk_chart_around_disk
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) :
    ∃ (Γ : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ ∧ Γ ⊆ K.space ∧
      D ⊆ r '' openSimplex (stdVertices 1) ∧
      p ∈ Γ \ r '' stdSimplexBoundary 2 ∧ p ∉ D ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ Γ ↔ y ∈ K.space := by
  classical
  obtain ⟨R, A, L, φ, ψ, hR, hRfin, hAR, hAfin, hAD, hLfin, hL, hIso, -⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar K hD hDK
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let N := PiecewiseLinear.derivedNeighborhood R A
  have hRM := hK.isCombinatorialManifoldWithBoundary.of_isSubdivision hR
  have hNball : IsPLBall 2 N.space :=
    hRM.isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface hAR hL hIso
  have hNK : N.space ⊆ K.space :=
    (derivedNeighborhood_space_subset R A).trans hR.space_eq.subset
  have hnhds : ∀ x ∈ D, N.space ∈ 𝓝[K.space] x := by
    intro x hx
    have h := derivedNeighborhood_mem_nhdsWithin hAR (hAD.symm ▸ hx)
    rwa [hR.space_eq] at h
  obtain ⟨r, hr⟩ := hNball
  have hDint : D ⊆ r '' openSimplex (stdVertices 1) := by
    rw [hr.image_openSimplex_stdVertices]
    intro x hx
    refine ⟨mem_of_mem_nhdsWithin (hDK hx) (hnhds x hx), ?_⟩
    intro hxbd
    have hbd := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK
    have hxcl := (hbd.superset hxbd).2
    obtain ⟨O, hO, hxO, hON⟩ := mem_nhdsWithin.mp (hnhds x hx)
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff_nhds.mp hxcl O (hO.mem_nhds hxO)
    exact hy.2 (hON ⟨hyO, hy.1⟩)
  obtain ⟨p, hpN, hpD⟩ :=
    hr.exists_interior_point_outside_closed_disk_subset hD.isPolyhedron.isClosed hDint
  refine ⟨N.space, r, p, hr, hNK, hDint, hpN, hpD, ?_⟩
  intro x hx
  obtain ⟨O, hO, hxO, hON⟩ := mem_nhdsWithin.mp (hnhds x hx)
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact ⟨fun hyN => hNK hyN, fun hyK => hON ⟨hy, hyK⟩⟩

theorem IsCombinatorialManifold.exists_disk_neighborhood_of_disk_subset
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {D Ω : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ (M : Set (EuclideanSpace ℝ (Fin 3)))
      (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M ∧ M ⊆ K.space ∩ Ω ∧
      D ⊆ r '' openSimplex (stdVertices 1) ∧
      ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ M ↔ y ∈ K.space := by
  obtain ⟨Γ, q, p, hq, hΓK, hDΓ, hpΓ, hpD, hag⟩ :=
    hK.exists_disk_chart_around_disk K hD hDK
  have hpc := hq.isPseudoCell_of_mem_interior hpΓ
  have hDE : D ⊆ (Γ \ q '' stdSimplexBoundary 2) \ {p} := by
    intro x hx
    exact ⟨hq.image_openSimplex_stdVertices ▸ hDΓ hx, fun hxp => hpD (hxp ▸ hx)⟩
  obtain ⟨M, r, hr, hMΓ, hMΩ, hDM, hMgerm⟩ := hpc.exists_disk_neighborhood hD hDE hΩ hDΩ
  refine ⟨M, r, hr, fun x hx => ⟨hΓK (hMΓ hx).1.1, hMΩ hx⟩, hDM, ?_⟩
  intro x hx
  filter_upwards [hMgerm x hx, hag x hx] with y h₁ h₂
  exact h₁.trans h₂

end DifferentialGeometry.Topology.PiecewiseLinear
