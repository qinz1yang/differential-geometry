import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsBallPairOfInteriorEssentialDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cylindrical_model_of_interior_essential_disk
    {P : Set E} (hP : IsPLBall 2 P) (hdim : Module.finrank ℝ E = 2)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hT : IsPLTorus (frontier R.space))
    {D : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDR : D ⊆ R.space)
    (hmeet : D ∩ frontier R.space = r '' stdSimplexBoundary 2)
    (hess : ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨inclusion hboundary, continuous_inclusion hboundary⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic) :
    IsTopologicalSolidTorus R.space ∧
      ∃ f : E × ℝ → EuclideanSpace ℝ (Fin 3), IsCylindricalDiagram f P R.space ∧
        (∀ x ∈ P, f (x, 0) = f (x, 1)) ∧
        frontier R.space = f '' (frontier P ×ˢ Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hunion, D₀, D₁, hD₀, hD₁, hdis,
    hD₀A, hD₁A, hD₀B, hD₁B, hinter⟩ :=
    exists_ball_pair_of_interior_essential_disk R hR hT hr hDR hmeet hess
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hfrontA := frontier_space_eq_boundaryComplex_space_of_finrank
    (d := Classical.decEq _) (by simp) A hA.isCombinatorialManifoldWithBoundary
  have hfrontB := frontier_space_eq_boundaryComplex_space_of_finrank
    (d := Classical.decEq _) (by simp) B hB.isCombinatorialManifoldWithBoundary
  rw [hfrontA] at hD₀A hD₁A
  rw [hfrontB] at hD₀B hD₁B
  obtain ⟨g₀, hg₀⟩ := hD₀
  obtain ⟨p, hp⟩ := hP
  obtain ⟨f₀, hf₀, -⟩ := exists_cylindricalDiagram_of_ball_pair (show IsPLBall 2 P from ⟨p, hp⟩)
    A B hA hB hD₁ hdis hD₀A hD₁A hD₀B hD₁B hinter (hp.symm.trans hg₀)
  rw [hunion] at hf₀
  obtain ⟨T, -, hTcard, hRT⟩ := exists_affineIndependent_openSimplex_superset 3 (by simp)
    (isPolyhedron_space R).isCompact.isBounded
  have hor : IsOrientable 3 R := isOrientable_of_space_subset_convexHull R hR T hTcard
    (hRT.trans (openSimplex_subset_convexHull T))
  have hP : IsPLBall 2 P := ⟨p, hp⟩
  obtain ⟨f, hf, hends⟩ := hf₀.exists_endMap_id_of_isOrientable hP R hR hor
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hP
  have hfK : IsCylindricalDiagram f K.space R.space := hKspace.symm ▸ hf
  have hfront := hfK.frontier_eq_image_side K R hK hR (by simp)
  have hKfront := frontier_space_eq_boundaryComplex_space_of_finrank
    (d := Classical.decEq _) hdim K
    hK.isCombinatorialManifoldWithBoundary
  rw [← hKfront, hKspace] at hfront
  exact ⟨hf.isTopologicalSolidTorus_of_eq_ends hP hends, f, hf, hends, hfront⟩

theorem exists_cylindrical_model_of_essential_disk_and_carrier
    {P : Set E} (hP : IsPLBall 2 P) (hdim : Module.finrank ℝ E = 2)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S J : Set M}
    (hS : IsTopologicalSolidTorus S) (hJ : CarriesFundamentalGroupOnto J S)
    (hne : J.Nonempty)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hT : IsPLTorus (frontier R.space))
    {V D : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hV : IsOpen V) (hu : IsPLHomeomorphInto 3 u V) (hRV : R.space ⊆ V)
    (hVS : u '' V ⊆ S) (hJR : J ⊆ u '' R.space)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDV : D ⊆ V)
    (hmeet : D ∩ frontier R.space = r '' stdSimplexBoundary 2)
    (hess : ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨inclusion hboundary, continuous_inclusion hboundary⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic) :
    D ⊆ R.space ∧ IsTopologicalSolidTorus R.space ∧ IsTopologicalSolidTorus (u '' R.space) ∧
      ∃ f : E × ℝ → EuclideanSpace ℝ (Fin 3), IsCylindricalDiagram f P R.space ∧
        (∀ x ∈ P, f (x, 0) = f (x, 1)) ∧
        frontier R.space = f '' (frontier P ×ˢ Icc (0 : ℝ) 1) := by
  have hclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hside : D \ r '' stdSimplexBoundary 2 ⊆ interior R.space ∨
      D \ r '' stdSimplexBoundary 2 ⊆ R.spaceᶜ := by
    apply hr.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected.subset_or_subset
      isOpen_interior hclosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxR : x ∈ R.space
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxR).mpr
        (fun hxfront => hx.2 (hmeet.subset ⟨hx.1, hxfront⟩)))
    · exact Or.inr hxR
  have hinside := hside.resolve_right (hS.not_exterior_compression_of_carrier hJ hne
    R hR hT hV hu hRV hVS hJR hr hDV hmeet hess)
  have hDR : D ⊆ R.space := by
    intro x hx
    by_cases hxend : x ∈ r '' stdSimplexBoundary 2
    · exact hclosed.frontier_subset (hmeet.symm.subset hxend).2
    · exact interior_subset (hinside ⟨hx, hxend⟩)
  obtain ⟨hsolid, f, hf, hends, hfront⟩ :=
    exists_cylindrical_model_of_interior_essential_disk hP hdim R hR hT hr hDR hmeet hess
  exact ⟨hDR, hsolid, hsolid.image_of_continuousOn_injOn (hu.continuousOn.mono hRV)
    (hu.injOn.mono hRV), f, hf, hends, hfront⟩

end DifferentialGeometry.Topology.PiecewiseLinear
