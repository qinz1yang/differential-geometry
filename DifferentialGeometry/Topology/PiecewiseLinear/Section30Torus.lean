/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEssentialDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShellHomology
import DifferentialGeometry.Topology.PiecewiseLinear.NestedTori
import DifferentialGeometry.Topology.PiecewiseLinear.TorusOfOrientableEulerCharZero
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.NontrivialKernelInSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsBallPairOfInteriorEssentialDisk
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise252Producer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise306_of_moise252 (h252 : Moise252) : Moise306 := by
  intro Y T₀ T₁ hY
  obtain ⟨L, hLfin, hL, hLc, hLo, -, hsep, -, -, hχ, hLY, -⟩ :=
    hY.exists_separating_surface_bettiOne_eq_two h252
  let _ : Finite L.faces := hLfin.to_subtype
  exact ⟨L.space, ⟨isPolyhedron_space L,
    hL.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero L hLc hLo hχ⟩,
    hLY, hsep⟩

theorem moise307_of_moise306_of_moise252 (h306 : Moise306) (h252 : Moise252) : Moise307 := by
  classical
  intro S₁ S₂ hS₁ hS₂ h₁₂ hshell
  obtain ⟨T, hT, hTshell, hsep⟩ := h306 _ _ _ hshell
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  subst T
  obtain ⟨R, hRfin, hR, -, hfront, hreg, hint, hext⟩ :=
    hL.exists_isCombinatorialManifoldWithBoundary_boundaryComplex L (by simp) hLc
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨h₁R, hR₂⟩ := subset_interior_of_nested_tori hS₁ hS₂ h₁₂ hshell hTshell hsep
    R hfront hreg hint hext
  have hS₂compact : IsCompact S₂ := by
    obtain ⟨e⟩ := hS₂
    let _ : CompactSpace S₂ := e.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hT₂ : L.space ⊆ interior S₂ :=
    hTshell.trans (interior_mono (closure_minimal sdiff_subset hS₂compact.isClosed))
  obtain ⟨x, g, hg, hnull⟩ :=
    hT.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus hS₂ hT₂
  obtain ⟨D, r, hr, hD₂, hmeet, hboundary, hess⟩ :=
    IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_fundamentalGroup_map_eq_one
      h252 L hL (by simp) hLc isOpen_interior hT₂ x g hg hnull
  have hmeetR : D ∩ frontier R.space = r '' stdSimplexBoundary 2 := by
    rwa [hfront]
  have hessR : ∃ hJ : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨Set.inclusion hJ, continuous_inclusion hJ⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic := by
    rw [hfront]
    exact ⟨hboundary, hess⟩
  have htorusR : IsPLTorus (frontier R.space) := hfront.symm ▸ hT
  have hside : D \ r '' stdSimplexBoundary 2 ⊆ interior R.space ∨
      D \ r '' stdSimplexBoundary 2 ⊆ R.spaceᶜ := by
    apply hr.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected.subset_or_subset
      isOpen_interior (isPolyhedron_space R).isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro y hy
    by_cases hyR : y ∈ R.space
    · exact Or.inl ((mem_interior_iff_notMem_frontier hyR).mpr
        (fun hyfront => hy.2 (hmeetR.subset ⟨hy.1, hyfront⟩)))
    · exact Or.inr hyR
  rcases hside with hDin | hDout
  · have hDR : D ⊆ R.space := by
      intro y hy
      by_cases hybd : y ∈ r '' stdSimplexBoundary 2
      · exact (isPolyhedron_space R).isClosed.frontier_subset
          (hmeetR.symm.subset hybd).2
      · exact interior_subset (hDin ⟨hy, hybd⟩)
    obtain ⟨A, B, hAfin, hBfin, hA, hB, hunion, D₀, D₁, hD₀, hD₁, hdis,
      hD₀A, hD₁A, hD₀B, hD₁B, hinter⟩ :=
      exists_ball_pair_of_interior_essential_disk R hR htorusR hr hDR hmeetR hessR
    let _ : Finite A.faces := hAfin.to_subtype
    let _ : Finite B.faces := hBfin.to_subtype
    have hfrontA := frontier_space_eq_boundaryComplex_space_of_finrank
      (d := Classical.decEq _) (by simp) A hA.isCombinatorialManifoldWithBoundary
    have hfrontB := frontier_space_eq_boundaryComplex_space_of_finrank
      (d := Classical.decEq _) (by simp) B hB.isCombinatorialManifoldWithBoundary
    rw [hfrontA] at hD₀A hD₁A
    rw [hfrontB] at hD₀B hD₁B
    obtain ⟨g₀, hg₀⟩ := hD₀
    obtain ⟨f, hf, -⟩ := exists_cylindricalDiagram_of_ball_pair (isPLBall_stdSimplex 2)
      A B hA hB hD₁ hdis hD₀A hD₁A hD₀B hD₁B hinter hg₀
    exact ⟨R.space, ⟨f, hunion ▸ hf⟩, h₁R, hR₂⟩
  · obtain ⟨B, hB, hRB, hB₂⟩ := exists_isPLBall_superset_of_exterior_compression
      R hR htorusR isOpen_interior hR₂ hr hD₂ hmeetR hessR hDout
    have h₁B : S₁ ⊆ B :=
      (h₁R.trans interior_subset).trans (hRB.trans interior_subset)
    let i : C(S₁, B) := ⟨Set.inclusion h₁B, continuous_inclusion h₁B⟩
    let j : C(B, S₂) :=
      ⟨Set.inclusion (hB₂.trans interior_subset), continuous_inclusion _⟩
    let _ := hB.contractibleSpace
    have hnull : (j.comp i).Nullhomotopic :=
      ((id_nullhomotopic B).comp_right j).comp_left i
    have heq : j.comp i = (⟨Set.inclusion (h₁₂.trans interior_subset),
        continuous_inclusion _⟩ : C(S₁, S₂)) := by
      ext y
      rfl
    rw [heq] at hnull
    exact (not_nullhomotopic_inclusion_of_nested_tori hS₁ hS₂ h₁₂ hshell hnull).elim

theorem moise307_of_moise252 (h252 : Moise252) : Moise307 := by
  exact moise307_of_moise306_of_moise252 (moise306_of_moise252 h252) h252

theorem moise306 : Moise306 :=
  moise306_of_moise252 moise252

theorem moise307 : Moise307 :=
  moise307_of_moise252 moise252

end DifferentialGeometry.Topology.PiecewiseLinear
