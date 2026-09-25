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

/-!
# Polyhedral interpolation in toroidal shells

The proved assemblies give `Moise306` from `Moise252`, and `Moise307` from `Moise306` and
`Moise252`, using the seven open leaves below.  The combined endpoint takes only `Moise252`.
This is Moise 30.6--30.7, printed pages 216--218.  No use is made of 30.8 or of the approximation
theorems of Sections 31--35.

For 30.6, `IsToroidalShell.exists_separating_surface_bettiOne_eq_two` already supplies the
finite connected orientable separating surface, its injective fundamental-group map, Betti
number two and Euler characteristic zero.  Only orientable genus-one recognition remains
here.  For 30.7, `SurfaceFilling` constructs the bounded region of the separating surface.
`SurfaceEssentialDisk` produces the essential disk from the boundary Loop Theorem `Moise252`
inside the prescribed open set.  Its interior lies on one side of the surface by connectedness.
The exterior branch factors the inclusion of the inner solid torus through a contractible PL
ball and contradicts the shell inclusion.  The interior branch produces two PL balls meeting
in two boundary disks; the existing
`exists_cylindricalDiagram_of_ball_pair` then constructs the cylindrical diagram.

Open leaves, all owned by the torus lane, reviewed OK and frozen with proofs OPEN:

* `IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero`:
  a finite connected orientable closed surface of Euler characteristic zero is a torus.
* `IsPLTorus.exists_combinatorial_triangulation`: a polyhedral topological torus has a finite
  triangulation which is a connected combinatorial surface.
* `subset_interior_of_nested_tori`: the bounded region of the chosen separator lies between
  the given nested tori.  Its frontier and regular-closed certificate are retained explicitly.
* `IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus`: the map from the torus
  group to the fundamental group of the interior of a solid torus has a nontrivial kernel.
* `not_nullhomotopic_inclusion_of_nested_tori`: the shell makes the nested inclusion a homotopy
  equivalence, so the inclusion is not nullhomotopic.  This uses the shell retraction and the
  nontrivial fundamental group of a solid torus, not `Moise308Nested`.
* `exists_isPLBall_superset_of_exterior_compression`: an exterior essential compression of a
  torus boundary encloses its bounded region in a PL ball inside the prescribed open set.
* `exists_ball_pair_of_interior_essential_disk`: an interior essential compression gives the
  two-ball decomposition with two disjoint common boundary disks used by the cylindrical API.

The two compression leaves describe general torus regions and disks.  They do not take the
complete nested-shell data: an exterior compression has a nondegenerate local model even
though the exterior branch of 30.7 is impossible.  The region is the same finite complex from
`SurfaceFilling`, and the disk is the same existential witness returned by the proved
essential-disk theorem; neither is replaced by a free universal object.  No injectivity is
required on a closed path.

The first review and lead due diligence are recorded in
`consult/BC-section30-torus-first-review-digest.md`. The seven statements and all assemblies
are unchanged. Finite surface link recognition, the ambient-interior identification for a
topological solid torus, and the relative disk-neighborhood construction remain obligations.
Exterior compression must identify the same regular neighborhood chosen inside the prescribed
open set as a ball; containment of its boundary sphere alone does not control the filled ball.

Fixtures remain UNTESTED.  The tree's `exists_embedded_torus_compression` provides a genuine
polyhedral torus with a meridian and a capped sphere, but this file supplies no joint Lean
certificate for the nested-shell input, the bounded-region inclusions and the interior branch.
The exterior-compression leaf also needs its separate local fixture.  Empty surfaces are
excluded by connectedness or the torus homeomorphism; each disk
has a PL simplex parametrization and an essential boundary.  The recognition leaf keeps
orientability explicitly, excluding the Klein bottle.

The essential-disk theorem derives the needed orientable three-dimensional compression from
`Moise252`, so the unrestricted `Moise264` is not an additional input to these assemblies.
The cylindrical-diagram-to-cyclic-cell bridge needed by Section 31 remains in its own skeleton.
This file is not imported by the root aggregate or any other skeleton.

Proved and imported on 2026-09-22 (Gemini batch, lead-accepted with zero-diagnostic checks and an
axiom audit; statements byte-identical with the frozen leaves): `subset_interior_of_nested_tori`,
`not_nullhomotopic_inclusion_of_nested_tori`.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statements byte-identical with the frozen leaves): the three recognition
leaves — a closed orientable surface of Euler characteristic zero is a torus
(`TorusOfOrientableEulerCharZero`), a PL torus has a combinatorial triangulation
(`ExistsCombinatorialTriangulation`), and the inclusion of a PL torus into a solid torus has a
non-trivial kernel on fundamental groups (`NontrivialKernelInSolidTorus`). With `NestedTori`,
`moise306_of_moise252` is now proved from `Moise252`; only the two compression leaves remain.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statements byte-identical with the frozen leaves): the two compression leaves
(compressing the torus along the disk gives a PL sphere, filled by the unconditional PL
Schoenflies; the first Betti number of the torus is at most two). With them the file has no
`sorry` left: `moise306_of_moise252` and `moise307_of_moise252` are real proofs, and the module is
ready to be promoted out of `Skeleton/`.

Promoted out of `Skeleton/` on 2026-09-22: every former leaf is proved in an imported real module
(`NestedTori` from the Gemini batch; `TorusOfOrientableEulerCharZero`,
`ExistsCombinatorialTriangulation`, `NontrivialKernelInSolidTorus`,
`ExistsIsPLBallSupersetOfExteriorCompression`, `ExistsBallPairOfInteriorEssentialDisk` from Opus
5.5 workers), so `moise306_of_moise252` and `moise307_of_moise252` below are real proofs
conditional only on `Moise252`.  With `moise252` proved (`LoopTheorem/Moise252Producer`),
`moise306` and `moise307` hold without hypotheses.
-/

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
