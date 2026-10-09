/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.Regions

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem eq_inside_of_isOpen_isBounded_frontier_subset
    {U J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hne : U.Nonempty)
    (hfront : frontier U ⊆ J) (hdis : Disjoint U J) : U = Schoenflies.inside J := by
  have hsub : U ⊆ Jᶜ := fun _ hx hxJ => disjoint_left.mp hdis hx hxJ
  have hcomponent (x : Schoenflies.Plane) (hx : x ∈ U) :
      connectedComponentIn Jᶜ x ⊆ U := by
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hU
      ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
    rintro y ⟨hycl, hycomp⟩
    by_contra hyU
    exact connectedComponentIn_subset _ _ hycomp
      (hfront (hU.frontier_eq.symm.subset ⟨hycl, hyU⟩))
  have hinside : U ⊆ Schoenflies.inside J :=
    fun x hx => ⟨hsub hx, hbounded.subset (hcomponent x hx)⟩
  obtain ⟨x, hx⟩ := hne
  exact hinside.antisymm
    (((Schoenflies.jordan_curve_theorem hJ).connectedComponentIn_eq_inside (hinside
        hx)).symm.subset.trans
      (hcomponent x hx))

end DifferentialGeometry.Topology.PlanarJordan
