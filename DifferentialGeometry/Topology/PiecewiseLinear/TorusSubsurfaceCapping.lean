/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubsurfaceDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFixedBallAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCircleCapping.exists_subsurface_of_essential_boundary [d : DecidableEq E3]
    (K Q R : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hQ : IsCombinatorialManifoldWithBoundary 2 Q) (hQconn : IsConnected Q.space)
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRconn : IsPreconnected R.space)
    {T Θ : Set E3} (hΘ : IsPLTorus Θ) (hRΘ : R.space ⊆ Θ)
    {f : E3 → E3} (hf : IsPLHomeomorphOn f R.space K.space)
    (hboundary : (boundaryComplex 2 R).space = (boundaryComplex 2 K).space)
    (hfix : EqOn f id (boundaryComplex 2 R).space)
    (hcap : IsCircleCapping K.space Q.space T (boundaryComplex 2 K).space)
    (hnull : ∀ G ∈ traceCircles K.space T, boundsDiskIn G T → boundsDiskIn G Θ)
    {H : Set E3} (hH : IsPLSphere 1 H) (hHQ : H ⊆ (boundaryComplex 2 Q).space)
    (hess : ¬ boundsDiskIn H Θ) :
    ∃ R' : Geometry.SimplicialComplex ℝ E3, R'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 R' ∧ IsConnected R'.space ∧ R'.space ⊆ Θ ∧
      (boundaryComplex 2 R').space = (boundaryComplex 2 Q).space ∧
      ∃ g : E3 → E3, IsPLHomeomorphOn g R'.space Q.space ∧
        EqOn g id (boundaryComplex 2 R').space := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Δ, r, g, hr, hΔT, hmeet, hG, hGb, hg, hgfix, hQb⟩ :=
    hcap.exists_boundary_preserving_map K Q hK
  obtain ⟨D, s, hs, hDΘ, hrims⟩ := hnull _ hG ⟨Δ, r, hr, hΔT, rfl⟩
  have hsb : s '' stdSimplexBoundary 2 ⊆ (boundaryComplex 2 R).space := by
    rw [← hrims, hboundary]
    exact hGb
  have hHR : H ⊆ R.space := fun x hx => boundaryComplex_space_subset 2 R
    (hboundary.symm.subset (hQb.subset (hHQ hx)).1)
  have hHJ : Disjoint H (s '' stdSimplexBoundary 2) := by
    rw [← hrims]
    exact disjoint_left.mpr fun x hxH hxG => (hQb.subset (hHQ hxH)).2 hxG
  obtain ⟨A, hAfin, hA, -, hAΘ⟩ := hΘ.exists_combinatorial_triangulation
  let _ : Finite A.faces := hAfin.to_subtype
  have hRD : R.space ∩ D = s '' stdSimplexBoundary 2 :=
    hR.inter_disk_eq_of_essential_circle A R hA hRconn (hRΘ.trans hAΘ.symm.subset)
      hs (hDΘ.trans hAΘ.symm.subset) hsb hH hHR hHJ (by
        rintro ⟨D', q, hq, hD'A, hHq⟩
        exact hess ⟨D', q, hq, hD'A.trans hAΘ.subset, hHq⟩)
  have hgfixR : EqOn g id ((boundaryComplex 2 R).space \ s '' stdSimplexBoundary 2) := by
    rw [hboundary, ← hrims]
    exact hgfix
  have hQbR : (boundaryComplex 2 Q).space =
      (boundaryComplex 2 R).space \ s '' stdSimplexBoundary 2 := by
    rw [hboundary, ← hrims]
    exact hQb
  obtain ⟨R', hR'fin, hR', hR'conn, hR'space, hR'b, k, hk, hkfix⟩ :=
    hf.exists_manifold_union_ball_fixed_boundary R Q hQ hQconn hfix hs hr hrims hRD
      (hmeet.trans hrims) hsb hg hgfixR hQbR
  exact ⟨R', hR'fin, hR', hR'conn, hR'space.subset.trans (union_subset hRΘ hDΘ),
    hR'b, k, hk, hkfix⟩

end DifferentialGeometry.Topology.PiecewiseLinear
