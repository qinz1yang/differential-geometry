/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Finite polyhedral neighborhoods containing nullhomotopies
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_neighborhood_fundamentalGroup_map_eq_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (x : S) (g : FundamentalGroup S x)
    (hg : FundamentalGroup.map (⟨Set.inclusion hSU, continuous_inclusion hSU⟩ :
      C(S, U)) x g = 1) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧
      S ⊆ interior N.space ∧ N.space ⊆ U ∧
      ∀ hSN : S ⊆ N.space,
        FundamentalGroup.map (⟨Set.inclusion hSN, continuous_inclusion hSN⟩ :
          C(S, N.space)) x g = 1 := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  change Path.Homotopic.Quotient.mk (p.map (continuous_inclusion hSU)) =
    Path.Homotopic.Quotient.mk (Path.refl (Set.inclusion hSU x)) at hg
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hg
  let C : Set E := S ∪ range (fun t : unitInterval × unitInterval => (H t : E))
  have hC : IsCompact C := hS.union
    (isCompact_range (continuous_subtype_val.comp H.continuous))
  have hCU : C ⊆ U := by
    rintro y (hy | ⟨t, rfl⟩)
    · exact hSU hy
    · exact (H t).property
  obtain ⟨N, hNfin, hN, hCN, hNU⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood hdim hC hU hCU
  refine ⟨N, hNfin, hN, (subset_union_left : S ⊆ C).trans hCN, hNU, ?_⟩
  intro hSN
  change Path.Homotopic.Quotient.mk (p.map (continuous_inclusion hSN)) =
    Path.Homotopic.Quotient.mk (Path.refl (Set.inclusion hSN x))
  apply Path.Homotopic.Quotient.eq.mpr
  refine ⟨{
    toFun := fun t => ⟨(H t : E), interior_subset (hCN (Or.inr ⟨t, rfl⟩))⟩
    continuous_toFun := (continuous_subtype_val.comp H.continuous).subtype_mk _
    map_zero_left := fun t => Subtype.ext
      (congrArg (fun z : U => (z : E)) (H.apply_zero t))
    map_one_left := fun t => Subtype.ext
      (congrArg (fun z : U => (z : E)) (H.apply_one t))
    prop' := fun t y hy => Subtype.ext
      (congrArg (fun z : U => (z : E)) (H.eq_fst t hy))
  }⟩

theorem exists_neighborhood_fundamentalGroup_map_eq_one_of_simplyConnectedSpace {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) [SimplyConnectedSpace U]
    (x : S) (g : FundamentalGroup S x) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧
      S ⊆ interior N.space ∧ N.space ⊆ U ∧
      ∀ hSN : S ⊆ N.space,
        FundamentalGroup.map (⟨Set.inclusion hSN, continuous_inclusion hSN⟩ :
          C(S, N.space)) x g = 1 :=
  exists_neighborhood_fundamentalGroup_map_eq_one hdim hS hU hSU x g
    (Subsingleton.elim _ _)

end DifferentialGeometry.Topology.PiecewiseLinear
