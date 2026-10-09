/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface
import DifferentialGeometry.Topology.PiecewiseLinear.ConnectedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FreeLoopFilling
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

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

theorem exists_connected_neighborhood_fundamentalGroup_map_eq_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {S U : Set E}
    (hS : IsCompact S) (hconn : IsConnected S) (hU : IsOpen U) (hSU : S ⊆ U)
    (x : S) (g : FundamentalGroup S x)
    (hg : FundamentalGroup.map (⟨Set.inclusion hSU, continuous_inclusion hSU⟩ :
      C(S, U)) x g = 1) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧ IsConnected N.space ∧
      S ⊆ interior N.space ∧ N.space ⊆ U ∧
      ∀ hSN : S ⊆ N.space,
        FundamentalGroup.map (⟨Set.inclusion hSN, continuous_inclusion hSN⟩ :
          C(S, N.space)) x g = 1 := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  change Path.Homotopic.Quotient.mk (p.map (continuous_inclusion hSU)) =
    Path.Homotopic.Quotient.mk (Path.refl (Set.inclusion hSU x)) at hg
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hg
  let f : unitInterval × unitInterval → E := fun t => (H t : E)
  have hf : Continuous f := continuous_subtype_val.comp H.continuous
  let C := S ∪ range f
  have hC : IsCompact C := hS.union (isCompact_range hf)
  have hCc : IsConnected C := hconn.union (by
    refine ⟨(p 0).val, (p 0).property, (0, 0), ?_⟩
    exact congrArg (fun z : U => z.val) (H.apply_zero 0)) (isConnected_range hf)
  have hCU : C ⊆ U := by
    rintro y (hy | ⟨t, rfl⟩)
    · exact hSU hy
    · exact (H t).property
  obtain ⟨M, hMfin, hM, hCM, _⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood hdim hC hU hCU
  let _ : Finite M.faces := hMfin.to_subtype
  obtain ⟨N, hNfin, hN, hNc, _, hNU, hCN⟩ :=
    hM.exists_connected_neighborhood hC hCc (hCM.trans interior_subset)
      (mem_nhdsSetWithin.mpr ⟨U, hU, hCU, inter_subset_left⟩)
  have hCNint : C ⊆ interior N.space := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have h := hCN y hy
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hCM hy))] at h
  refine ⟨N, hNfin, hN, hNc, subset_union_left.trans hCNint, hNU, ?_⟩
  intro hSN
  change Path.Homotopic.Quotient.mk (p.map (continuous_inclusion hSN)) =
    Path.Homotopic.Quotient.mk (Path.refl (Set.inclusion hSN x))
  apply Path.Homotopic.Quotient.eq.mpr
  refine ⟨{
    toFun := fun t => ⟨f t, interior_subset (hCNint (Or.inr ⟨t, rfl⟩))⟩
    continuous_toFun := hf.subtype_mk _
    map_zero_left := fun t => Subtype.ext
      (congrArg (fun z : U => z.val) (H.apply_zero t))
    map_one_left := fun t => Subtype.ext
      (congrArg (fun z : U => z.val) (H.apply_one t))
    prop' := fun t y hy => Subtype.ext
      (congrArg (fun z : U => z.val) (H.eq_fst t hy)) }⟩

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

theorem exists_neighborhood_isPiecewiseAffineOn_filling {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1)
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    {U : Set E} (hU : IsOpen U) (hLU : L.space ⊆ U) [SimplyConnectedSpace U]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (γ : freeLoop L.space) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧
      L.space ⊆ interior N.space ∧ N.space ⊆ U ∧
      ∃ f : EuclideanSpace ℝ (Fin 2) → E,
        IsPiecewiseAffineOn f P ∧ MapsTo f P (interior N.space) ∧
        ∃ (b : C(frontier P, L.space)) (e : loopCircle ≃ₜ frontier P),
          (∀ z : frontier P, f z = (b z : E)) ∧
          γ.Homotopic (b.comp (e : C(loopCircle, frontier P))) := by
  obtain ⟨f, hf, hfU, b, e, htrace, hhom⟩ :=
    hP.exists_isPiecewiseAffineOn_filling_freeLoop_homotopic L hU hLU γ
  have hC : IsCompact (L.space ∪ f '' P) :=
    (isPolyhedron_space L).isCompact.union (hP.isPolyhedron.isCompact.image_of_continuousOn
      hf.continuousOn)
  have hCU : L.space ∪ f '' P ⊆ U := union_subset hLU hfU.image_subset
  obtain ⟨N, hNfin, hN, hCN, hNU⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood hdim hC hU hCU
  exact ⟨N, hNfin, hN, subset_union_left.trans hCN, hNU, f, hf,
    fun z hz => hCN (Or.inr (mem_image_of_mem f hz)), b, e, htrace, hhom⟩

end DifferentialGeometry.Topology.PiecewiseLinear
