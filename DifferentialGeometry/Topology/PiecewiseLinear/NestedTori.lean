/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.Connected.SeparatorLocation
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308NestedShell
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Closure

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isCompact_of_isTopologicalSolidTorus
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) : IsCompact S := by
  obtain ⟨φ⟩ := hS
  have : CompactSpace S := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

private theorem isConnected_of_isTopologicalSolidTorus
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) : IsConnected S := by
  obtain ⟨φ⟩ := hS
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have hD : PathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).isPathConnected
        ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  have hC : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  have : PathConnectedSpace S := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  have : ConnectedSpace S := inferInstance
  have hrange : range (Subtype.val : S → EuclideanSpace ℝ (Fin 3)) = S := Subtype.range_val
  rw [← hrange]
  exact isConnected_range continuous_subtype_val

theorem subset_interior_of_nested_tori
    {S₁ S₂ T : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsTopologicalSolidTorus S₁) (hS₂ : IsTopologicalSolidTorus S₂)
    (h₁₂ : S₁ ⊆ interior S₂)
    (hshell : IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂))
    (hT : T ⊆ interior (closure (S₂ \ S₁))) (hsep : Separates T (frontier S₁) (frontier S₂))
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hfront : frontier R.space = T) (hreg : closure (interior R.space) = R.space)
    (hint : IsConnected (interior R.space)) (hext : IsConnected R.spaceᶜ) :
    S₁ ⊆ interior R.space ∧ R.space ⊆ interior S₂ := by
  let _ := hreg
  have hRpoly : IsPolyhedron R.space := isPolyhedron_space R
  have hRcomp : IsCompact R.space := hRpoly.isCompact
  have hRclosed : IsClosed R.space := hRpoly.isClosed
  have hS₁comp : IsCompact S₁ := isCompact_of_isTopologicalSolidTorus hS₁
  have hS₁closed : IsClosed S₁ := hS₁comp.isClosed
  have hS₁conn : IsConnected S₁ := isConnected_of_isTopologicalSolidTorus hS₁
  have hS₂comp : IsCompact S₂ := isCompact_of_isTopologicalSolidTorus hS₂
  have hS₂closed : IsClosed S₂ := hS₂comp.isClosed
  have hdisj : Disjoint (interior R.space) R.spaceᶜ :=
    disjoint_compl_right.mono interior_subset subset_rfl
  have hTc : Tᶜ = interior R.space ∪ R.spaceᶜ := by
    rw [← hfront, compl_frontier_eq_union_interior, hRclosed.isOpen_compl.interior_eq]
  have subset_W_or_X {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : IsConnected A) (hAT : A ⊆ Tᶜ) :
      A ⊆ interior R.space ∨ A ⊆ R.spaceᶜ := by
    by_cases h : (A ∩ interior R.space).Nonempty
    · exact Or.inl (hAc.isPreconnected.subset_left_of_subset_union
        isOpen_interior hRclosed.isOpen_compl hdisj (hAT.trans hTc.subset) h)
    · refine Or.inr fun x hx => ?_
      rcases hTc.subset (hAT hx) with hxW | hxX
      · exact False.elim (h ⟨x, hx, hxW⟩)
      · exact hxX
  have hF₁_conn : IsConnected (frontier S₁) := hshell.isConnected_left
  have hF₂_conn : IsConnected (frontier S₂) := hshell.isConnected_right
  have hF₁_sub : frontier S₁ ⊆ Tᶜ := hsep.left_subset_compl
  have hF₂_sub : frontier S₂ ⊆ Tᶜ := hsep.right_subset_compl
  have hF₁_case := subset_W_or_X hF₁_conn hF₁_sub
  have hF₂_case := subset_W_or_X hF₂_conn hF₂_sub
  have not_both_W (h1 : frontier S₁ ⊆ interior R.space) (h2 : frontier S₂ ⊆ interior R.space) :
      False := by
    obtain ⟨x, hx⟩ := hF₁_conn.nonempty
    obtain ⟨y, hy⟩ := hF₂_conn.nonempty
    have hxW : x ∈ interior R.space := h1 hx
    have hyW : y ∈ interior R.space := h2 hy
    have hWsub : interior R.space ⊆ connectedComponentIn Tᶜ x :=
      hint.isPreconnected.subset_connectedComponentIn hxW
        (subset_union_left.trans hTc.symm.subset)
    exact hsep.not_mem_connectedComponentIn hx hy (hWsub hyW)
  have not_both_X (h1 : frontier S₁ ⊆ R.spaceᶜ) (h2 : frontier S₂ ⊆ R.spaceᶜ) :
      False := by
    obtain ⟨x, hx⟩ := hF₁_conn.nonempty
    obtain ⟨y, hy⟩ := hF₂_conn.nonempty
    have hxX : x ∈ R.spaceᶜ := h1 hx
    have hyX : y ∈ R.spaceᶜ := h2 hy
    have hXsub : R.spaceᶜ ⊆ connectedComponentIn Tᶜ x :=
      hext.isPreconnected.subset_connectedComponentIn hxX
        (subset_union_right.trans hTc.symm.subset)
    exact hsep.not_mem_connectedComponentIn hx hy (hXsub hyX)
  have not_swap (h1 : frontier S₁ ⊆ R.spaceᶜ) (h2 : frontier S₂ ⊆ interior R.space) :
      False := by
    have hsepS₂ : Separates (frontier S₂) (interior S₂) S₂ᶜ :=
      separates_frontier subset_rfl (by rw [hS₂closed.isOpen_compl.interior_eq])
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))).mp
      (hRcomp.union hS₂comp).isBounded
    let p : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (max r 0 + 1)
    have hdist : dist p 0 = max r 0 + 1 := by
      rw [dist_zero_right, PiLp.norm_single, Real.norm_of_nonneg]
      linarith [le_max_right r 0]
    have hp_not : p ∉ Metric.closedBall 0 r := by
      rw [Metric.mem_closedBall, hdist]
      linarith [le_max_left r 0]
    have hpX : p ∈ R.spaceᶜ := fun hpR => hp_not (hr (Or.inl hpR))
    have hpS₂c : p ∈ S₂ᶜ := fun hpS => hp_not (hr (Or.inr hpS))
    have hmeetK : (S₂ᶜ ∩ R.spaceᶜ).Nonempty := ⟨p, hpS₂c, hpX⟩
    obtain ⟨x, hx⟩ := hF₁_conn.nonempty
    have hxint : x ∈ interior S₂ := h₁₂ (hS₁closed.frontier_subset hx)
    have hmeetH : (interior S₂ ∩ R.spaceᶜ).Nonempty := ⟨x, hxint, h1 hx⟩
    have hmeet : (frontier S₂ ∩ R.spaceᶜ).Nonempty :=
      hsepS₂.inter_nonempty_of_isPreconnected hext.isPreconnected hmeetH hmeetK
    obtain ⟨y, hyF₂, hyX⟩ := hmeet
    exact hyX (interior_subset (h2 hyF₂))
  have hF₁W : frontier S₁ ⊆ interior R.space := by
    rcases hF₁_case with h1 | h1
    · exact h1
    · rcases hF₂_case with h2 | h2
      · exact False.elim (not_swap h1 h2)
      · exact False.elim (not_both_X h1 h2)
  have hF₂X : frontier S₂ ⊆ R.spaceᶜ := by
    rcases hF₂_case with h2 | h2
    · rcases hF₁_case with h1 | h1
      · exact False.elim (not_both_W h1 h2)
      · exact False.elim (not_swap h1 h2)
    · exact h2
  have hdisj1 : Disjoint (interior S₁) (S₂ \ S₁) :=
    disjoint_left.mpr fun x hx ⟨_, hx₂⟩ => hx₂ (interior_subset hx)
  have hdisj2 : Disjoint (interior S₁) (closure (S₂ \ S₁)) :=
    hdisj1.closure_right isOpen_interior
  have hdisjT : Disjoint (interior S₁) T :=
    hdisj2.mono_right (hT.trans interior_subset)
  have hS₁T : Disjoint S₁ T := by
    rw [← hS₁closed.closure_eq, closure_eq_interior_union_frontier, disjoint_union_left]
    exact ⟨hdisjT, disjoint_left.mpr fun x hx hxT => hsep.left_subset_compl hx hxT⟩
  have hS₁_sub_Tc : S₁ ⊆ Tᶜ := disjoint_left.mp hS₁T
  have hS₁W : S₁ ⊆ interior R.space := by
    obtain ⟨x, hx⟩ := hF₁_conn.nonempty
    have hxS₁ : x ∈ S₁ := hS₁closed.frontier_subset hx
    have hxW : x ∈ interior R.space := hF₁W hx
    exact hS₁conn.isPreconnected.subset_left_of_subset_union
      isOpen_interior hRclosed.isOpen_compl hdisj (hS₁_sub_Tc.trans hTc.subset) ⟨x, hxS₁, hxW⟩
  have hT_S₂ : T ⊆ interior S₂ := by
    have hsub : S₂ \ S₁ ⊆ S₂ := sdiff_subset
    have hcl : closure (S₂ \ S₁) ⊆ S₂ :=
      closure_minimal hsub hS₂closed
    exact hT.trans (interior_mono hcl)
  have hW_S₂ : interior R.space ⊆ interior S₂ := by
    have hsepS₂ : Separates (frontier S₂) (interior S₂) S₂ᶜ :=
      separates_frontier subset_rfl (by rw [hS₂closed.isOpen_compl.interior_eq])
    by_contra hn
    have hmeetK : (S₂ᶜ ∩ interior R.space).Nonempty := by
      obtain ⟨x, hxW, hxS₂⟩ := not_subset.mp hn
      by_cases hx : x ∈ S₂
      · have hx_front : x ∈ frontier S₂ := by
          refine ⟨subset_closure hx, ?_⟩
          intro hx_int
          exact hxS₂ hx_int
        have hxX : x ∈ R.spaceᶜ := hF₂X hx_front
        exact False.elim ((disjoint_left.mp hdisj hxW) hxX)
      · exact ⟨x, hx, hxW⟩
    obtain ⟨x, hx⟩ := hF₁_conn.nonempty
    have hxint : x ∈ interior S₂ := h₁₂ (hS₁closed.frontier_subset hx)
    have hmeetH : (interior S₂ ∩ interior R.space).Nonempty := ⟨x, hxint, hF₁W hx⟩
    have hmeet : (frontier S₂ ∩ interior R.space).Nonempty :=
      hsepS₂.inter_nonempty_of_isPreconnected hint.isPreconnected hmeetH hmeetK
    obtain ⟨y, hyF₂, hyW⟩ := hmeet
    exact (disjoint_left.mp hdisj hyW) (hF₂X hyF₂)
  have hR_S₂ : R.space ⊆ interior S₂ := by
    rw [← hRclosed.closure_eq, closure_eq_interior_union_frontier, hfront]
    exact union_subset hW_S₂ hT_S₂
  exact ⟨hS₁W, hR_S₂⟩

private noncomputable def circleModelHomeomorph :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  refine
    { toFun := fun z =>
        ⟨e z, by
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.norm_map]
          exact Circle.norm_coe z⟩
      invFun := fun y =>
        ⟨e.symm y, by
          change e.symm (y : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere (0 : ℂ) 1
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.symm.norm_map]
          exact mem_sphere_zero_iff_norm.mp y.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact e.symm_apply_apply z
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

private noncomputable def fundamentalGroupSolidTorusEquivInt
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) (x : S) :
    FundamentalGroup S x ≃* Multiplicative ℤ := by
  let φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := Classical.choice hS
  let p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨0, by simp⟩
  let e₁ : S ≃ₕ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := φ.toHomotopyEquiv
  let e₂ : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₕ
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    (Homeomorph.prodComm _ _).toHomotopyEquiv
  let e₃ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₕ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    DifferentialGeometry.HomotopyEquiv.productConvex _
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) p
  let e₄ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₕ Circle :=
    circleModelHomeomorph.symm.toHomotopyEquiv
  let e := e₁.trans (e₂.trans (e₃.trans e₄))
  let q : Path (e x) (1 : Circle) := PathConnectedSpace.somePath _ _
  exact
    (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        e x (e x) rfl).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans
        DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt)

theorem not_nullhomotopic_inclusion_of_nested_tori
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsTopologicalSolidTorus S₁) (hS₂ : IsTopologicalSolidTorus S₂)
    (h₁₂ : S₁ ⊆ interior S₂)
    (hshell : IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂)) :
    ¬ (⟨Set.inclusion (h₁₂.trans interior_subset), continuous_inclusion _⟩ :
      C(S₁, S₂)).Nullhomotopic := by
  intro hnull
  have hclosed₁ : IsClosed S₁ := (isCompact_of_isTopologicalSolidTorus hS₁).isClosed
  have hclosed₂ : IsClosed S₂ := (isCompact_of_isTopologicalSolidTorus hS₂).isClosed
  let i₁₂ : C(S₁, S₂) :=
    ⟨Set.inclusion (h₁₂.trans interior_subset), continuous_inclusion _⟩
  obtain ⟨eShell, heShell⟩ :=
    homotopyEquiv_inclusion_of_isToroidalShell hclosed₁ hclosed₂ h₁₂ hshell
  obtain ⟨x⟩ := (isConnected_of_isTopologicalSolidTorus hS₁).nonempty.to_subtype
  have hi₁₂ : Function.Injective (FundamentalGroup.map i₁₂ x) :=
    (DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
      eShell i₁₂ heShell x).1
  let eGroup : FundamentalGroup S₁ x ≃* Multiplicative ℤ :=
    fundamentalGroupSolidTorusEquivInt hS₁ x
  let g : FundamentalGroup S₁ x := eGroup.symm (Multiplicative.ofAdd 1)
  have hg1 : g ≠ 1 := by
    intro hg
    have heq : eGroup g = 1 := by rw [hg, map_one]
    rw [eGroup.apply_symm_apply] at heq
    have h1 : (1 : ℤ) = 0 := Multiplicative.ofAdd.injective (heq.trans ofAdd_zero.symm)
    exact one_ne_zero h1
  have hmap : FundamentalGroup.map i₁₂ x g = 1 :=
    fundamentalGroup_map_eq_one_of_nullhomotopic i₁₂ hnull x g
  have hg_one : g = 1 := by
    apply hi₁₂
    rw [hmap, map_one]
  exact hg1 hg_one

end DifferentialGeometry.Topology.PiecewiseLinear
