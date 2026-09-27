/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.CollaredCut
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.SphereComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSimplyConnected
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShellFundamentalGroup

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsToroidalShell.not_separates_of_isPLSphere
    {Y T₀ T₁ S : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (hS : IsPLSphere 2 S) (hSY : S ⊆ interior Y) : ¬ Separates S T₀ T₁ := by
  intro hsep
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS.isPolyhedron.isCompact
  let _ : SimplyConnectedSpace S := hS.twoSimplyConnectedSpace
  let _ : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hY.isConnected
  let _ : LocallyPathConnectedSpace Y := hY.locallyPathConnectedSpace
  obtain ⟨D, hD, hfront, _, hcover, hdisj, hDi, hDo, _⟩ :=
    hS.exists_isPLBall_complement_components
  have hDc : IsClosed D := hD.isPolyhedron.isCompact.isClosed
  obtain ⟨x₀, hx₀⟩ := hY.isConnected_left.nonempty
  obtain ⟨x₁, hx₁⟩ := hY.isConnected_right.nonempty
  have hsides : (T₀ ⊆ interior D ∧ T₁ ⊆ Dᶜ) ∨ (T₀ ⊆ Dᶜ ∧ T₁ ⊆ interior D) := by
    rcases hY.isConnected_left.isPreconnected.subset_or_subset isOpen_interior
        hDc.isOpen_compl hdisj (hsep.left_subset_compl.trans hcover.subset) with h₀ | h₀ <;>
      rcases hY.isConnected_right.isPreconnected.subset_or_subset isOpen_interior
        hDc.isOpen_compl hdisj (hsep.right_subset_compl.trans hcover.subset) with h₁ | h₁
    · exact False.elim (hsep.not_mem_connectedComponentIn hx₀ hx₁
        (hDi.isPreconnected.subset_connectedComponentIn (h₀ hx₀)
          (subset_union_left.trans hcover.symm.subset) (h₁ hx₁)))
    · exact Or.inl ⟨h₀, h₁⟩
    · exact Or.inr ⟨h₀, h₁⟩
    · exact False.elim (hsep.not_mem_connectedComponentIn hx₀ hx₁
        (hDo.isPreconnected.subset_connectedComponentIn (h₀ hx₀)
          (subset_union_right.trans hcover.symm.subset) (h₁ hx₁)))
  have impossible {T A : Set (EuclideanSpace ℝ (Fin 3))} (hTY : T ⊆ Y) (x : T)
      (hsurj : Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hTY, continuous_inclusion hTY⟩ : C(T, Y)) x))
      (hTA : T ⊆ A) (hA : SimplyConnectedSpace (((↑) : Y → _) ⁻¹' A)) : False := by
    let _ := hA
    let P := ((↑) : Y → EuclideanSpace ℝ (Fin 3)) ⁻¹' A
    let f : C(T, P) := ⟨fun t => ⟨⟨t, hTY t.property⟩, hTA t.property⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    let i : C(P, Y) := ⟨Subtype.val, continuous_subtype_val⟩
    have hfac : i.comp f = (⟨Set.inclusion hTY, continuous_inclusion hTY⟩ : C(T, Y)) := rfl
    have hnull (a : FundamentalGroup T x) :
        FundamentalGroup.map (⟨Set.inclusion hTY, continuous_inclusion hTY⟩ : C(T, Y)) x a = 1 := by
      rw [← hfac]
      change Path.Homotopic.Quotient.map a _ = .refl _
      rw [Path.Homotopic.Quotient.map_comp]
      change FundamentalGroup.map i (f x) (FundamentalGroup.map f x a) = 1
      rw [Subsingleton.elim (FundamentalGroup.map f x a) 1, map_one]
    obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_mulEquiv_intProd (Set.inclusion hTY x)
    obtain ⟨a, ha⟩ := hsurj (e.symm (Multiplicative.ofAdd (1 : ℤ), 1))
    have he := congrArg e (ha.symm.trans (hnull a))
    have hne : (Multiplicative.ofAdd (1 : ℤ), (1 : Multiplicative ℤ)) ≠ 1 := by decide
    exact hne (by simpa only [e.apply_symm_apply, map_one] using he)
  obtain ⟨c⟩ := hS.isBicollared
  obtain ⟨s, hs⟩ := hS.isConnected.nonempty
  have hc := c.simplyConnectedSpace_or_preimage_of_isMulCommutative hDc hD.closure_interior
    hfront hSY ⟨s, hs⟩ (hY.isMulCommutative_fundamentalGroup _)
  rcases hsides with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> rcases hc with hP | hQ
  · exact impossible hY.left_subset ⟨x₀, hx₀⟩
      (hY.fundamentalGroup_map_left_bijective _).2 (h₀.trans interior_subset) hP
  · exact impossible hY.right_subset ⟨x₁, hx₁⟩
      (hY.fundamentalGroup_map_right_bijective _).2
      (h₁.trans (compl_subset_compl.mpr interior_subset)) hQ
  · exact impossible hY.right_subset ⟨x₁, hx₁⟩
      (hY.fundamentalGroup_map_right_bijective _).2 (h₁.trans interior_subset) hP
  · exact impossible hY.left_subset ⟨x₀, hx₀⟩
      (hY.fundamentalGroup_map_left_bijective _).2
      (h₀.trans (compl_subset_compl.mpr interior_subset)) hQ

theorem IsToroidalShell.not_simplyConnectedSpace_of_separates
    {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hKY : K.space ⊆ interior Y)
    (hsep : Separates K.space T₀ T₁) : ¬ SimplyConnectedSpace K.space := by
  intro h
  let _ := h
  exact hY.not_separates_of_isPLSphere (hK.isPLSphere_two_of_simplyConnectedSpace K) hKY hsep

end DifferentialGeometry.Topology.PiecewiseLinear
