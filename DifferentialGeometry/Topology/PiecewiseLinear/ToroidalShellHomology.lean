/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FundamentalGroupRank
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShellCompression
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShellFundamentalGroup
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEulerParity

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))}

theorem IsToroidalShell.bettiOne_eq_two_of_separates_of_fundamentalGroup_map_injective
    (hY : IsToroidalShell Y T₀ T₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hSY : S.space ⊆ interior Y) (hsep : Separates S.space T₀ T₁) (x : S.space)
    (hi : Function.Injective (FundamentalGroup.map
      (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x)) :
    Homology.bettiOne S.space = 2 := by
  let _ : PathConnectedSpace S.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace S hSc)
  obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_interior_mulEquiv_intProd (Set.inclusion hSY x)
  let e' := e.trans (MulEquiv.prodMultiplicative ℤ ℤ).symm
  let f := e'.toMonoidHom.comp (FundamentalGroup.map
    (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x)
  have hle := fieldSingularHomology_one_finrank_le_of_fundamentalGroup_injective
    (k := ℚ) x f (e'.injective.comp hi)
  change Homology.bettiOne S.space ≤ Module.finrank ℤ (ℤ × ℤ) at hle
  have hle₂ : Homology.bettiOne S.space ≤ 2 := by simpa using hle
  have ho := hS.isOrientable_of_finrank_eq_three S (by simp) hSc
  have hpos := hS.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two S hSc ho
    (fun hχ => hY.not_separates_of_isPLSphere
      (hS.isPLSphere_two_of_faceEulerChar_eq_two S hSc hχ) hSY hsep)
  obtain ⟨m, hm⟩ := hS.even_bettiOne_of_finrank_eq_three S (by simp) hSc
  omega

theorem IsToroidalShell.eulerChar_eq_zero_of_separates_of_fundamentalGroup_map_injective
    (hY : IsToroidalShell Y T₀ T₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hSY : S.space ⊆ interior Y) (hsep : Separates S.space T₀ T₁) (x : S.space)
    (hi : Function.Injective (FundamentalGroup.map
      (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x)) :
    eulerChar S = 0 := by
  rw [hS.eulerChar_eq_two_sub_bettiOne_of_isOrientable S hSc
    (hS.isOrientable_of_finrank_eq_three S (by simp) hSc),
    hY.bettiOne_eq_two_of_separates_of_fundamentalGroup_map_injective S hS hSc hSY hsep x hi]
  norm_num

theorem IsToroidalShell.exists_separating_surface_bettiOne_eq_two
    (h252 : Moise252) (hY : IsToroidalShell Y T₀ T₁) :
    ∃ (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hSfin : S.faces.Finite),
      letI := hSfin.to_subtype
      IsCombinatorialManifold 2 S ∧ IsConnected S.space ∧ IsOrientable 2 S ∧
      IsTwoSided S.space ∧ Separates S.space T₀ T₁ ∧ ¬ SimplyConnectedSpace S.space ∧
      Homology.bettiOne S.space = 2 ∧ eulerChar S = 0 ∧
      ∃ hSY : S.space ⊆ interior Y, ∀ x : S.space,
        Function.Injective (FundamentalGroup.map
          (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x) := by
  obtain ⟨S, hSfin, hS, hSc, ho, ht, hsep, hn, hSY, hi⟩ :=
    hY.exists_non_simply_connected_separating_surface_fundamentalGroup_map_injective h252
  let _ : Finite S.faces := hSfin.to_subtype
  obtain ⟨x, hx⟩ := hSc.nonempty
  have hb := hY.bettiOne_eq_two_of_separates_of_fundamentalGroup_map_injective
    S hS hSc hSY hsep ⟨x, hx⟩ (hi ⟨x, hx⟩)
  have hχ := hY.eulerChar_eq_zero_of_separates_of_fundamentalGroup_map_injective
    S hS hSc hSY hsep ⟨x, hx⟩ (hi ⟨x, hx⟩)
  exact ⟨S, hSfin, hS, hSc, ho, ht, hsep, hn, hb, hχ, hSY, hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
