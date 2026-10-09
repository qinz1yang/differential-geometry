/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerFiniteWindow
import DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCarrierOfSpine
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterTorusTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalConfiguration.isSpine_image_solid
    {P : Fin 4 → E3} {D Dint : Fin 3 → Set E3} {J : Fin 4 → Set E3}
    {A S T : Fin 3 → Set E3} {N : Set E3} {φ : E3 → E3}
    {S'' T'' : Fin 3 → Set E3}
    (hc : IsCanonicalConfiguration P D Dint J A S T N φ S'' T'')
    (j : Fin 3) (k : Fin 4) (hk : k = j.castSucc ∨ k = j.succ) :
    IsSpine (φ '' S j) (φ '' J k) := by
  have hSN : S j ⊆ N := hc.unionEq.symm ▸ subset_iUnion S j
  have hp : P k ∈ Dint j := by
    rcases hk with rfl | rfl
    · exact hc.base.chain.segmentSubset j (left_mem_segment ℝ _ _)
    · exact hc.base.chain.segmentSubset j (right_mem_segment ℝ _ _)
  have hsp : IsSpine (S j) (J k) := by
    rw [hc.base.solidEq j, hc.base.circleEq k]
    exact isSpine_revolutionOf_of_mem_cellInterior (hc.base.chain.cell j)
      (hc.base.chain.halfPlane j) hp
  exact hsp.image_of_isEmbedding (hc.isEmbedding.comp (IsEmbedding.inclusion hSN))

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.isSpine_outer
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i k : ℤ) (hk : k = i ∨ k = i + 1) :
    IsSpine (φ '' S i) (φ '' J k) := by
  rcases hk with hk | hk
  · subst k
    simpa using (htw.config i).isSpine_image_solid 0 0 (Or.inl rfl)
  · subst k
    simpa using (htw.config i).isSpine_image_solid 0 1 (Or.inr rfl)

theorem IsCanonicalTower.circle_subset_interior
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i k : ℤ) (hk : k = i ∨ k = i + 1) : φ '' J k ⊆ interior (S'' i) := by
  have h := htw.config i
  rcases hk with rfl | rfl
  · simpa using (image_mono (h.base.circle_subset_annulus 0 0 (Or.inl rfl))).trans
      (h.annulusImageSubset 0)
  · simpa using (image_mono (h.base.circle_subset_annulus 0 1 (Or.inr rfl))).trans
      (h.annulusImageSubset 0)

theorem IsCanonicalTower.circle_carriesFundamentalGroupOnto
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i k : ℤ) (hk : k = i ∨ k = i + 1) :
    CarriesFundamentalGroupOnto (φ '' J k) (S'' i) := by
  have hsolid : IsCombinatorialSolidTorus (S'' i) := by
    simpa using (htw.config i).isPolyhedralSolidTorus 0
  have hinner : S'' i ⊆ interior (φ '' S i) := by
    simpa using (htw.config i).innerSubset 0
  have hsp := htw.isSpine_outer i k hk
  exact ⟨(htw.circle_subset_interior i k hk).trans interior_subset, fun hsub x =>
    (fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus
      hsolid.1 hsp.isTopologicalSolidTorus hinner hsp hsub x).2⟩

theorem IsCanonicalTower.exists_polygon_carrier_lower
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ K : Set E3, IsPLSphere 1 K ∧ K ⊆ T'' (i + 1) ∩ interior (S'' i) ∧
      CarriesFundamentalGroupOnto K (S'' (i + 1)) := by
  have hsolid : ∀ j, IsCombinatorialSolidTorus (S'' j) := fun j => by
    simpa using (htw.config j).isPolyhedralSolidTorus 0
  have hinner : ∀ j, S'' j ⊆ interior (φ '' S j) := fun j => by
    simpa using (htw.config j).innerSubset 0
  have hsp₁ := htw.isSpine_outer i (i + 1) (Or.inr rfl)
  have hsp₂ := htw.isSpine_outer (i + 1) (i + 1) (Or.inl rfl)
  have hsp₀ := htw.isSpine_outer i i (Or.inl rfl)
  have hother : φ '' J i ⊆ φ '' S (i - 1) :=
    (htw.circle_subset_interior (i - 1) i (Or.inr (by omega))).trans
      (interior_subset.trans (htw.solid_subset_outer (i - 1)))
  have hdis : Disjoint (φ '' J i) (S'' (i + 1)) :=
    (htw.apart (i - 1) (i + 1) (by rw [le_abs]; omega)).mono hother
      (htw.solid_subset_outer (i + 1))
  obtain ⟨K, hK, hsub, hgen⟩ := exists_polygon_carrier_of_spine
    (hsolid i) (hsolid (i + 1)) hsp₁.isTopologicalSolidTorus
    hsp₂.isTopologicalSolidTorus (hinner i) (hinner (i + 1)) hsp₁ hsp₂
    (htw.circle_subset_interior i (i + 1) (Or.inr rfl))
    (htw.circle_subset_interior (i + 1) (i + 1) (Or.inl rfl)) hsp₀.nonempty
    (htw.circle_subset_interior i i (Or.inl rfl)) hdis
    (htw.circle_carriesFundamentalGroupOnto i i (Or.inl rfl))
  exact ⟨K, hK, by rwa [htw.boundary_eq], hgen⟩

theorem IsCanonicalTower.exists_polygon_carrier_upper
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ K : Set E3, IsPLSphere 1 K ∧ K ⊆ T'' i ∩ interior (S'' (i + 1)) ∧
      CarriesFundamentalGroupOnto K (S'' i) := by
  have hsolid : ∀ j, IsCombinatorialSolidTorus (S'' j) := fun j => by
    simpa using (htw.config j).isPolyhedralSolidTorus 0
  have hinner : ∀ j, S'' j ⊆ interior (φ '' S j) := fun j => by
    simpa using (htw.config j).innerSubset 0
  have hsp₁ := htw.isSpine_outer (i + 1) (i + 1) (Or.inl rfl)
  have hsp₂ := htw.isSpine_outer i (i + 1) (Or.inr rfl)
  have hsp₀ := htw.isSpine_outer (i + 1) (i + 2) (Or.inr (by omega))
  have hother : φ '' J (i + 2) ⊆ φ '' S (i + 2) :=
    (htw.circle_subset_interior (i + 2) (i + 2) (Or.inl rfl)).trans
      (interior_subset.trans (htw.solid_subset_outer (i + 2)))
  have hdis : Disjoint (φ '' J (i + 2)) (S'' i) :=
    (htw.apart (i + 2) i (by rw [le_abs]; omega)).mono hother
      (htw.solid_subset_outer i)
  obtain ⟨K, hK, hsub, hgen⟩ := exists_polygon_carrier_of_spine
    (hsolid (i + 1)) (hsolid i) hsp₁.isTopologicalSolidTorus
    hsp₂.isTopologicalSolidTorus (hinner (i + 1)) (hinner i) hsp₁ hsp₂
    (htw.circle_subset_interior (i + 1) (i + 1) (Or.inl rfl))
    (htw.circle_subset_interior i (i + 1) (Or.inr rfl)) hsp₀.nonempty
    (htw.circle_subset_interior (i + 1) (i + 2) (Or.inr (by omega))) hdis
    (htw.circle_carriesFundamentalGroupOnto (i + 1) (i + 2) (Or.inr (by omega)))
  exact ⟨K, hK, by rwa [htw.boundary_eq], hgen⟩

theorem IsCanonicalTower.exists_disjoint_polygon_carriers
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ Klo Khi : Set E3, IsPLSphere 1 Klo ∧ IsPLSphere 1 Khi ∧
      Klo ⊆ T'' i ∩ interior (S'' (i - 1)) ∧
      Khi ⊆ T'' i ∩ interior (S'' (i + 1)) ∧ Disjoint Klo Khi ∧
      CarriesFundamentalGroupOnto Klo (S'' i) ∧
      CarriesFundamentalGroupOnto Khi (S'' i) := by
  obtain ⟨Klo, hlo, hlosub, hlogen⟩ := htw.exists_polygon_carrier_lower (i - 1)
  obtain ⟨Khi, hhi, hhisub, hhigen⟩ := htw.exists_polygon_carrier_upper i
  have hlosub' : Klo ⊆ T'' i ∩ interior (S'' (i - 1)) := by simpa using hlosub
  have hlogen' : CarriesFundamentalGroupOnto Klo (S'' i) := by simpa using hlogen
  refine ⟨Klo, Khi, hlo, hhi, hlosub', hhisub, ?_, hlogen', hhigen⟩
  exact (htw.solid_disjoint (i := i - 1) (k := i + 1) (by rw [le_abs]; omega)).mono
    (hlosub'.trans inter_subset_right |>.trans interior_subset)
    (hhisub.trans inter_subset_right |>.trans interior_subset)

end DifferentialGeometry.Topology.PiecewiseLinear
