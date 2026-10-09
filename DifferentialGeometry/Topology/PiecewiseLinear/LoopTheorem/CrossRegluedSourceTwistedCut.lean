/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedBranch
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def verticalWall (s : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' ({s} ×ˢ Icc (0 : ℝ) 1)

private theorem mem_verticalWall {s : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ verticalWall s ↔ (seamWitnessPlane.symm z).1 = s ∧
      (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1 := mem_image_seamWitnessPlane

private theorem isPolyhedron_verticalWall (s : ℝ) : IsPolyhedron (verticalWall s) :=
  isPolyhedron_image_seamWitnessPlane
    ((isHPolytope_singleton s).prod isHPolytope_Icc).isPolyhedron

noncomputable def twistedStripReflection :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  seamWitnessPlane.toLinearMap.toAffineMap.comp
    ((AffineMap.const ℝ (ℝ × ℝ) (1, 1) - AffineMap.id ℝ (ℝ × ℝ)).comp
      seamWitnessPlane.symm.toLinearMap.toAffineMap)

theorem twistedStripReflection_apply (s t : ℝ) :
    twistedStripReflection (seamWitnessPlane (s, t)) = seamWitnessPlane (1 - s, 1 - t) := by
  change seamWitnessPlane ((1, 1) - seamWitnessPlane.symm (seamWitnessPlane (s, t))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem twistedStripReflection_involutive : Function.Involutive twistedStripReflection := by
  intro z
  obtain ⟨⟨s, t⟩, rfl⟩ := seamWitnessPlane.surjective z
  rw [twistedStripReflection_apply, twistedStripReflection_apply]
  congr 1
  ext <;> dsimp <;> ring

theorem twistedStripReflection_image_wall (s : ℝ) :
    twistedStripReflection '' (seamWitnessPlane '' ({s} ×ˢ Icc (0 : ℝ) 1)) =
      seamWitnessPlane '' ({1 - s} ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro z ⟨w, ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩, rfl⟩
    change r = s at hr
    subst r
    rw [twistedStripReflection_apply]
    exact mem_image_of_mem _ ⟨rfl, by linarith [ht.2], by linarith [ht.1]⟩
  · rintro z ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    change r = 1 - s at hr
    subst r
    refine ⟨seamWitnessPlane (s, 1 - t),
      mem_image_of_mem _ ⟨rfl, by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [twistedStripReflection_apply]
    congr 1
    exact Prod.ext rfl (by ring)

theorem isPLHomeomorphOn_twistedStripReflection_wall (s : ℝ) :
    IsPLHomeomorphOn twistedStripReflection
      (seamWitnessPlane '' ({s} ×ˢ Icc (0 : ℝ) 1))
      (seamWitnessPlane '' ({1 - s} ×ˢ Icc (0 : ℝ) 1)) := by
  rw [← twistedStripReflection_image_wall]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_verticalWall s)
    ((isPiecewiseAffineOn_of_affine twistedStripReflection isOpen_univ).mono_of_isPolyhedron
      (isPolyhedron_verticalWall s) (subset_univ _))
    twistedStripReflection_involutive.injective.injOn.bijOn_image

private theorem cell_plane (s t : ℝ) :
    twistedStripCell (seamWitnessPlane (s, t)) = twistedStripMap (s, t) := by
  change twistedStripMap (seamWitnessPlane.symm (seamWitnessPlane (s, t))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

private theorem seam_reverse (t : ℝ) : twistedStripMap (1, t) = twistedStripMap (0, 1 - t) := by
  have h := twistedStripMap_seam (1 - t)
  have heq : (1, 1 - (1 - t)) = ((1 : ℝ), t) := Prod.ext rfl (by ring)
  rw [heq] at h
  exact h.symm

private theorem cell_injOn_wall {s : ℝ} (hs : s ∈ Icc (-1 / 4 : ℝ) (5 / 4)) :
    InjOn (⇑twistedStripCell) (verticalWall s) := by
  rintro z ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩ w ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ heq
  change r = s at hr
  change u = s at hu
  subst r u
  rw [cell_plane, cell_plane] at heq
  rcases (twistedStripMap_eq_iff hs hs).mp heq with h | h | h
  · exact congrArg seamWitnessPlane h
  · have h01 : (0 : ℝ) = 1 := h.1.symm.trans h.2.1
    norm_num at h01
  · have h10 : (1 : ℝ) = 0 := h.1.symm.trans h.2.1
    norm_num at h10

private theorem cell_image_wall {s : ℝ} (hs : s = 0 ∨ s = 1) :
    ⇑twistedStripCell '' verticalWall s =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain := by
  rw [twistedStripCell_doublePointSet]
  apply Subset.antisymm
  · rintro z ⟨w, ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩, rfl⟩
    change r = s at hr
    subst r
    rw [cell_plane]
    rcases hs with rfl | rfl
    · exact mem_image_of_mem _ ht
    · exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (seam_reverse t).symm⟩
  · rintro z ⟨t, ht, rfl⟩
    rcases hs with rfl | rfl
    · exact ⟨seamWitnessPlane (0, t), mem_image_of_mem _ ⟨rfl, ht⟩, cell_plane _ _⟩
    · refine ⟨seamWitnessPlane (1, 1 - t),
        mem_image_of_mem _ ⟨rfl, by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      rw [cell_plane]
      exact (twistedStripMap_seam t).symm

private theorem branchPreimage_walls {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain) :
    hD.branchPreimage c = verticalWall 0 ∪ verticalWall 1 := by
  ext z
  change (z ∈ twistedStripCell.domain ∧ twistedStripCell z ∈ hD.singularSet.branchCarrier c) ↔ _
  rw [hc]
  constructor
  · rintro ⟨hz, hy⟩
    rw [twistedStripCell_doublePointSet] at hy
    obtain ⟨t, ht, heq⟩ := hy
    have hp := mem_image_seamWitnessPlane.mp hz
    have hval : twistedStripMap (seamWitnessPlane.symm z) = twistedStripMap (0, t) := heq.symm
    rcases (twistedStripMap_eq_iff hp.1 (by norm_num)).mp hval with h | h | h
    · exact Or.inl (mem_verticalWall.mpr ⟨congrArg Prod.fst h, hp.2⟩)
    · norm_num at h
    · exact Or.inr (mem_verticalWall.mpr ⟨h.1, hp.2⟩)
  · rintro (hz | hz)
    · have hp := mem_verticalWall.mp hz
      refine ⟨mem_image_seamWitnessPlane.mpr ⟨?_, hp.2⟩,
        (cell_image_wall (Or.inl rfl)).subset (mem_image_of_mem _ hz)⟩
      rw [hp.1]
      norm_num
    · have hp := mem_verticalWall.mp hz
      refine ⟨mem_image_seamWitnessPlane.mpr ⟨?_, hp.2⟩,
        (cell_image_wall (Or.inr rfl)).subset (mem_image_of_mem _ hz)⟩
      rw [hp.1]
      norm_num

private theorem branchCoordinate_wall {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
    {s : ℝ} (hs : s = 0 ∨ s = 1) :
    IsPLHomeomorphOn (hD.branchCoordinate c) (verticalWall s)
      (hD.singularSet.branchComplex c).space := by
  have hsub : verticalWall s ⊆ hD.branchPreimage c := by
    rw [branchPreimage_walls hD hc]
    rcases hs with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have hsI : s ∈ Icc (-1 / 4 : ℝ) (5 / 4) := by rcases hs with rfl | rfl <;> norm_num
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_verticalWall s)
    ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron
      (isPolyhedron_verticalWall s) hsub)
  refine ⟨fun _ hz => hD.branchCoordinate_mem c (hsub hz), ?_, ?_⟩
  · intro z hz w hw heq
    apply cell_injOn_wall hsI hz hw
    rw [← hD.branchPieceIn_map_branchCoordinate c (hsub hz),
      ← hD.branchPieceIn_map_branchCoordinate c (hsub hw), heq]
  · intro v hv
    have hvm := (hD.singularSet.branchPieceIn c).bijOn.mapsTo hv
    obtain ⟨z, hz, heq⟩ := (cell_image_wall hs).symm.subset (hc.subset hvm)
    refine ⟨z, hz, ?_⟩
    apply (hD.singularSet.branchPieceIn c).bijOn.injOn
      (hD.branchCoordinate_mem c (hsub hz)) hv
    rw [hD.branchPieceIn_map_branchCoordinate c (hsub hz), heq]

theorem twistedStripCell_exists_reversing_cut {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain) :
    ∃ D₁ D₂ D₃ : SingularTwoCell halfTurnQuotient,
      hD.IsBoundaryBranchCut c
        (seamWitnessPlane '' ({(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1))
        (seamWitnessPlane '' ({(1 : ℝ)} ×ˢ Icc (0 : ℝ) 1))
        (seamWitnessPlane (0, 0)) (seamWitnessPlane (0, 1))
        (seamWitnessPlane (1, 0)) (seamWitnessPlane (1, 1))
        twistedStripReflection D₁ D₂ D₃ ∧
      D₁.domain = seamWitnessPlane '' (Icc (-1 / 4 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1) ∧
      D₂.domain = seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      D₃.domain = seamWitnessPlane '' (Icc (1 : ℝ) (5 / 4) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨D₁, D₂, D₃, hD₁, hD₂, hD₃, hA, hC, hdis, hdom, h₁₂, h₂₃,
    hA₁, hA₂, hC₂, hC₃, hdis₁₃, hf₁, hf₂, hf₃, ht₁, ht₃, hc₁, hc₃⟩ :=
    twistedStripCell.exists_three_cells_of_rectangular_domain
      (a := -1 / 4) (b := 0) (c := 1) (d := 5 / 4)
      (by norm_num) (by norm_num) (by norm_num) rfl
  refine ⟨D₁, D₂, D₃, ⟨hA, hC, hdis, branchPreimage_walls hD hc,
    branchCoordinate_wall hD hc (Or.inl rfl), branchCoordinate_wall hD hc (Or.inr rfl),
    ?_, ?_, hdom, h₁₂, h₂₃, hA₁, hA₂, hC₂, hC₃, hdis₁₃, hf₁, hf₂, hf₃,
    ht₁, ht₃, hc₁, hc₃⟩, hD₁, hD₂, hD₃⟩
  · simpa only [sub_zero] using isPLHomeomorphOn_twistedStripReflection_wall 0
  · rintro z ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    change s = 0 at hs
    subst s
    change twistedStripCell (seamWitnessPlane (0, t)) =
      twistedStripCell (twistedStripReflection (seamWitnessPlane (0, t)))
    rw [twistedStripReflection_apply, sub_zero, cell_plane, cell_plane]
    exact twistedStripMap_seam t

theorem twistedStripReflection_reversing_endpoints :
    twistedStripReflection (seamWitnessPlane (0, 0)) = seamWitnessPlane (1, 1) ∧
      twistedStripReflection (seamWitnessPlane (0, 1)) = seamWitnessPlane (1, 0) := by
  constructor <;> rw [twistedStripReflection_apply] <;> norm_num

end DifferentialGeometry.Topology.PiecewiseLinear
