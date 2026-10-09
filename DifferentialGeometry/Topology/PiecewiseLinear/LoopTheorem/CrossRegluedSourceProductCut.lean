/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductBranch
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseOfCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def placedStrip (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)

private def placedWall (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' ({a} ×ˢ Icc (0 : ℝ) 1)

private theorem mem_placedStrip {a b : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ placedStrip a b ↔
      (seamWitnessPlane.symm z).1 ∈ Icc a b ∧
        (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1 :=
  mem_image_seamWitnessPlane

private theorem mem_placedWall {a : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ placedWall a ↔
      (seamWitnessPlane.symm z).1 = a ∧ (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1 :=
  mem_image_seamWitnessPlane

private theorem isPLBall_placedStrip {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (placedStrip a b) := by
  have h := isPLBall_two_prod (isPLBall_Icc hab)
    (isPLBall_Icc (by norm_num : (0 : ℝ) < 1))
  exact h.of_isPLHomeomorphOn
    (isPLHomeomorphOn_seamWitnessPlane (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron)

private noncomputable def wallAffine (a : ℝ) : ℝ →ᵃ[ℝ] (ℝ × ℝ) where
  toFun t := (a, t)
  linear := LinearMap.inr ℝ ℝ ℝ
  map_vadd' t v := by simp

private theorem isPLHomeomorphOn_wall (a : ℝ) :
    IsPLHomeomorphOn (fun t => seamWitnessPlane (a, t)) (Icc (0 : ℝ) 1) (placedWall a) := by
  have hpa : IsPiecewiseAffineOn (⇑(wallAffine a)) (Icc (0 : ℝ) 1) :=
    (isPiecewiseAffineOn_of_affine (wallAffine a) isOpen_univ).mono_of_isPolyhedron
      isHPolytope_Icc.isPolyhedron (subset_univ _)
  have himg : (wallAffine a) '' Icc (0 : ℝ) 1 = {a} ×ˢ Icc (0 : ℝ) 1 := by
    ext ⟨s, t⟩
    constructor
    · rintro ⟨u, hu, h⟩
      cases h
      exact ⟨rfl, hu⟩
    · rintro ⟨rfl, ht⟩
      exact ⟨t, ht, rfl⟩
  have hinj : Function.Injective (wallAffine a) :=
    fun s t h => congrArg Prod.snd h
  have hw := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hpa hinj.injOn.bijOn_image
  rw [himg] at hw
  exact hw.trans (isPLHomeomorphOn_seamWitnessPlane
    ((isHPolytope_singleton a).prod isHPolytope_Icc).isPolyhedron)

private theorem isPLBall_placedWall (a : ℝ) : IsPLBall 1 (placedWall a) :=
  (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn
    (isPLHomeomorphOn_wall a)

private theorem isArcBetween_placedWall (a : ℝ) :
    Schoenflies.IsArcBetween (placedWall a)
      (seamWitnessPlane (a, 0)) (seamWitnessPlane (a, 1)) :=
  ⟨fun t => seamWitnessPlane (a, t),
    (seamWitnessPlane.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn,
    fun _ _ _ _ h => congrArg Prod.snd (seamWitnessPlane.injective h),
    (isPLHomeomorphOn_wall a).image_eq, rfl, rfl⟩

private theorem mem_frontier_placedStrip {a b : ℝ} (hab : a ≤ b)
    {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ frontier (placedStrip a b) ↔
      ((seamWitnessPlane.symm z).1 ∈ Icc a b ∧
        ((seamWitnessPlane.symm z).2 = 0 ∨ (seamWitnessPlane.symm z).2 = 1)) ∨
      (((seamWitnessPlane.symm z).1 = a ∨ (seamWitnessPlane.symm z).1 = b) ∧
        (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1) := by
  have hfront : frontier (placedStrip a b) =
      seamWitnessPlane '' frontier (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    (seamWitnessPlane.toHomeomorph.image_frontier _).symm
  rw [hfront, mem_image_seamWitnessPlane, frontier_prod_eq, isClosed_Icc.closure_eq,
    isClosed_Icc.closure_eq, frontier_Icc hab, frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

private theorem placedWall_subset_frontier_left {a b : ℝ} (hab : a ≤ b) :
    placedWall a ⊆ frontier (placedStrip a b) := by
  intro z hz
  have h := mem_placedWall.mp hz
  exact (mem_frontier_placedStrip hab).mpr (Or.inr ⟨Or.inl h.1, h.2⟩)

private theorem placedWall_subset_frontier_right {a b : ℝ} (hab : a ≤ b) :
    placedWall b ⊆ frontier (placedStrip a b) := by
  intro z hz
  have h := mem_placedWall.mp hz
  exact (mem_frontier_placedStrip hab).mpr (Or.inr ⟨Or.inr h.1, h.2⟩)

private theorem placedStrip_subset {a b c d : ℝ} (hac : c ≤ a) (hbd : b ≤ d) :
    placedStrip a b ⊆ placedStrip c d := by
  intro z hz
  have h := mem_placedStrip.mp hz
  exact mem_placedStrip.mpr ⟨⟨hac.trans h.1.1, h.1.2.trans hbd⟩, h.2⟩

private theorem placedStrip_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    placedStrip a b ∪ placedStrip b c = placedStrip a c := by
  ext z
  simp only [mem_union, mem_placedStrip, mem_Icc]
  constructor
  · rintro (⟨⟨ha, hb⟩, ht⟩ | ⟨⟨hb, hc⟩, ht⟩)
    · exact ⟨⟨ha, hb.trans hbc⟩, ht⟩
    · exact ⟨⟨hab.trans hb, hc⟩, ht⟩
  · rintro ⟨⟨ha, hc⟩, ht⟩
    rcases le_total (seamWitnessPlane.symm z).1 b with hb | hb
    · exact Or.inl ⟨⟨ha, hb⟩, ht⟩
    · exact Or.inr ⟨⟨hb, hc⟩, ht⟩

private theorem placedStrip_inter {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    placedStrip a b ∩ placedStrip b c = placedWall b := by
  ext z
  simp only [mem_inter_iff, mem_placedStrip, mem_placedWall, mem_Icc]
  constructor
  · rintro ⟨⟨⟨-, hb⟩, ht⟩, ⟨⟨hb', -⟩, -⟩⟩
    exact ⟨le_antisymm hb hb', ht⟩
  · rintro ⟨hb, ht⟩
    exact ⟨⟨⟨by simpa [hb] using hab, by simp [hb]⟩, ht⟩,
      ⟨⟨by simp [hb], by simpa [hb] using hbc⟩, ht⟩⟩

private theorem placedStrip_disjoint {a b c d : ℝ} (hbc : b < c) :
    Disjoint (placedStrip a b) (placedStrip c d) := by
  apply disjoint_left.mpr
  intro z hz hw
  have hz' := mem_placedStrip.mp hz
  have hw' := mem_placedStrip.mp hw
  exact (not_le_of_gt hbc) (hw'.1.1.trans hz'.1.2)

private theorem exists_placedStrip_trace_cut {a s b : ℝ} (has : a < s) (hsb : s < b) :
    IsPLBall 1 (placedStrip a s ∩ frontier (placedStrip a b)) ∧
      Schoenflies.IsCutPair (frontier (placedStrip a s))
        (seamWitnessPlane (s, 0)) (seamWitnessPlane (s, 1)) (placedWall s)
        (placedStrip a s ∩ frontier (placedStrip a b)) ∧
      IsPLBall 1 (placedStrip s b ∩ frontier (placedStrip a b)) ∧
      Schoenflies.IsCutPair (frontier (placedStrip s b))
        (seamWitnessPlane (s, 0)) (seamWitnessPlane (s, 1)) (placedWall s)
        (placedStrip s b ∩ frontier (placedStrip a b)) := by
  have hi := placedStrip_inter has.le hsb.le
  obtain ⟨R, T, hRcut, hTcut, hR, hT, hfront⟩ :=
    exists_complementary_frontier_arcs_of_isPLBall_union_between
      (isPLBall_placedStrip has) (isPLBall_placedStrip hsb)
      (hi.symm ▸ isPLBall_placedWall s) (hi.symm ▸ isArcBetween_placedWall s)
      (hi.symm ▸ placedWall_subset_frontier_right has.le)
      (hi.symm ▸ placedWall_subset_frontier_left hsb.le)
  rw [hi] at hRcut hTcut
  have hleft : R = placedStrip a s ∩ frontier (placedStrip a b) := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨(isPLBall_placedStrip has).isPolyhedron.isClosed.frontier_subset
        (hRcut.snd_subset hz), ?_⟩
      rw [← placedStrip_union has.le hsb.le, hfront]
      exact Or.inl hz
    · intro z hz
      have hzf : z ∈ frontier (placedStrip a s) := by
        rcases (mem_frontier_placedStrip (has.trans hsb).le).mp hz.2 with h | h
        · exact (mem_frontier_placedStrip has.le).mpr (Or.inl ⟨
            (mem_placedStrip.mp hz.1).1, h.2⟩)
        · rcases h.1 with ha | hb
          · exact (mem_frontier_placedStrip has.le).mpr (Or.inr ⟨Or.inl ha, h.2⟩)
          · have hh := (mem_placedStrip.mp hz.1).1.2
            exact (not_le_of_gt hsb (hb ▸ hh)).elim
      rcases hRcut.union_eq.symm.subset hzf with hzW | hzR
      · have hw := mem_placedWall.mp hzW
        have ht : (seamWitnessPlane.symm z).2 = 0 ∨
            (seamWitnessPlane.symm z).2 = 1 := by
          rcases (mem_frontier_placedStrip (has.trans hsb).le).mp hz.2 with h | h
          · exact h.2
          · rcases h.1 with h | h <;> linarith [hw.1]
        rcases ht with ht | ht
        · have hz0 : z = seamWitnessPlane (s, 0) := by
            apply seamWitnessPlane.symm.injective
            simpa using Prod.ext hw.1 ht
          exact hz0 ▸ hRcut.snd.left_mem
        · have hz1 : z = seamWitnessPlane (s, 1) := by
            apply seamWitnessPlane.symm.injective
            simpa using Prod.ext hw.1 ht
          exact hz1 ▸ hRcut.snd.right_mem
      · exact hzR
  have hright : T = placedStrip s b ∩ frontier (placedStrip a b) := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨(isPLBall_placedStrip hsb).isPolyhedron.isClosed.frontier_subset
        (hTcut.snd_subset hz), ?_⟩
      rw [← placedStrip_union has.le hsb.le, hfront]
      exact Or.inr hz
    · intro z hz
      have hzf : z ∈ frontier (placedStrip s b) := by
        rcases (mem_frontier_placedStrip (has.trans hsb).le).mp hz.2 with h | h
        · exact (mem_frontier_placedStrip hsb.le).mpr (Or.inl ⟨
            (mem_placedStrip.mp hz.1).1, h.2⟩)
        · rcases h.1 with ha | hb
          · have hh := (mem_placedStrip.mp hz.1).1.1
            exact (not_le_of_gt has (ha ▸ hh)).elim
          · exact (mem_frontier_placedStrip hsb.le).mpr (Or.inr ⟨Or.inr hb, h.2⟩)
      rcases hTcut.union_eq.symm.subset hzf with hzW | hzT
      · have hw := mem_placedWall.mp hzW
        have ht : (seamWitnessPlane.symm z).2 = 0 ∨
            (seamWitnessPlane.symm z).2 = 1 := by
          rcases (mem_frontier_placedStrip (has.trans hsb).le).mp hz.2 with h | h
          · exact h.2
          · rcases h.1 with h | h <;> linarith [hw.1]
        rcases ht with ht | ht
        · have hz0 : z = seamWitnessPlane (s, 0) := by
            apply seamWitnessPlane.symm.injective
            simpa using Prod.ext hw.1 ht
          exact hz0 ▸ hTcut.snd.left_mem
        · have hz1 : z = seamWitnessPlane (s, 1) := by
            apply seamWitnessPlane.symm.injective
            simpa using Prod.ext hw.1 ht
          exact hz1 ▸ hTcut.snd.right_mem
      · exact hzT
  exact ⟨hleft ▸ hR, hleft ▸ hRcut, hright ▸ hT, hright ▸ hTcut⟩

private theorem crossingProductCell_on_wall {s : ℝ} (hs : s = 3 / 2 ∨ s = 7 / 2)
    (t : ℝ) : crossingProductCell (seamWitnessPlane (s, t)) =
      spliceEmbedding ((0, 0), t) := by
  change spliceEmbedding (crossingProductMap (seamWitnessPlane.symm
    (seamWitnessPlane (s, t)))) = _
  rw [seamWitnessPlane.symm_apply_apply]
  rcases hs with rfl | rfl
  · rw [crossingProductMap_core_first]
  · rw [crossingProductMap_core_second]

private theorem crossingProductCell_image_wall {s : ℝ} (hs : s = 3 / 2 ∨ s = 7 / 2) :
    crossingProductCell '' placedWall s = spliceEmbedding '' spliceCore := by
  apply Subset.antisymm
  · rintro y ⟨z, ⟨⟨r, t⟩, ⟨rfl, ht⟩, rfl⟩, rfl⟩
    rw [crossingProductCell_on_wall hs]
    exact ⟨((0, 0), t), ⟨rfl, ht⟩, rfl⟩
  · rintro y ⟨⟨⟨a, b⟩, t⟩, ⟨h, ht⟩, rfl⟩
    have hab : (a, b) = ((0 : ℝ), (0 : ℝ)) := h
    refine ⟨seamWitnessPlane (s, t), ⟨(s, t), ⟨rfl, ht⟩, rfl⟩, ?_⟩
    rw [crossingProductCell_on_wall hs, hab]

private theorem crossingProductCell_injOn_wall {s : ℝ} (hs : s = 3 / 2 ∨ s = 7 / 2) :
    InjOn (⇑crossingProductCell) (placedWall s) := by
  rintro z ⟨⟨r, t⟩, ⟨rfl, ht⟩, rfl⟩ w ⟨⟨r, u⟩, ⟨rfl, hu⟩, rfl⟩ heq
  rw [crossingProductCell_on_wall hs, crossingProductCell_on_wall hs] at heq
  have htu : t = u := congrArg Prod.snd (spliceEmbedding.injective heq)
  rw [htu]

private theorem crossingProductCell_branchPreimage_wall
    {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore) :
    hD.branchPreimage c = placedWall (3 / 2) ∪ placedWall (7 / 2) := by
  ext z
  change (z ∈ crossingProductCell.domain ∧ crossingProductCell z ∈
    hD.singularSet.branchCarrier c) ↔ _
  rw [hc]
  constructor
  · rintro ⟨hz, ⟨⟨⟨a, b⟩, t⟩, ⟨h, ht⟩, heq⟩⟩
    have hab : (a, b) = ((0 : ℝ), (0 : ℝ)) := h
    have hval : crossingProductMap (seamWitnessPlane.symm z) =
        crossingProductMap (3 / 2, t) := by
      rw [crossingProductMap_core_first]
      exact spliceEmbedding.injective (heq.symm.trans (by rw [hab]))
    have hmem := mem_image_seamWitnessPlane.mp hz
    have hfiber := (crossingProductMap_eq_iff hmem.1 (by norm_num)).mp hval
    rcases hfiber.2 with he | ⟨he, he'⟩ | ⟨he, he'⟩ | ⟨he, he'⟩ | ⟨he, he'⟩
    · exact Or.inl (mem_placedWall.mpr ⟨he, hmem.2⟩)
    · norm_num at he'
    · exact Or.inr (mem_placedWall.mpr ⟨he, hmem.2⟩)
    · norm_num at he'
    · norm_num at he'
  · rintro (hz | hz)
    · refine ⟨?_, crossingProductCell_image_wall (Or.inl rfl) ▸ mem_image_of_mem _ hz⟩
      rw [show crossingProductCell.domain = placedStrip 0 5 from rfl, mem_placedStrip]
      have h := mem_placedWall.mp hz
      exact ⟨by rw [h.1]; norm_num, h.2⟩
    · refine ⟨?_, crossingProductCell_image_wall (Or.inr rfl) ▸ mem_image_of_mem _ hz⟩
      rw [show crossingProductCell.domain = placedStrip 0 5 from rfl, mem_placedStrip]
      have h := mem_placedWall.mp hz
      exact ⟨by rw [h.1]; norm_num, h.2⟩

private theorem crossingProductCell_branchCoordinate_wall
    {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore)
    {s : ℝ} (hs : s = 3 / 2 ∨ s = 7 / 2) :
    IsPLHomeomorphOn (hD.branchCoordinate c) (placedWall s)
      (hD.singularSet.branchComplex c).space := by
  have hsub : placedWall s ⊆ hD.branchPreimage c := by
    rw [crossingProductCell_branchPreimage_wall hD hc]
    rcases hs with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isPLBall_placedWall s).isPolyhedron
    ((hD.branchCoordinate_isPiecewiseAffineOn c).mono_of_isPolyhedron
      (isPLBall_placedWall s).isPolyhedron hsub)
  refine ⟨fun _ hz => hD.branchCoordinate_mem c (hsub hz), ?_, ?_⟩
  · intro z hz w hw heq
    apply crossingProductCell_injOn_wall hs hz hw
    rw [← hD.branchPieceIn_map_branchCoordinate c (hsub hz),
      ← hD.branchPieceIn_map_branchCoordinate c (hsub hw), heq]
  · intro v hv
    have hvimage := (hD.singularSet.branchPieceIn c).bijOn.mapsTo hv
    have hvimage' := (crossingProductCell_image_wall hs).symm.subset (hc.subset hvimage)
    obtain ⟨z, hz, heq⟩ := hvimage'
    refine ⟨z, hz, ?_⟩
    apply (hD.singularSet.branchPieceIn c).bijOn.injOn
      (hD.branchCoordinate_mem c (hsub hz)) hv
    rw [hD.branchPieceIn_map_branchCoordinate c (hsub hz), heq]

private noncomputable def stripShift : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
    EuclideanSpace ℝ (Fin 2) where
  toFun z := z + seamWitnessPlane (2, 0)
  linear := LinearMap.id
  map_vadd' z v := by simp [add_assoc]

private theorem stripShift_apply (s t : ℝ) :
    stripShift (seamWitnessPlane (s, t)) = seamWitnessPlane (s + 2, t) := by
  change seamWitnessPlane (s, t) + seamWitnessPlane (2, 0) = _
  rw [← map_add]
  congr 1
  simp

private theorem isPLHomeomorphOn_stripShift :
    IsPLHomeomorphOn (⇑stripShift) (placedWall (3 / 2)) (placedWall (7 / 2)) := by
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isPLBall_placedWall (3 / 2)).isPolyhedron
    ((isPiecewiseAffineOn_of_affine stripShift isOpen_univ).mono_of_isPolyhedron
      (isPLBall_placedWall (3 / 2)).isPolyhedron (subset_univ _))
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨⟨s, t⟩, ⟨rfl, ht⟩, rfl⟩
    rw [stripShift_apply]
    exact ⟨(7 / 2, t), ⟨rfl, ht⟩, by norm_num⟩
  · intro z _ w _ heq
    exact add_right_cancel heq
  · rintro z ⟨⟨s, t⟩, ⟨rfl, ht⟩, rfl⟩
    refine ⟨seamWitnessPlane (3 / 2, t), ⟨(3 / 2, t), ⟨rfl, ht⟩, rfl⟩, ?_⟩
    rw [stripShift_apply]
    norm_num

theorem crossingProductCell_exists_preserving_cut {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore) :
    ∃ D₁ D₂ D₃ : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      hD.IsBoundaryBranchCut c
        (seamWitnessPlane '' ({(3 / 2 : ℝ)} ×ˢ Icc (0 : ℝ) 1))
        (seamWitnessPlane '' ({(7 / 2 : ℝ)} ×ˢ Icc (0 : ℝ) 1))
        (seamWitnessPlane (3 / 2, 0)) (seamWitnessPlane (3 / 2, 1))
        (seamWitnessPlane (7 / 2, 0)) (seamWitnessPlane (7 / 2, 1))
        (fun z => z + seamWitnessPlane (2, 0)) D₁ D₂ D₃ ∧
      D₁.domain = seamWitnessPlane '' (Icc (0 : ℝ) (3 / 2) ×ˢ Icc (0 : ℝ) 1) ∧
      D₂.domain = seamWitnessPlane '' (Icc (3 / 2 : ℝ) (7 / 2) ×ˢ Icc (0 : ℝ) 1) ∧
      D₃.domain = seamWitnessPlane '' (Icc (7 / 2 : ℝ) 5 ×ˢ Icc (0 : ℝ) 1) := by
  have h₁ := isPLBall_placedStrip (by norm_num : (0 : ℝ) < 3 / 2)
  have h₂ := isPLBall_placedStrip (by norm_num : (3 / 2 : ℝ) < 7 / 2)
  have h₃ := isPLBall_placedStrip (by norm_num : (7 / 2 : ℝ) < 5)
  let D₁ := crossingProductCell.restrict h₁
    (placedStrip_subset (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (3 / 2 : ℝ) ≤ 5))
  let D₂ := crossingProductCell.restrict h₂
    (placedStrip_subset (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (7 / 2 : ℝ) ≤ 5))
  let D₃ := crossingProductCell.restrict h₃
    (placedStrip_subset (by norm_num : (0 : ℝ) ≤ 7 / 2) (by norm_num : (5 : ℝ) ≤ 5))
  refine ⟨D₁, D₂, D₃, ?_, rfl, rfl, rfl⟩
  have htrace₁ := exists_placedStrip_trace_cut
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 5)
  have htrace₃ := exists_placedStrip_trace_cut
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (7 / 2 : ℝ) < 5)
  refine ⟨isPLBall_placedWall _, isPLBall_placedWall _, ?_,
    crossingProductCell_branchPreimage_wall hD hc,
    crossingProductCell_branchCoordinate_wall hD hc (Or.inl rfl),
    crossingProductCell_branchCoordinate_wall hD hc (Or.inr rfl),
    isPLHomeomorphOn_stripShift, ?_, ?_,
    placedStrip_inter (by norm_num) (by norm_num),
    placedStrip_inter (by norm_num) (by norm_num),
    placedWall_subset_frontier_right (by norm_num),
    placedWall_subset_frontier_left (by norm_num),
    placedWall_subset_frontier_right (by norm_num),
    placedWall_subset_frontier_left (by norm_num),
    placedStrip_disjoint (by norm_num), rfl, rfl, rfl,
    htrace₁.1, htrace₃.2.2.1, htrace₁.2.1, htrace₃.2.2.2⟩
  · apply disjoint_left.mpr
    intro z hz hw
    have hz' := mem_placedWall.mp hz
    have hw' := mem_placedWall.mp hw
    linarith [hz'.1, hw'.1]
  · rintro z ⟨⟨s, t⟩, ⟨rfl, ht⟩, rfl⟩
    change crossingProductCell (seamWitnessPlane (3 / 2, t)) =
      crossingProductCell (stripShift (seamWitnessPlane (3 / 2, t)))
    rw [stripShift_apply]
    norm_num only at *
    rw [crossingProductCell_on_wall (Or.inl rfl),
      crossingProductCell_on_wall (Or.inr rfl)]
  · change placedStrip 0 (3 / 2) ∪ placedStrip (3 / 2) (7 / 2) ∪ placedStrip (7 / 2) 5 =
      placedStrip 0 5
    rw [placedStrip_union (by norm_num) (by norm_num),
      placedStrip_union (by norm_num) (by norm_num)]

private noncomputable def reflectionAffine : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun z := (5 - z.1, z.2)
  linear := (-LinearMap.fst ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ)
  map_vadd' z v := by
    ext <;> simp [sub_eq_add_neg]
    ring

private noncomputable def stripReflection : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ]
    EuclideanSpace ℝ (Fin 2) :=
  seamWitnessPlane.toLinearMap.toAffineMap.comp
    (reflectionAffine.comp seamWitnessPlane.symm.toLinearMap.toAffineMap)

private theorem stripReflection_apply (s t : ℝ) :
    stripReflection (seamWitnessPlane (s, t)) = seamWitnessPlane (5 - s, t) := by
  change seamWitnessPlane (5 - (seamWitnessPlane.symm
    (seamWitnessPlane (s, t))).1, (seamWitnessPlane.symm (seamWitnessPlane (s, t))).2) = _
  rw [seamWitnessPlane.symm_apply_apply]

private theorem stripReflection_involutive : Function.Involutive stripReflection := by
  intro z
  obtain ⟨⟨s, t⟩, rfl⟩ := seamWitnessPlane.surjective z
  rw [stripReflection_apply, stripReflection_apply]
  congr 1
  exact Prod.ext (by ring) rfl

private theorem stripReflection_mapsTo :
    MapsTo (⇑stripReflection) (placedStrip (3 / 2) (7 / 2))
      (placedStrip (3 / 2) (7 / 2)) := by
  rintro z ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  rw [stripReflection_apply]
  exact ⟨(5 - s, t), ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, ht⟩, rfl⟩

private theorem isPLHomeomorphOn_stripReflection :
    IsPLHomeomorphOn (⇑stripReflection) (placedStrip (3 / 2) (7 / 2))
      (placedStrip (3 / 2) (7 / 2)) := by
  have hpoly := (isPLBall_placedStrip (by norm_num : (3 / 2 : ℝ) < 7 / 2)).isPolyhedron
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine stripReflection isOpen_univ).mono_of_isPolyhedron
      hpoly (subset_univ _))
  exact ⟨stripReflection_mapsTo, stripReflection_involutive.injective.injOn,
    fun z hz => ⟨stripReflection z, stripReflection_mapsTo hz, stripReflection_involutive z⟩⟩

private theorem stripReflection_image_wall (s : ℝ) :
    stripReflection '' placedWall s = placedWall (5 - s) := by
  apply Subset.antisymm
  · rintro z ⟨w, ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩, rfl⟩
    have hr' : r = s := hr
    subst r
    rw [stripReflection_apply]
    exact ⟨(5 - s, t), ⟨rfl, ht⟩, rfl⟩
  · rintro z ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    have hr' : r = 5 - s := hr
    subst r
    exact ⟨seamWitnessPlane (s, t), ⟨(s, t), ⟨rfl, ht⟩, rfl⟩, stripReflection_apply s t⟩

private theorem stripReflection_invFunOn {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ placedStrip (3 / 2) (7 / 2)) :
    Function.invFunOn (⇑stripReflection) (placedStrip (3 / 2) (7 / 2)) z =
      stripReflection z := by
  apply stripReflection_involutive.injective
  rw [isPLHomeomorphOn_stripReflection.bijOn.invOn_invFunOn.2 hz,
    stripReflection_involutive]

private theorem crossRegluedProductCell_eq_left :
    EqOn (⇑crossRegluedProductCell) (⇑crossingProductCell) (placedStrip 0 (3 / 2)) := by
  intro z hz
  have hz' := mem_placedStrip.mp hz
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm z)) =
    spliceEmbedding (crossingProductMap (seamWitnessPlane.symm z))
  rw [crossingProductMap_eq_crossRegluedProductMap_of_le hz'.1.2]

private theorem crossRegluedProductCell_eq_right :
    EqOn (⇑crossRegluedProductCell) (⇑crossingProductCell) (placedStrip (7 / 2) 5) := by
  intro z hz
  have hz' := mem_placedStrip.mp hz
  change spliceEmbedding (crossRegluedProductMap (seamWitnessPlane.symm z)) =
    spliceEmbedding (crossingProductMap (seamWitnessPlane.symm z))
  rw [crossingProductMap_eq_crossRegluedProductMap_of_ge hz'.1.1]

private theorem crossRegluedProductCell_eq_middle :
    EqOn (⇑crossRegluedProductCell) (⇑crossingProductCell ∘ ⇑stripReflection)
      (placedStrip (3 / 2) (7 / 2)) := by
  rintro z ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  simp only [Function.comp_apply, stripReflection_apply]
  change spliceEmbedding (crossRegluedProductMap
    (seamWitnessPlane.symm (seamWitnessPlane (s, t)))) =
    spliceEmbedding (crossingProductMap (seamWitnessPlane.symm (seamWitnessPlane (5 - s, t))))
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [crossRegluedProductMap_eq_crossingProductMap_reflection hs.1 hs.2]

private theorem stripReflection_mapsTo_middle_trace :
    MapsTo (⇑stripReflection)
      (placedStrip (3 / 2) (7 / 2) ∩ frontier (placedStrip 0 5))
      (placedStrip (3 / 2) (7 / 2) ∩ frontier (placedStrip 0 5)) := by
  intro z hz
  refine ⟨stripReflection_mapsTo hz.1, ?_⟩
  have hz' := mem_placedStrip.mp hz.1
  obtain ⟨⟨s, t⟩, rfl⟩ := seamWitnessPlane.surjective z
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hz'
  rw [stripReflection_apply, mem_frontier_placedStrip (by norm_num : (0 : ℝ) ≤ 5)]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hzt := (mem_frontier_placedStrip (by norm_num : (0 : ℝ) ≤ 5)).mp hz.2
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hzt
  refine Or.inl ⟨⟨by linarith [hz'.1.2], by linarith [hz'.1.1]⟩, ?_⟩
  rcases hzt with ht | ⟨hs, -⟩
  · exact ht.2
  · rcases hs with hs | hs <;> linarith [hz'.1.1, hz'.1.2]

private theorem crossRegluedProductCell_image_middle_trace :
    crossRegluedProductCell ''
      (placedStrip (3 / 2) (7 / 2) ∩ frontier (placedStrip 0 5)) =
    crossingProductCell ''
      (placedStrip (3 / 2) (7 / 2) ∩ frontier (placedStrip 0 5)) := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨stripReflection z, stripReflection_mapsTo_middle_trace hz,
      (crossRegluedProductCell_eq_middle hz.1).symm⟩
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨stripReflection z, stripReflection_mapsTo_middle_trace hz, ?_⟩
    rw [crossRegluedProductCell_eq_middle (stripReflection_mapsTo hz.1)]
    exact congrArg crossingProductCell (stripReflection_involutive z)

private theorem crossRegluedProductCell_image_left_trace :
    crossRegluedProductCell '' (placedStrip 0 (7 / 2) ∩ frontier (placedStrip 0 5)) =
    crossingProductCell '' (placedStrip 0 (7 / 2) ∩ frontier (placedStrip 0 5)) := by
  rw [← placedStrip_union (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (by norm_num : (3 / 2 : ℝ) ≤ 7 / 2), union_inter_distrib_right, image_union, image_union,
    image_congr (crossRegluedProductCell_eq_left.mono inter_subset_left),
    crossRegluedProductCell_image_middle_trace]

private theorem crossRegluedProductCell_core_double {t : ℝ} (ht : t ∈ Icc 0 1) :
    spliceEmbedding ((0, 0), t) ∈
      doublePointSet (⇑crossRegluedProductCell) crossRegluedProductCell.domain := by
  have hp : seamWitnessPlane (3 / 2, t) ∈ placedStrip 0 (3 / 2) :=
    ⟨(3 / 2, t), ⟨⟨by norm_num, le_rfl⟩, ht⟩, rfl⟩
  have hq : seamWitnessPlane (7 / 2, t) ∈ placedStrip (7 / 2) 5 :=
    ⟨(7 / 2, t), ⟨⟨le_rfl, by norm_num⟩, ht⟩, rfl⟩
  refine ⟨seamWitnessPlane (3 / 2, t), placedStrip_subset (by norm_num) (by norm_num) hp,
    seamWitnessPlane (7 / 2, t), placedStrip_subset (by norm_num) (by norm_num) hq, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg Prod.fst (seamWitnessPlane.injective h)
    norm_num at h'
  · rw [crossRegluedProductCell_eq_left hp, crossingProductCell_on_wall (Or.inl rfl)]
  · rw [crossRegluedProductCell_eq_right hq, crossingProductCell_on_wall (Or.inr rfl)]

theorem crossRegluedProductCell_isCrossRegluedCell {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore) :
    hD.IsCrossRegluedCell c crossRegluedProductCell := by
  classical
  obtain ⟨D₁, D₂, D₃, hcut, -⟩ := crossingProductCell_exists_preserving_cut hD hc
  obtain ⟨hA, hC, hAC, hpre, -, -, hg, hcompat, -⟩ := hcut
  let P := placedStrip 0 (3 / 2)
  let Q := placedStrip (3 / 2) (7 / 2)
  let P' := placedStrip 0 (7 / 2)
  let Q' := placedStrip (7 / 2) 5
  let R := P' ∩ frontier (placedStrip 0 5)
  let T := Q' ∩ frontier (placedStrip 0 5)
  have hP : IsPLBall 2 P := isPLBall_placedStrip (by norm_num)
  have hQ : IsPLBall 2 Q := isPLBall_placedStrip (by norm_num)
  have hP' : IsPLBall 2 P' := isPLBall_placedStrip (by norm_num)
  have hQ' : IsPLBall 2 Q' := isPLBall_placedStrip (by norm_num)
  have hPQ : P ∪ Q = P' := placedStrip_union (by norm_num) (by norm_num)
  have hPQ' : P' ∪ Q' = placedStrip 0 5 := placedStrip_union (by norm_num) (by norm_num)
  have hI : P ∩ Q = placedWall (3 / 2) := placedStrip_inter (by norm_num) (by norm_num)
  have hI' : P' ∩ Q' = placedWall (7 / 2) := placedStrip_inter (by norm_num) (by norm_num)
  have hAin : placedWall (3 / 2) ⊆ Q := by
    rw [← hI]
    exact inter_subset_right
  let H := crossRegluedProductCell.restrict hP'
    (placedStrip_subset (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (7 / 2 : ℝ) ≤ 5))
  have htrace := exists_placedStrip_trace_cut
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (7 / 2 : ℝ) < 5)
  have hRcut : Schoenflies.IsCutPair (frontier P')
      (seamWitnessPlane (7 / 2, 0)) (seamWitnessPlane (7 / 2, 1)) (P' ∩ Q') R :=
    hI'.symm ▸ htrace.2.1
  have hTcut : Schoenflies.IsCutPair (frontier Q')
      (seamWitnessPlane (7 / 2, 0)) (seamWitnessPlane (7 / 2, 1)) (P' ∩ Q') T :=
    hI'.symm ▸ htrace.2.2.2
  have hfront : frontier crossRegluedProductCell.domain = R ∪ T := by
    change frontier (placedStrip 0 5) =
      P' ∩ frontier (placedStrip 0 5) ∪ Q' ∩ frontier (placedStrip 0 5)
    rw [← union_inter_distrib_right, hPQ', inter_eq_right.mpr
      (isPLBall_placedStrip (by norm_num : (0 : ℝ) < 5)).isPolyhedron.isClosed.frontier_subset]
  have hRT : R ∩ T =
      {seamWitnessPlane (7 / 2, 0), seamWitnessPlane (7 / 2, 1)} := by
    apply Subset.antisymm
    · intro z hz
      exact hRcut.inter_eq.subset ⟨⟨hz.1.1, hz.2.1⟩, hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hRcut.snd.left_mem, hTcut.snd.left_mem⟩
      · exact ⟨hRcut.snd.right_mem, hTcut.snd.right_mem⟩
  have hGR : crossRegluedProductCell '' R = crossingProductCell '' R :=
    crossRegluedProductCell_image_left_trace
  have hGT : crossRegluedProductCell '' T = crossingProductCell '' T :=
    image_congr (crossRegluedProductCell_eq_right.mono inter_subset_left)
  have hGfront : crossRegluedProductCell '' frontier crossRegluedProductCell.domain =
      crossingProductCell '' frontier crossingProductCell.domain := by
    change crossRegluedProductCell '' frontier crossRegluedProductCell.domain =
      crossingProductCell '' frontier crossRegluedProductCell.domain
    rw [hfront, image_union, image_union, hGR, hGT]
  have hshiftreflect : EqOn (⇑stripShift ∘ ⇑stripReflection) id (placedWall (7 / 2)) := by
    rintro z ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    have hs' : s = 7 / 2 := hs
    subst s
    simp only [Function.comp_apply, stripReflection_apply, stripShift_apply, id_eq]
    norm_num
  have hkinv : Function.invFunOn (⇑stripReflection) Q '' placedWall (3 / 2) =
      placedWall (7 / 2) := by
    rw [image_congr (fun z hz => stripReflection_invFunOn (hAin hz)),
      stripReflection_image_wall]
    norm_num
  obtain ⟨a', b', ρ, κ, e, hρrange, hκrange, he, hρinj, hκinj⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union hRcut.snd hTcut.snd hRT hfront
  let σ := ρ.map crossRegluedProductCell.boundary.continuous
  let ω := κ.map crossRegluedProductCell.boundary.continuous
  have hσrange : Set.range σ = crossRegluedProductCell '' R := by
    change Set.range (⇑crossRegluedProductCell ∘ fun t =>
      (ρ t : EuclideanSpace ℝ (Fin 2))) = _
    rw [Set.range_comp, hρrange]
  have hωrange : Set.range ω = crossRegluedProductCell '' T := by
    change Set.range (⇑crossRegluedProductCell ∘ fun t =>
      (κ t : EuclideanSpace ℝ (Fin 2))) = _
    rw [Set.range_comp, hκrange]
  have heG : ∀ θ, crossRegluedProductCell (e θ) = pathToCircle (σ.trans ω) θ := by
    intro θ
    rw [he θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map crossRegluedProductCell.boundary.continuous) t = (σ.trans ω) t
    rw [Path.map_trans]
  have hp : seamWitnessPlane (3 / 2, 0) ∈ placedWall (3 / 2) :=
    ⟨(3 / 2, 0), ⟨rfl, by norm_num⟩, rfl⟩
  have hq : seamWitnessPlane (3 / 2, 1) ∈ placedWall (3 / 2) :=
    ⟨(3 / 2, 1), ⟨rfl, by norm_num⟩, rfl⟩
  have hr : seamWitnessPlane (7 / 2, 0) ∈ placedWall (7 / 2) :=
    ⟨(7 / 2, 0), ⟨rfl, by norm_num⟩, rfl⟩
  have hs : seamWitnessPlane (7 / 2, 1) ∈ placedWall (7 / 2) :=
    ⟨(7 / 2, 1), ⟨rfl, by norm_num⟩, rfl⟩
  refine ⟨placedWall (3 / 2), placedWall (7 / 2), P, Q, Q', P, Q, P', Q',
    placedWall (7 / 2), R, T, seamWitnessPlane (3 / 2, 0), seamWitnessPlane (3 / 2, 1),
    seamWitnessPlane (7 / 2, 0), seamWitnessPlane (7 / 2, 1),
    seamWitnessPlane (7 / 2, 0), seamWitnessPlane (7 / 2, 1),
    ⇑stripShift, id, ⇑stripReflection, id, id, H, hA, hC, hAC, hpre, hg, hcompat,
    hp, hq, hr, hs, ?_, hPQ ▸ hPQ', hI,
    placedStrip_inter (by norm_num) (by norm_num), placedStrip_disjoint (by norm_num),
    hP, hQ, hPQ.symm, hP.isPolyhedron.isPLHomeomorphOn_id, isPLHomeomorphOn_stripReflection,
    ?_, ?_, crossRegluedProductCell_eq_left, crossRegluedProductCell_eq_middle, hkinv.symm,
    hC, ?_, placedWall_subset_frontier_right (by norm_num), ?_,
    hP', hQ', hPQ'.symm, hP'.isPolyhedron.isPLHomeomorphOn_id,
    hQ'.isPolyhedron.isPLHomeomorphOn_id, ?_, ?_, fun _ _ => rfl,
    crossRegluedProductCell_eq_right, hRcut, hTcut, htrace.1, htrace.2.2.1, hfront,
    ?_, ?_, ?_, ?_, crossingProductCell_image.symm.subset, ?_,
    crossRegluedProductCell a', crossRegluedProductCell b', σ, ω, e,
    hσrange, hωrange, heG, ?_, hGT, hGfront, a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, he⟩
  · exact Or.inl ⟨by rw [stripShift_apply]; norm_num,
      by rw [stripShift_apply]; norm_num⟩
  · simpa only [image_id] using hI
  · rw [hI, stripReflection_image_wall]
    norm_num
  · rw [hI]
    exact hAC.symm
  · exact hC.isPolyhedron.isPLHomeomorphOn_id.congr hshiftreflect
  · simpa only [image_id] using hI'
  · simpa only [image_id] using hI'
  · change _ = Function.invFunOn (⇑stripReflection) Q _
    rw [stripReflection_invFunOn (hAin hp), stripReflection_apply]
    norm_num
  · change _ = Function.invFunOn (⇑stripReflection) Q _
    rw [stripReflection_invFunOn (hAin hq), stripReflection_apply]
    norm_num
  · rw [stripShift_apply]
    norm_num
  · rw [stripShift_apply]
    norm_num
  · rw [hc]
    rintro y ⟨⟨⟨x, y⟩, t⟩, ⟨hxy, ht⟩, rfl⟩
    have hxy' : (x, y) = ((0 : ℝ), (0 : ℝ)) := hxy
    rw [hxy']
    exact crossRegluedProductCell_core_double ht
  · rw [hPQ]
    exact hGR

theorem crossingProductCell_exists_crossReading {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : Set.range crossingProductCell.boundary ⊆ B) :
    ∃ (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
      (c d : hD.singularSet.Branch)
      (T : CrossSeamTubeData hD c (spliceEmbedding '' tubeWitnessTube)),
      hD.singularSet.complexity = 2 ∧ c ≠ d ∧
      hD.singularSet.IsBoundaryBranch c ∧ hD.singularSet.IsBoundaryBranch d ∧
      hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore ∧
      hD.singularSet.branchCarrier d = crossingProductBranchCarrier true ∧
      hD.IsCrossRegluedCell c crossRegluedProductCell ∧
      T.chart = ⇑spliceEmbedding ∧
      Nonempty (PLSeamTubeChart (EuclideanSpace ℝ (Fin 3)) T.chart) ∧
      Nonempty (PLCrossSeamReading T.chart crossRegluedProductCell) ∧
      T.chart '' spliceCylinder ⊆ crossingProductSide ∧
      T.chart '' spliceCylinder ∩ frontier crossingProductSide = T.chart '' spliceEndDisks := by
  obtain ⟨hD⟩ := crossingProductCell_nonempty_normalSingularCellData hB
  obtain ⟨c, d, T, hcd, hc, hd, hcore, hcurl, hchart, hPL, hside, hbd⟩ :=
    crossingProductCell_exists_boundaryTube hD
  refine ⟨hD, c, d, T, crossingProductCell_complexity_eq_two hD.singularSet,
    hcd, hc, hd, hcore, hcurl, crossRegluedProductCell_isCrossRegluedCell hD hcore,
    hchart, hPL, ?_, hside, hbd⟩
  rw [hchart]
  exact ⟨crossRegluedProductReading⟩

private def placedHorizontal (t : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc (3 / 2 : ℝ) (7 / 2) ×ˢ {t})

private theorem mem_placedHorizontal {t : ℝ} {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ placedHorizontal t ↔
      (seamWitnessPlane.symm z).1 ∈ Icc (3 / 2 : ℝ) (7 / 2) ∧
        (seamWitnessPlane.symm z).2 = t := mem_image_seamWitnessPlane

private theorem isArcBetween_placedHorizontal (t : ℝ) :
    Schoenflies.IsArcBetween (placedHorizontal t)
      (seamWitnessPlane (3 / 2, t)) (seamWitnessPlane (7 / 2, t)) := by
  refine ⟨fun r => seamWitnessPlane (3 / 2 + 2 * r, t),
    (seamWitnessPlane.continuous.comp
      ((continuous_const.add (continuous_const.mul continuous_id)).prodMk
        continuous_const)).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro u _ v _ huv
    have := congrArg Prod.fst (seamWitnessPlane.injective huv)
    dsimp at this
    linarith
  · apply Subset.antisymm
    · rintro z ⟨r, hr, rfl⟩
      refine ⟨(3 / 2 + 2 * r, t), ⟨⟨?_, ?_⟩, rfl⟩, rfl⟩ <;>
        linarith [hr.1, hr.2]
    · rintro z ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
      have hs' : s = t := hs
      subst s
      refine ⟨(r - 3 / 2) / 2, ⟨?_, ?_⟩, ?_⟩
      · linarith [hr.1]
      · linarith [hr.2]
      · change seamWitnessPlane (3 / 2 + 2 * ((r - 3 / 2) / 2), t) = _
        congr 1
        exact Prod.ext (by ring) rfl
  · norm_num
  · norm_num

private theorem exists_product_boundary_paths :
    ∃ (p q u v : frontier crossingProductCell.domain)
      (σ : Path p q) (τ : Path q u) (υ : Path u v) (φ : Path v p)
      (e : loopCircle ≃ₜ frontier crossingProductCell.domain),
      (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 0) ∧
      (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 1) ∧
      (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 1) ∧
      (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 0) ∧
      Set.range (fun t => (σ t : EuclideanSpace ℝ (Fin 2))) =
        placedStrip 0 (3 / 2) ∩ frontier crossingProductCell.domain ∧
      Set.range (fun t => (τ t : EuclideanSpace ℝ (Fin 2))) = placedHorizontal 1 ∧
      Set.range (fun t => (υ t : EuclideanSpace ℝ (Fin 2))) =
        placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain ∧
      Set.range (fun t => (φ t : EuclideanSpace ℝ (Fin 2))) = placedHorizontal 0 ∧
      (∀ θ, e θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      Function.Injective σ ∧ Function.Injective τ ∧
      Function.Injective υ ∧ Function.Injective φ := by
  have hleft := (exists_placedStrip_trace_cut
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 5)).2.1.snd
  have hright := (exists_placedStrip_trace_cut
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (7 / 2 : ℝ) < 5)).2.2.2.snd.reverse
  have hthree : ∀ z ∈ placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain,
      z ∈ placedHorizontal 0 → z = seamWitnessPlane (7 / 2, 0) := by
    intro z hz hbot
    have h₁ := mem_placedStrip.mp hz.1
    have h₂ := mem_placedHorizontal.mp hbot
    apply seamWitnessPlane.symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext (by linarith [h₁.1.1, h₂.1.2]) h₂.2
  have htwo : ∀ z ∈ placedHorizontal 1,
      z ∈ (placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain) ∪
        placedHorizontal 0 → z = seamWitnessPlane (7 / 2, 1) := by
    intro z hz hz'
    have h₂ := mem_placedHorizontal.mp hz
    rcases hz' with hz' | hz'
    · have h₃ := mem_placedStrip.mp hz'.1
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₂.1.2, h₃.1.1]) h₂.2
    · have h₄ := mem_placedHorizontal.mp hz'
      exact (by linarith [h₂.2, h₄.2] : False).elim
  have hone : ∀ z ∈ placedStrip 0 (3 / 2) ∩ frontier crossingProductCell.domain,
      z ∈ placedHorizontal 1 ∪
        ((placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain) ∪
          placedHorizontal 0) →
        z = seamWitnessPlane (3 / 2, 0) ∨ z = seamWitnessPlane (3 / 2, 1) := by
    intro z hz hz'
    have h₁ := mem_placedStrip.mp hz.1
    rcases hz' with hz' | hz' | hz'
    · have h₂ := mem_placedHorizontal.mp hz'
      right
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₁.1.2, h₂.1.1]) h₂.2
    · have h₃ := mem_placedStrip.mp hz'.1
      exact (by linarith [h₁.1.2, h₃.1.1] : False).elim
    · have h₄ := mem_placedHorizontal.mp hz'
      left
      apply seamWitnessPlane.symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext (by linarith [h₁.1.2, h₄.1.1]) h₄.2
  have hfront : frontier crossingProductCell.domain =
      (placedStrip 0 (3 / 2) ∩ frontier crossingProductCell.domain) ∪
        (placedHorizontal 1 ∪
          ((placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain) ∪
            placedHorizontal 0)) := by
    ext z
    have hfrontz : z ∈ frontier crossingProductCell.domain ↔
        ((seamWitnessPlane.symm z).1 ∈ Icc (0 : ℝ) 5 ∧
          ((seamWitnessPlane.symm z).2 = 0 ∨ (seamWitnessPlane.symm z).2 = 1)) ∨
        (((seamWitnessPlane.symm z).1 = 0 ∨ (seamWitnessPlane.symm z).1 = 5) ∧
          (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1) :=
      mem_frontier_placedStrip (by norm_num)
    simp only [mem_union, mem_inter_iff, mem_placedStrip, mem_placedHorizontal, hfrontz,
      mem_Icc]
    constructor
    · rintro (⟨hs, ht | ht⟩ | ⟨hs | hs, ht⟩)
      · by_cases h : (seamWitnessPlane.symm z).1 ≤ 3 / 2
        · exact Or.inl ⟨⟨⟨hs.1, h⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inl ht⟩⟩
        · by_cases h' : 7 / 2 ≤ (seamWitnessPlane.symm z).1
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨⟨h', hs.2⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inl ht⟩⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨⟨by linarith, by linarith⟩, ht⟩))
      · by_cases h : (seamWitnessPlane.symm z).1 ≤ 3 / 2
        · exact Or.inl ⟨⟨⟨hs.1, h⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inr ht⟩⟩
        · by_cases h' : 7 / 2 ≤ (seamWitnessPlane.symm z).1
          · exact Or.inr (Or.inr (Or.inl
              ⟨⟨⟨h', hs.2⟩, by rw [ht]; norm_num⟩, Or.inl ⟨hs, Or.inr ht⟩⟩))
          · exact Or.inr (Or.inl ⟨⟨by linarith, by linarith⟩, ht⟩)
      · exact Or.inl ⟨⟨by rw [hs]; norm_num, ht⟩, Or.inr ⟨Or.inl hs, ht⟩⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨⟨by rw [hs]; norm_num, ht⟩, Or.inr ⟨Or.inr hs, ht⟩⟩))
    · rintro (⟨-, h⟩ | ⟨hs, ht⟩ | ⟨-, h⟩ | ⟨hs, ht⟩)
      · exact h
      · exact Or.inl ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, Or.inr ht⟩
      · exact h
      · exact Or.inl ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, Or.inl ht⟩
  obtain ⟨p, q, u, v, σ, τ, υ, φ, e, hbody, hinj⟩ :=
    exists_injective_boundaryParam_four_paths hleft (isArcBetween_placedHorizontal 1)
      hright (isArcBetween_placedHorizontal 0).reverse hthree htwo hone hfront
  exact ⟨p, q, u, v, σ, τ, υ, φ, e, hbody.1, hbody.2.1, hbody.2.2.1,
    hbody.2.2.2.1, hbody.2.2.2.2.1, hbody.2.2.2.2.2.1,
    hbody.2.2.2.2.2.2.1, hbody.2.2.2.2.2.2.2.1, hbody.2.2.2.2.2.2.2.2, hinj⟩

private theorem stripReflection_mapsTo_horizontal (t : ℝ) :
    MapsTo stripReflection (placedHorizontal t) (placedHorizontal t) := by
  rintro z ⟨⟨s, r⟩, ⟨hs, hr⟩, rfl⟩
  have hr' : r = t := hr
  subst r
  rw [stripReflection_apply]
  exact ⟨(5 - s, t), ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩, rfl⟩

private theorem exists_reflected_horizontal_path
    {p q u v : frontier crossingProductCell.domain} (P : Path p q) {t : ℝ}
    (hP : Set.range (fun r => (P r : EuclideanSpace ℝ (Fin 2))) = placedHorizontal t)
    (hu : stripReflection p = u) (hv : stripReflection q = v) :
    ∃ Q : Path u v,
      (∀ r, (Q r : EuclideanSpace ℝ (Fin 2)) = stripReflection (P r)) ∧
        Set.range Q ⊆ Set.range P := by
  have hmem (r : unitInterval) : stripReflection (P r) ∈
      Set.range (fun s => (P s : EuclideanSpace ℝ (Fin 2))) := by
    rw [hP]
    apply stripReflection_mapsTo_horizontal t
    rw [← hP]
    exact ⟨r, rfl⟩
  have hfront (r : unitInterval) : stripReflection (P r) ∈ frontier crossingProductCell.domain := by
    obtain ⟨s, hs⟩ := hmem r
    exact hs ▸ (P s).property
  let Q : Path u v := {
    toFun r := ⟨stripReflection (P r), hfront r⟩
    continuous_toFun :=
      (stripReflection.continuous_of_finiteDimensional.comp
        (continuous_subtype_val.comp P.continuous)).subtype_mk _
    source' := Subtype.ext (by simpa only [Path.source] using hu)
    target' := Subtype.ext (by simpa only [Path.target] using hv) }
  refine ⟨Q, fun _ => rfl, ?_⟩
  rintro z ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := hmem r
  exact ⟨s, Subtype.ext hs⟩

theorem crossingProductCell_exists_preserving_boundaryWordWitnesses
    {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : NormalSingularCellData crossingProductCell (frontier crossingProductSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c = spliceEmbedding '' spliceCore)
    {X : Type*} [TopologicalSpace X] {ρ : X → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsEmbedding ρ) (f : frontier crossingProductCell.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier crossingProductCell.domain, ρ (f z) = crossingProductCell z) :
    ∃ (p q u v : frontier crossingProductCell.domain)
      (σ₀ : Path p q) (τ₀ : Path q u) (υ₀ : Path u v) (φ₀ : Path v p)
      (e : loopCircle ≃ₜ frontier crossingProductCell.domain)
      (a b : X) (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a)
      (Gd : SingularTwoCell (EuclideanSpace ℝ (Fin 3))),
      (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 0) ∧
      (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (3 / 2, 1) ∧
      (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 1) ∧
      (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (7 / 2, 0) ∧
      (∀ θ, e θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      Function.Injective σ₀ ∧ Function.Injective τ₀ ∧
      Function.Injective υ₀ ∧ Function.Injective φ₀ ∧
      (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
      (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
      hD.IsBoundarySurgeryCell c Gd ∧
      Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ))) ∧
      Nonempty (BoundaryWordWitness crossRegluedProductCell ρ
        (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))) := by
  obtain ⟨D₁, D₂, D₃, hcut, hD₁, -, hD₃⟩ :=
    crossingProductCell_exists_preserving_cut hD hc
  obtain ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, hp, hq, hu, hv,
    hrσ, hrτ, hrυ, hrφ, he, hσinj, hτinj, hυinj, hφinj⟩ := exists_product_boundary_paths
  have huX : f u = f q := by
    apply hρ.injective
    rw [hfρ, hfρ, hu, hq, crossingProductCell_on_wall (Or.inr rfl),
      crossingProductCell_on_wall (Or.inl rfl)]
  have hvX : f v = f p := by
    apply hρ.injective
    rw [hfρ, hfρ, hv, hp, crossingProductCell_on_wall (Or.inr rfl),
      crossingProductCell_on_wall (Or.inl rfl)]
  let σ := σ₀.map hf
  let τ : Path (f q) (f q) := (τ₀.map hf).cast rfl huX.symm
  let υ : Path (f q) (f p) := (υ₀.map hf).cast huX.symm hvX.symm
  let φ : Path (f p) (f p) := (φ₀.map hf).cast hvX.symm rfl
  obtain ⟨τ₁, hτ₁, hrτ₁⟩ := exists_reflected_horizontal_path τ₀ hrτ
    (u := u) (v := q)
    (by rw [hq, hu, stripReflection_apply]; norm_num)
    (by rw [hu, hq, stripReflection_apply]; norm_num)
  obtain ⟨φ₁, hφ₁, hrφ₁⟩ := exists_reflected_horizontal_path φ₀ hrφ
    (u := p) (v := v)
    (by rw [hv, hp, stripReflection_apply]; norm_num)
    (by rw [hp, hv, stripReflection_apply]; norm_num)
  let τX : Path (f q) (f q) := (τ₁.map hf).cast huX.symm rfl
  let φX : Path (f p) (f p) := (φ₁.map hf).cast rfl hvX.symm
  have hτhom : τX.Homotopic τ.symm :=
    BoundaryWordWitness.push_source_homotopy_reverse f hf hτinj hrτ₁
      (fun _ => rfl) (fun _ => rfl)
  have hφhom : φX.Homotopic φ.symm :=
    BoundaryWordWitness.push_source_homotopy_reverse f hf hφinj hrφ₁
      (fun _ => rfl) (fun _ => rfl)
  have hσeq (t : unitInterval) : (σ.map hρ.continuous) t = crossRegluedProductCell (σ₀ t) := by
    change ρ (f (σ₀ t)) = _
    rw [hfρ]
    apply (crossRegluedProductCell_eq_left _).symm
    have hmem : (σ₀ t : EuclideanSpace ℝ (Fin 2)) ∈
        placedStrip 0 (3 / 2) ∩ frontier crossingProductCell.domain := hrσ ▸ ⟨t, rfl⟩
    exact hmem.1
  have hυeq (t : unitInterval) : (υ.map hρ.continuous) t = crossRegluedProductCell (υ₀ t) := by
    change ρ (f (υ₀ t)) = _
    rw [hfρ]
    apply (crossRegluedProductCell_eq_right _).symm
    have hmem : (υ₀ t : EuclideanSpace ℝ (Fin 2)) ∈
        placedStrip (7 / 2) 5 ∩ frontier crossingProductCell.domain := hrυ ▸ ⟨t, rfl⟩
    exact hmem.1
  have hτeq (t : unitInterval) : (τX.map hρ.continuous) t = crossRegluedProductCell (τ₀ t) := by
    change ρ (f (τ₁ t)) = _
    rw [hfρ, hτ₁]
    apply (crossRegluedProductCell_eq_middle _).symm
    have hmem := mem_placedHorizontal.mp (hrτ ▸ Set.mem_range_self t)
    exact mem_placedStrip.mpr ⟨hmem.1, by rw [hmem.2]; norm_num⟩
  have hφeq (t : unitInterval) : (φX.map hρ.continuous) t = crossRegluedProductCell (φ₀ t) := by
    change ρ (f (φ₁ t)) = _
    rw [hfρ, hφ₁]
    apply (crossRegluedProductCell_eq_middle _).symm
    have hmem := mem_placedHorizontal.mp (hrφ ▸ Set.mem_range_self t)
    exact mem_placedStrip.mpr ⟨hmem.1, by rw [hmem.2]; norm_num⟩
  have hwhole : ∀ t,
      ((σ.trans (τX.trans (υ.trans φX))).map hρ.continuous) t =
        crossRegluedProductCell ((σ₀.trans (τ₀.trans (υ₀.trans φ₀))) t) := by
    have htail := trans_apply_eq_map
      (f := fun z : frontier crossingProductCell.domain => crossRegluedProductCell z)
      (α := υ₀) (β := φ₀) hυeq hφeq
    have hmiddle := trans_apply_eq_map
      (f := fun z : frontier crossingProductCell.domain => crossRegluedProductCell z)
      (α := τ₀) hτeq htail
    simpa only [Path.map_trans] using
      trans_apply_eq_map
        (f := fun z : frontier crossingProductCell.domain => crossRegluedProductCell z)
        (α := σ₀) hσeq hmiddle
  let W : BoundaryWordWitness crossRegluedProductCell ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) := {
    param := e
    loop := pathToCircle (σ.trans (τX.trans (υ.trans φX)))
    realizes := fun θ => by
      change ρ (pathToCircle (σ.trans (τX.trans (υ.trans φX))) θ) =
        crossRegluedProductCell (e θ : EuclideanSpace ℝ (Fin 2))
      rw [he θ]
      obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
      simp only [pathToCircle_coe]
      exact hwhole t
    homotopic := pathToCircle_homotopic
      ((Path.Homotopic.refl σ).hcomp (hτhom.hcomp ((Path.Homotopic.refl υ).hcomp hφhom))) }
  obtain ⟨Gd, hGd, Wd⟩ := hD.exists_boundaryWordWitness_direct_of_cut hcut f hf hfρ
    σ₀ υ₀ hp hq
    (by rw [hu]; change _ = stripShift _; rw [stripShift_apply]; norm_num)
    (by rw [hv]; change _ = stripShift _; rw [stripShift_apply]; norm_num)
    hσinj hυinj (by rw [hD₁]; exact hrσ) (by rw [hD₃]; exact hrυ)
    (σ := σ) (υ := υ) (fun _ => rfl) (fun _ => rfl)
  exact ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, f p, f q, σ, τ, υ, φ, Gd,
    hp, hq, hu, hv, he, hσinj, hτinj, hυinj, hφinj,
    (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), hGd, Wd, ⟨W⟩⟩

theorem SingularTwoCell.exists_three_cells_of_rectangular_domain
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hdom : D.domain = seamWitnessPlane '' (Icc a d ×ˢ Icc (0 : ℝ) 1)) :
    let S := fun l u : ℝ => seamWitnessPlane '' (Icc l u ×ˢ Icc (0 : ℝ) 1)
    let A := seamWitnessPlane '' ({b} ×ˢ Icc (0 : ℝ) 1)
    let C := seamWitnessPlane '' ({c} ×ˢ Icc (0 : ℝ) 1)
    ∃ D₁ D₂ D₃ : SingularTwoCell M,
      D₁.domain = S a b ∧ D₂.domain = S b c ∧ D₃.domain = S c d ∧
      IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain ∧
      D₁.domain ∩ D₂.domain = A ∧ D₂.domain ∩ D₃.domain = C ∧
      A ⊆ frontier D₁.domain ∧ A ⊆ frontier D₂.domain ∧
      C ⊆ frontier D₂.domain ∧ C ⊆ frontier D₃.domain ∧
      Disjoint D₁.domain D₃.domain ∧
      D₁.toFun = D.toFun ∧ D₂.toFun = D.toFun ∧ D₃.toFun = D.toFun ∧
      IsPLBall 1 (D₁.domain ∩ frontier D.domain) ∧
      IsPLBall 1 (D₃.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₁.domain)
        (seamWitnessPlane (b, 0)) (seamWitnessPlane (b, 1)) A
        (D₁.domain ∩ frontier D.domain) ∧
      Schoenflies.IsCutPair (frontier D₃.domain)
        (seamWitnessPlane (c, 0)) (seamWitnessPlane (c, 1)) C
        (D₃.domain ∩ frontier D.domain) := by
  let D₁ := D.restrict (isPLBall_placedStrip hab) (by
    rw [hdom]
    exact placedStrip_subset le_rfl (hbc.trans hcd).le)
  let D₂ := D.restrict (isPLBall_placedStrip hbc) (by
    rw [hdom]
    exact placedStrip_subset hab.le hcd.le)
  let D₃ := D.restrict (isPLBall_placedStrip hcd) (by
    rw [hdom]
    exact placedStrip_subset (hab.trans hbc).le le_rfl)
  have htrace₁ := exists_placedStrip_trace_cut hab (hbc.trans hcd)
  have htrace₃ := exists_placedStrip_trace_cut (hab.trans hbc) hcd
  have hdom' : D.domain = placedStrip a d := hdom
  rw [← hdom'] at htrace₁ htrace₃
  refine ⟨D₁, D₂, D₃, rfl, rfl, rfl,
    isPLBall_placedWall _, isPLBall_placedWall _, ?_, ?_,
    placedStrip_inter hab.le hbc.le, placedStrip_inter hbc.le hcd.le,
    placedWall_subset_frontier_right hab.le, placedWall_subset_frontier_left hbc.le,
    placedWall_subset_frontier_right hbc.le, placedWall_subset_frontier_left hcd.le,
    placedStrip_disjoint hbc, rfl, rfl, rfl,
    htrace₁.1, htrace₃.2.2.1, htrace₁.2.1, htrace₃.2.2.2⟩
  · apply disjoint_left.mpr
    intro z hz hw
    have hz' := mem_placedWall.mp hz
    have hw' := mem_placedWall.mp hw
    exact (ne_of_lt hbc) (hz'.1.symm.trans hw'.1)
  · change placedStrip a b ∪ placedStrip b c ∪ placedStrip c d = D.domain
    rw [placedStrip_union hab.le hbc.le, placedStrip_union (hab.trans hbc).le hcd.le]
    exact hdom.symm

theorem isPLBall_seamWitnessPlane_image_Icc_prod {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)) :=
  isPLBall_placedStrip hab

theorem seamWitnessPlane_image_Icc_prod_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1) ∪
      seamWitnessPlane '' (Icc b c ×ˢ Icc (0 : ℝ) 1) =
        seamWitnessPlane '' (Icc a c ×ˢ Icc (0 : ℝ) 1) :=
  placedStrip_union hab hbc

theorem seamWitnessPlane_image_Icc_prod_inter {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1) ∩
      seamWitnessPlane '' (Icc b c ×ˢ Icc (0 : ℝ) 1) =
        seamWitnessPlane '' ({b} ×ˢ Icc (0 : ℝ) 1) :=
  placedStrip_inter hab hbc

theorem seamWitnessPlane_image_Icc_prod_disjoint {a b c d : ℝ} (hbc : b < c) :
    Disjoint (seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1))
      (seamWitnessPlane '' (Icc c d ×ˢ Icc (0 : ℝ) 1)) :=
  placedStrip_disjoint hbc

theorem mem_frontier_seamWitnessPlane_image_Icc_prod {a b : ℝ} (hab : a ≤ b)
    {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ frontier (seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)) ↔
      ((seamWitnessPlane.symm z).1 ∈ Icc a b ∧
        ((seamWitnessPlane.symm z).2 = 0 ∨ (seamWitnessPlane.symm z).2 = 1)) ∨
      (((seamWitnessPlane.symm z).1 = a ∨ (seamWitnessPlane.symm z).1 = b) ∧
        (seamWitnessPlane.symm z).2 ∈ Icc (0 : ℝ) 1) :=
  mem_frontier_placedStrip hab

theorem isCutPair_seamWitnessPlane_rectangle_traces {a s b : ℝ} (has : a < s) (hsb : s < b) :
    let P := seamWitnessPlane '' (Icc a s ×ˢ Icc (0 : ℝ) 1)
    let Q := seamWitnessPlane '' (Icc s b ×ˢ Icc (0 : ℝ) 1)
    let S := seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)
    let A := seamWitnessPlane '' ({s} ×ˢ Icc (0 : ℝ) 1)
    IsPLBall 1 (P ∩ frontier S) ∧
      Schoenflies.IsCutPair (frontier P) (seamWitnessPlane (s, 0))
        (seamWitnessPlane (s, 1)) A (P ∩ frontier S) ∧
      IsPLBall 1 (Q ∩ frontier S) ∧
      Schoenflies.IsCutPair (frontier Q) (seamWitnessPlane (s, 0))
        (seamWitnessPlane (s, 1)) A (Q ∩ frontier S) :=
  exists_placedStrip_trace_cut has hsb

end DifferentialGeometry.Topology.PiecewiseLinear
