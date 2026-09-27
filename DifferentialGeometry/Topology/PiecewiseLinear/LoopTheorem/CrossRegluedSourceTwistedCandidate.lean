/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedReglued

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def rect (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc a b ×ˢ Icc (0 : ℝ) 1)

private def wall (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' ({a} ×ˢ Icc (0 : ℝ) 1)

private theorem reflection_invFunOn {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ rect 0 1) :
    Function.invFunOn (⇑twistedStripReflection) (rect 0 1) z = twistedStripReflection z := by
  apply twistedStripReflection_involutive.injective
  unfold rect
  rw [isPLHomeomorphOn_twistedStripReflection_middle.bijOn.invOn_invFunOn.2 hz,
    twistedStripReflection_involutive]

private theorem reflection_mapsTo_trace :
    MapsTo (⇑twistedStripReflection) (rect 0 1 ∩ frontier (rect (-1 / 4) (5 / 4)))
      (rect 0 1 ∩ frontier (rect (-1 / 4) (5 / 4))) := by
  rintro z ⟨hz, hf⟩
  refine ⟨twistedStripReflection_mapsTo_middle hz, ?_⟩
  obtain ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩ := hz
  have h := (mem_frontier_seamWitnessPlane_image_Icc_prod
    (by norm_num : (-1 / 4 : ℝ) ≤ 5 / 4)).mp hf
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [twistedStripReflection_apply]
  apply (mem_frontier_seamWitnessPlane_image_Icc_prod
    (by norm_num : (-1 / 4 : ℝ) ≤ 5 / 4)).mpr
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  refine Or.inl ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  rcases h with h | ⟨h, -⟩
  · rcases h.2 with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rcases h with h | h <;> linarith [hs.1, hs.2]

private theorem image_middle_trace :
    crossRegluedTwistedCell '' (rect 0 1 ∩ frontier (rect (-1 / 4) (5 / 4))) =
      twistedStripCell '' (rect 0 1 ∩ frontier (rect (-1 / 4) (5 / 4))) := by
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨twistedStripReflection z, reflection_mapsTo_trace hz,
      (crossRegluedTwistedCell_eq_middle hz.1).symm⟩
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨twistedStripReflection z, reflection_mapsTo_trace hz, ?_⟩
    rw [crossRegluedTwistedCell_eq_middle (twistedStripReflection_mapsTo_middle hz.1)]
    exact congrArg twistedStripCell (twistedStripReflection_involutive z)

private theorem image_left_trace :
    crossRegluedTwistedCell '' (rect (-1 / 4) 1 ∩ frontier (rect (-1 / 4) (5 / 4))) =
      twistedStripCell '' (rect (-1 / 4) 1 ∩ frontier (rect (-1 / 4) (5 / 4))) := by
  have hunion : rect (-1 / 4) 0 ∪ rect 0 1 = rect (-1 / 4) 1 :=
    seamWitnessPlane_image_Icc_prod_union (by norm_num) (by norm_num)
  have hleft : EqOn (⇑crossRegluedTwistedCell) (⇑twistedStripCell)
      (rect (-1 / 4) 0) := crossRegluedTwistedCell_eq_left
  rw [← hunion, union_inter_distrib_right, image_union, image_union,
    image_congr (hleft.mono inter_subset_left), image_middle_trace]

private theorem reverseCut {C A B : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)} (h : Schoenflies.IsCutPair C p q A B) :
    Schoenflies.IsCutPair C q p A B :=
  ⟨h.fst.reverse, h.snd.reverse, h.union_eq, h.inter_eq.trans (pair_comm p q)⟩

theorem crossRegluedTwistedCell_isCrossRegluedCell {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain) :
    hD.IsCrossRegluedCell c crossRegluedTwistedCell := by
  classical
  obtain ⟨D₁, D₂, D₃, hcut, -⟩ := twistedStripCell_exists_reversing_cut hD hc
  obtain ⟨hA, hC, hAC, hpre, -, -, hg, hcompat, -⟩ := hcut
  let P := rect (-1 / 4) 0
  let Q := rect 0 1
  let P' := rect (-1 / 4) 1
  let Q' := rect 1 (5 / 4)
  let R := P' ∩ frontier (rect (-1 / 4) (5 / 4))
  let T := Q' ∩ frontier (rect (-1 / 4) (5 / 4))
  have hP : IsPLBall 2 P := isPLBall_seamWitnessPlane_image_Icc_prod (by norm_num)
  have hQ : IsPLBall 2 Q := isPLBall_seamWitnessPlane_image_Icc_prod (by norm_num)
  have hP' : IsPLBall 2 P' := isPLBall_seamWitnessPlane_image_Icc_prod (by norm_num)
  have hQ' : IsPLBall 2 Q' := isPLBall_seamWitnessPlane_image_Icc_prod (by norm_num)
  have hPQ : P ∪ Q = P' := seamWitnessPlane_image_Icc_prod_union (by norm_num) (by norm_num)
  have hPQ' : P' ∪ Q' = rect (-1 / 4) (5 / 4) :=
    seamWitnessPlane_image_Icc_prod_union (by norm_num) (by norm_num)
  have hI : P ∩ Q = wall 0 := seamWitnessPlane_image_Icc_prod_inter (by norm_num) (by norm_num)
  have hI' : P' ∩ Q' = wall 1 :=
    seamWitnessPlane_image_Icc_prod_inter (by norm_num) (by norm_num)
  have hAin : wall 0 ⊆ Q := by rw [← hI]; exact inter_subset_right
  have hsub : P' ⊆ crossRegluedTwistedCell.domain := by
    rintro z ⟨p, ⟨hs, ht⟩, rfl⟩
    exact ⟨p, ⟨⟨hs.1, by linarith [hs.2]⟩, ht⟩, rfl⟩
  let H := crossRegluedTwistedCell.restrict hP' hsub
  have htrace := isCutPair_seamWitnessPlane_rectangle_traces
    (by norm_num : (-1 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 5 / 4)
  have hRcut : Schoenflies.IsCutPair (frontier P')
      (seamWitnessPlane (1, 1)) (seamWitnessPlane (1, 0)) (P' ∩ Q') R :=
    hI'.symm ▸ reverseCut htrace.2.1
  have hTcut : Schoenflies.IsCutPair (frontier Q')
      (seamWitnessPlane (1, 1)) (seamWitnessPlane (1, 0)) (P' ∩ Q') T :=
    hI'.symm ▸ reverseCut htrace.2.2.2
  have hfront : frontier crossRegluedTwistedCell.domain = R ∪ T := by
    change frontier (rect (-1 / 4) (5 / 4)) =
      P' ∩ frontier (rect (-1 / 4) (5 / 4)) ∪ Q' ∩ frontier (rect (-1 / 4) (5 / 4))
    rw [← union_inter_distrib_right, hPQ']
    exact (inter_eq_right.mpr
      twistedStripCell.isPLBall_domain.isPolyhedron.isClosed.frontier_subset).symm
  have hRT : R ∩ T = {seamWitnessPlane (1, 1), seamWitnessPlane (1, 0)} := by
    apply Subset.antisymm
    · intro z hz
      exact hRcut.inter_eq.subset ⟨⟨hz.1.1, hz.2.1⟩, hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hRcut.snd.left_mem, hTcut.snd.left_mem⟩
      · exact ⟨hRcut.snd.right_mem, hTcut.snd.right_mem⟩
  have hGR : crossRegluedTwistedCell '' R = twistedStripCell '' R := image_left_trace
  have hGT : crossRegluedTwistedCell '' T = twistedStripCell '' T :=
    image_congr (crossRegluedTwistedCell_eq_right.mono inter_subset_left)
  have hGfront : crossRegluedTwistedCell '' frontier crossRegluedTwistedCell.domain =
      twistedStripCell '' frontier twistedStripCell.domain := by
    change crossRegluedTwistedCell '' frontier crossRegluedTwistedCell.domain =
      twistedStripCell '' frontier crossRegluedTwistedCell.domain
    rw [hfront, image_union, image_union, hGR, hGT]
  have hreflect : EqOn (⇑twistedStripReflection ∘ ⇑twistedStripReflection) id (wall 1) :=
    fun z _ => twistedStripReflection_involutive z
  have hkinv : Function.invFunOn (⇑twistedStripReflection) Q '' wall 0 = wall 1 := by
    rw [image_congr (fun z hz => reflection_invFunOn (hAin hz)),
      wall, twistedStripReflection_image_wall]
    norm_num [wall]
  obtain ⟨a', b', ρ, κ, e, hρrange, hκrange, he, hρinj, hκinj⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union hRcut.snd hTcut.snd hRT hfront
  let σ := ρ.map crossRegluedTwistedCell.boundary.continuous
  let ω := κ.map crossRegluedTwistedCell.boundary.continuous
  have hσrange : Set.range σ = crossRegluedTwistedCell '' R := by
    change Set.range (⇑crossRegluedTwistedCell ∘ fun t =>
      (ρ t : EuclideanSpace ℝ (Fin 2))) = _
    rw [Set.range_comp, hρrange]
  have hωrange : Set.range ω = crossRegluedTwistedCell '' T := by
    change Set.range (⇑crossRegluedTwistedCell ∘ fun t =>
      (κ t : EuclideanSpace ℝ (Fin 2))) = _
    rw [Set.range_comp, hκrange]
  have heG : ∀ θ, crossRegluedTwistedCell (e θ) = pathToCircle (σ.trans ω) θ := by
    intro θ
    rw [he θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map crossRegluedTwistedCell.boundary.continuous) t = (σ.trans ω) t
    rw [Path.map_trans]
  have hp : seamWitnessPlane (0, 0) ∈ wall 0 := ⟨(0, 0), ⟨rfl, by norm_num⟩, rfl⟩
  have hq : seamWitnessPlane (0, 1) ∈ wall 0 := ⟨(0, 1), ⟨rfl, by norm_num⟩, rfl⟩
  have hr : seamWitnessPlane (1, 0) ∈ wall 1 := ⟨(1, 0), ⟨rfl, by norm_num⟩, rfl⟩
  have hs : seamWitnessPlane (1, 1) ∈ wall 1 := ⟨(1, 1), ⟨rfl, by norm_num⟩, rfl⟩
  refine ⟨wall 0, wall 1, P, Q, Q', P, Q, P', Q', wall 1, R, T,
    seamWitnessPlane (0, 0), seamWitnessPlane (0, 1), seamWitnessPlane (1, 0),
    seamWitnessPlane (1, 1), seamWitnessPlane (1, 1), seamWitnessPlane (1, 0),
    ⇑twistedStripReflection, id, ⇑twistedStripReflection, id, id, H,
    hA, hC, hAC, hpre, hg, hcompat, hp, hq, hr, hs, ?_, hPQ ▸ hPQ', hI,
    seamWitnessPlane_image_Icc_prod_inter (by norm_num) (by norm_num),
    seamWitnessPlane_image_Icc_prod_disjoint (by norm_num), hP, hQ, hPQ.symm,
    hP.isPolyhedron.isPLHomeomorphOn_id, isPLHomeomorphOn_twistedStripReflection_middle,
    ?_, ?_, crossRegluedTwistedCell_eq_left, crossRegluedTwistedCell_eq_middle, hkinv.symm,
    hC, ?_, ?_, hC.isPolyhedron.isPLHomeomorphOn_id.congr hreflect,
    hP', hQ', hPQ'.symm, hP'.isPolyhedron.isPLHomeomorphOn_id,
    hQ'.isPolyhedron.isPLHomeomorphOn_id, ?_, ?_, fun _ _ => rfl,
    crossRegluedTwistedCell_eq_right, hRcut, hTcut, htrace.1, htrace.2.2.1, hfront,
    ?_, ?_, ?_, ?_, crossRegluedTwistedCell_image.subset, ?_,
    crossRegluedTwistedCell a', crossRegluedTwistedCell b', σ, ω, e,
    hσrange, hωrange, heG, ?_, hGT, hGfront, a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, he⟩
  · exact Or.inr twistedStripReflection_reversing_endpoints
  · simpa only [image_id] using hI
  · rw [hI, wall, twistedStripReflection_image_wall]
    norm_num [wall]
  · rw [hI]
    exact hAC.symm
  · rintro z ⟨⟨s, t⟩, ⟨hs', ht⟩, rfl⟩
    change s = 1 at hs'
    subst s
    apply (mem_frontier_seamWitnessPlane_image_Icc_prod
      (by norm_num : (-1 / 4 : ℝ) ≤ 1)).mpr
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact Or.inr ⟨Or.inr trivial, ht⟩
  · simpa only [image_id] using hI'
  · simpa only [image_id] using hI'
  · change _ = Function.invFunOn (⇑twistedStripReflection) Q _
    rw [reflection_invFunOn (hAin hp), twistedStripReflection_apply]
    norm_num
  · change _ = Function.invFunOn (⇑twistedStripReflection) Q _
    rw [reflection_invFunOn (hAin hq), twistedStripReflection_apply]
    norm_num
  · rw [twistedStripReflection_apply]
    norm_num
  · rw [twistedStripReflection_apply]
    norm_num
  · rw [hc, twistedStripCell_doublePointSet]
    rintro y ⟨t, ht, rfl⟩
    exact crossRegluedTwistedCell_core_double ht
  · rw [hPQ]
    exact hGR

end DifferentialGeometry.Topology.PiecewiseLinear
