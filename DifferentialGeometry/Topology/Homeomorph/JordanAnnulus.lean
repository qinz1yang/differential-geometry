/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.CircleIsotopy
import DifferentialGeometry.Topology.Homeomorph.JordanDiskMove
import DifferentialGeometry.Topology.ClosedBall.AnnulusHomeomorph
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion

open Set Metric Schoenflies
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PlanarJordan

namespace Homeomorph

theorem exists_image_nested_jordan_pair {C D C' D' : Set Plane}
    (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hC' : IsJordanCurve C') (hD' : IsJordanCurve D')
    (hnest : closure (inside C) ⊆ inside D)
    (hnest' : closure (inside C') ⊆ inside D') :
    ∃ e : Plane ≃ₜ Plane, e '' C = C' ∧ e '' D = D' := by
  obtain ⟨f, hf, _⟩ := exists_image_closed_region_eqOn_compl hD hD'
    isOpen_univ isPreconnected_univ (subset_univ _) (subset_univ _)
  have hfD : f '' D = D' := by
    rw [← frontier_closure_inside hD, f.image_frontier, hf, frontier_closure_inside hD']
  have hfI : f '' inside D = inside D' := by rw [image_inside, hfD]
  have hfCU : closure (inside (f '' C)) ⊆ inside D' := by
    rw [← image_inside, ← f.image_closure]
    exact (image_mono hnest).trans hfI.subset
  obtain ⟨g, hg, hgfix⟩ := exists_image_closed_region_eqOn_compl
    (isJordanCurve_image f hC) hC' (jordan_curve_theorem hD').isOpen_inside
    (jordan_curve_theorem hD').isConnected_inside.isPreconnected hfCU hnest'
  have hgC : g '' (f '' C) = C' := by
    rw [← frontier_closure_inside (isJordanCurve_image f hC), g.image_frontier, hg,
      frontier_closure_inside hC']
  have hgD : g '' D' = D' := by
    have hsub : D' ⊆ (inside D')ᶜ := fun _ hx hi => hi.1 hx
    exact (hgfix.mono hsub).image_eq.trans (image_id _)
  refine ⟨f.trans g, ?_, ?_⟩
  · exact (image_comp g f C).trans hgC
  · exact (image_comp g f D).trans (hfD ▸ hgD)

theorem exists_homeomorph_jordan_annulus {C D : Set Plane}
    (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hnest : closure (inside C) ⊆ inside D) :
    ∃ P : (unitInterval × loopCircle) ≃ₜ ↥(closure (inside D) \ inside C),
      range (fun θ => (P (0, θ) : Plane)) = C ∧
      range (fun θ => (P (1, θ) : Plane)) = D := by
  have hJ : IsJordanCurve (sphere (0 : Plane) 1) := by
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : sphere (0 : Plane) 1 → Plane))
  let s : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num)
  have hs : s '' sphere (0 : Plane) 1 = sphere 0 2 := by
    change ((2 : ℝ) • ·) '' sphere (0 : Plane) 1 = sphere 0 2
    rw [image_smul, smul_sphere' (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hJ2 : IsJordanCurve (sphere (0 : Plane) 2) := hs ▸ isJordanCurve_image s hJ
  have hreg (r : ℝ) (hr : 0 < r) (h : IsJordanCurve (sphere (0 : Plane) r)) :
      closure (inside (sphere (0 : Plane) r)) = closedBall 0 r := by
    have hfr := frontier_closedBall (0 : Plane) hr.ne'
    have hi : (interior (closedBall (0 : Plane) r)).Nonempty := by
      rw [interior_closedBall (0 : Plane) hr.ne']
      exact nonempty_ball.mpr hr
    simpa only [hfr] using closure_inside_frontier_eq_of_isCompact
      (isCompact_closedBall (0 : Plane) r) (hfr.symm ▸ h) hi
  have hint (r : ℝ) (hr : 0 < r) (h : IsJordanCurve (sphere (0 : Plane) r)) :
      inside (sphere (0 : Plane) r) = ball 0 r := by
    have hfr := frontier_closedBall (0 : Plane) hr.ne'
    have hi : (interior (closedBall (0 : Plane) r)).Nonempty := by
      rw [interior_closedBall (0 : Plane) hr.ne']
      exact nonempty_ball.mpr hr
    have hh := interior_eq_inside_frontier_of_isCompact
      (isCompact_closedBall (0 : Plane) r) (hfr.symm ▸ h) hi
    simpa only [hfr, interior_closedBall (0 : Plane) hr.ne'] using hh.symm
  obtain ⟨f, hfC, hfD⟩ := exists_image_nested_jordan_pair hC hD hJ hJ2 hnest (by
    rw [hreg 1 zero_lt_one hJ, hint 2 (by norm_num) hJ2]
    exact closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  let A := closure (inside D) \ inside C
  let B : Set Plane := {x | ‖x‖ ∈ Icc (1 : ℝ) 2}
  have hfA : f '' A = B := by
    dsimp [A, B]
    rw [image_sdiff f.injective, f.image_closure, image_inside, hfD,
      hreg 2 (by norm_num) hJ2, image_inside, hfC, hint 1 zero_lt_one hJ]
    ext x
    simp only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, mem_ofPred_eq,
      mem_Icc, not_lt]
    exact and_comm
  let c : loopCircle ≃ₜ sphere (0 : Plane) 1 :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
      (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
        change z ∈ sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ sphere 0 1
        rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
          Complex.orthonormalBasisOneI.repr.norm_map])
  let e : (unitInterval × loopCircle) ≃ₜ B :=
    (Homeomorph.prodComm _ _).trans ((c.prodCongr
      (iccHomeoI (1 : ℝ) 2 (by norm_num)).symm).trans
        (sphereProdIccHomeomorphAnnulus 1 2 zero_lt_one))
  have he (t : unitInterval) (θ : loopCircle) :
      (e (t, θ) : Plane) = ((t : ℝ) + 1) • (c θ : Plane) := by
    change ((iccHomeoI (1 : ℝ) 2 (by norm_num)).symm t : ℝ) • (c θ : Plane) = _
    rw [iccHomeoI_symm_apply_coe]
    congr 1
    ring
  have hc : range (fun θ => (c θ : Plane)) = sphere 0 1 := by
    change range (Subtype.val ∘ c) = _
    rw [range_comp, c.surjective.range_eq, image_univ, Subtype.range_coe]
  have he0 : range (fun θ => (e (0, θ) : Plane)) = sphere 0 1 := by
    simpa only [he, Set.Icc.coe_zero, zero_add, one_smul] using hc
  have he1 : range (fun θ => (e (1, θ) : Plane)) = sphere 0 2 := by
    have hi : range (fun θ => (e (1, θ) : Plane)) =
        ((2 : ℝ) • ·) '' range (fun θ => (c θ : Plane)) := by
      rw [← range_comp]
      congr 1
      funext θ
      rw [he]
      change ((1 : ℝ) + 1) • (c θ : Plane) = (2 : ℝ) • (c θ : Plane)
      norm_num
    rw [hi, hc]
    exact hs
  let q : A ≃ₜ B := (f.image A).trans (Homeomorph.setCongr hfA)
  let P := e.trans q.symm
  have hP (t : unitInterval) (θ : loopCircle) :
      (P (t, θ) : Plane) = f.symm (e (t, θ)) := by
    apply f.injective
    rw [f.apply_symm_apply]
    exact congrArg Subtype.val (q.apply_symm_apply (e (t, θ)))
  refine ⟨P, ?_, ?_⟩
  · simp_rw [hP]
    change range (f.symm ∘ (fun θ => (e (0, θ) : Plane))) = C
    rw [range_comp, he0, ← hfC]
    exact f.symm_image_image C
  · simp_rw [hP]
    change range (f.symm ∘ (fun θ => (e (1, θ) : Plane))) = D
    rw [range_comp, he1, ← hfD]
    exact f.symm_image_image D

theorem exists_jordan_annulus_boundary_extension {C D C' D' : Set Plane}
    (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hC' : IsJordanCurve C') (hD' : IsJordanCurve D')
    (hnest : closure (inside C) ⊆ inside D)
    (hnest' : closure (inside C') ⊆ inside D') :
    ∃ P : (unitInterval × loopCircle) ≃ₜ ↥(closure (inside D) \ inside C),
      ∃ Q : (unitInterval × loopCircle) ≃ₜ ↥(closure (inside D') \ inside C'),
        range (fun θ => (P (0, θ) : Plane)) = C ∧
        range (fun θ => (P (1, θ) : Plane)) = D ∧
        range (fun θ => (Q (0, θ) : Plane)) = C' ∧
        range (fun θ => (Q (1, θ) : Plane)) = D' ∧
        ∀ φ ψ : loopCircle ≃ₜ loopCircle,
          (HasIncreasingCircleLift φ ↔ HasIncreasingCircleLift ψ) →
          ∃ e : ↥(closure (inside D) \ inside C) ≃ₜ ↥(closure (inside D') \ inside C'),
            (∀ θ, e (P (0, θ)) = Q (0, φ θ)) ∧
            ∀ θ, e (P (1, θ)) = Q (1, ψ θ) := by
  obtain ⟨P, hP0, hP1⟩ := exists_homeomorph_jordan_annulus hC hD hnest
  obtain ⟨Q, hQ0, hQ1⟩ := exists_homeomorph_jordan_annulus hC' hD' hnest'
  refine ⟨P, Q, hP0, hP1, hQ0, hQ1, fun φ ψ hor => ?_⟩
  obtain ⟨E, _, hE0, hE1⟩ := exists_homeomorph_cylinder_of_same_orientation φ ψ hor
  refine ⟨(P.symm.trans E).trans Q, ?_, ?_⟩
  · intro θ
    change Q (E (P.symm (P (0, θ)))) = Q (0, φ θ)
    rw [P.symm_apply_apply, hE0]
  · intro θ
    change Q (E (P.symm (P (1, θ)))) = Q (1, ψ θ)
    rw [P.symm_apply_apply, hE1]

end Homeomorph
