/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.ClosedExtension
import DifferentialGeometry.Topology.Homeomorph.SubsetImage
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Extension of planar local homeomorphisms across compact Jordan disks. -/

open Set Metric Topology

namespace OpenPartialHomeomorph

open Schoenflies (Plane IsJordanCurve)
open DifferentialGeometry.Topology.PlanarJordan

theorem isJordanCurve_image_of_subset_source (e : OpenPartialHomeomorph Plane Plane)
    {C : Set Plane} (hC : IsJordanCurve C) (hs : C ⊆ e.source) :
    IsJordanCurve (e '' C) := by
  obtain ⟨f, hf, himage⟩ := hC
  have hmap : MapsTo f (Icc 0 1) e.source := by
    intro t ht
    exact hs (himage ▸ mem_image_of_mem f ht)
  refine ⟨e ∘ f, ⟨e.continuousOn.comp hf.continuousOn hmap,
    congrArg e hf.closes, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    exact hf.injOn hx hy (e.injOn (hmap ⟨hx.1, hx.2.le⟩)
      (hmap ⟨hy.1, hy.2.le⟩) hxy)
  · rw [image_comp, himage]

theorem exists_homeomorph_eqOn_of_isJordanCurve_frontier
    (e : OpenPartialHomeomorph Plane Plane) {K : Set Plane} (hK : IsCompact K)
    (hJ : IsJordanCurve (frontier K)) (hne : (interior K).Nonempty)
    (hs : K ⊆ e.source) : ∃ F : Plane ≃ₜ Plane, EqOn F e K := by
  have hfs : frontier K ⊆ e.source := hK.isClosed.frontier_subset.trans hs
  have hJe : IsJordanCurve (frontier (e '' K)) := by
    rw [← e.image_frontier_of_isCompact hK hs]
    exact e.isJordanCurve_image_of_subset_source hJ hfs
  have hec : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hs)
  have hei : (interior (e '' K)).Nonempty := by
    rw [← e.image_interior_of_subset_source hs]
    exact hne.image e
  obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJ
    (e.isJordanCurve_image_of_subset_source hJ hfs)
    (e.homeomorphOfImageSubsetSource hfs rfl)
  have hFfront : EqOn F e (frontier K) := fun x hx => hF ⟨x, hx⟩
  have hfront : frontier (F '' K) = frontier (e '' K) := by
    rw [← F.image_frontier, ← e.image_frontier_of_isCompact hK hs]
    exact image_congr hFfront
  have himage : F '' K = e '' K := by
    have hFJ : IsJordanCurve (frontier (F '' K)) := hfront ▸ hJe
    have hFi : (interior (F '' K)).Nonempty := by
      rw [← F.image_interior]
      exact hne.image F
    rw [← closure_inside_frontier_eq_of_isCompact (hK.image F.continuous) hFJ hFi,
      hfront, closure_inside_frontier_eq_of_isCompact hec hJe hei]
  let E : K ≃ₜ e '' K := e.homeomorphOfImageSubsetSource hs rfl
  let G : K ≃ₜ e '' K := (F.image K).trans (Homeomorph.setCongr himage)
  let q : K ≃ₜ K := E.trans G.symm
  have hfix : ∀ x : K, (x : Plane) ∈ frontier K → q x = x := by
    intro x hx
    apply G.injective
    change G (G.symm (E x)) = G x
    rw [G.apply_symm_apply]
    apply Subtype.ext
    exact (hFfront hx).symm
  refine ⟨(q.extendById hK.isClosed hfix).trans F, ?_⟩
  intro x hx
  change F (q.extendById hK.isClosed hfix x) = e x
  rw [q.extendById_apply_of_mem hK.isClosed hfix hx]
  exact congrArg Subtype.val (G.apply_symm_apply (E ⟨x, hx⟩))

private theorem isJordanCurve_sphere (x : Plane) {r : ℝ} (hr : 0 < r) :
    IsJordanCurve (sphere x r) := by
  have hJ : IsJordanCurve (sphere (0 : Plane) 1) := by
    have h := isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : sphere (0 : Plane) 1 → Plane))
    simpa only [Subtype.range_coe] using h
  let a : Plane ≃ₜ Plane := (Homeomorph.smulOfNeZero r hr.ne').trans
    (IsometryEquiv.vaddConst x).toHomeomorph
  have hi : a '' sphere (0 : Plane) 1 = sphere x r := by
    change (IsometryEquiv.vaddConst x) ∘ (r • ·) '' sphere (0 : Plane) 1 = sphere x r
    rw [image_comp, image_smul, smul_sphere' hr.ne', IsometryEquiv.image_sphere]
    simp [abs_of_pos hr]
  have h := a.toOpenPartialHomeomorph.isJordanCurve_image_of_subset_source hJ (subset_univ _)
  exact hi ▸ h

theorem exists_homeomorph_eqOn_closedBall (e : OpenPartialHomeomorph Plane Plane)
    (x : Plane) {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    ∃ F : Plane ≃ₜ Plane, EqOn F e (closedBall x r) := by
  apply e.exists_homeomorph_eqOn_of_isJordanCurve_frontier (isCompact_closedBall x r)
    (by rw [frontier_closedBall x hr.ne']; exact isJordanCurve_sphere x hr) ?_ hs
  rw [interior_closedBall x hr.ne']
  exact nonempty_ball.mpr hr

theorem exists_homeomorph_eventuallyEq (e : OpenPartialHomeomorph Plane Plane)
    {x : Plane} (hx : x ∈ e.source) :
    ∃ F : Plane ≃ₜ Plane, (F : Plane → Plane) =ᶠ[𝓝 x] e ∧
      (F.symm : Plane → Plane) =ᶠ[𝓝 (e x)] e.symm := by
  obtain ⟨r, hr, hs⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds hx)
  obtain ⟨F, hF⟩ := e.exists_homeomorph_eqOn_closedBall x hr hs
  have hf : (F : Plane → Plane) =ᶠ[𝓝 x] e := by
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact hF (ball_subset_closedBall hy)
  refine ⟨F, hf, ?_⟩
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [ContinuousAt, e.left_inv hx] using e.symm.continuousAt (e.map_source hx)
  filter_upwards [hf.comp_tendsto ht, e.open_target.mem_nhds (e.map_source hx)] with y hy hyt
  apply F.injective
  dsimp only [Function.comp_def] at hy
  rw [F.apply_symm_apply, hy, e.right_inv hyt]

end OpenPartialHomeomorph
