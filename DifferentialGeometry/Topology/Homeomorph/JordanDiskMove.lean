/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PlanarJordan.GraphApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalJordan

open Set Schoenflies
open DifferentialGeometry.Topology.PlanarJordan
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Graph

namespace Homeomorph

theorem exists_isPLSphere_image_eqOn_compl_of_isJordanCurve {C U : Set Plane}
    (hC : IsJordanCurve C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, IsPLSphere 1 (e '' C) ∧ EqOn e id Uᶜ := by
  obtain ⟨γ, hγ, hγC⟩ := hC
  have hp : γ 0 ∈ C := hγC ▸ mem_image_of_mem γ zero_mem_I
  have hq : γ (1 / 2) ∈ C := hγC ▸ mem_image_of_mem γ (by norm_num)
  have hpq : γ 0 ≠ γ (1 / 2) := by
    intro heq
    have h := hγ.injOn (by norm_num) (by norm_num) heq
    norm_num at h
  obtain ⟨A, B, hcut⟩ := exists_isCutPair ⟨γ, hγ, hγC⟩ hp hq hpq
  obtain ⟨a, hac, hai, ha, ha0, ha1⟩ := hcut.fst
  obtain ⟨b, hbc, hbi, hb, hb0, hb1⟩ := hcut.snd
  let f : Fin 2 → ℝ → Plane := ![a, b]
  let G := Graph.curveGraph f ∅
  let _ : G.Finite := Graph.finite_curveGraph f finite_empty
  have h0 (i : Fin 2) : f i 0 = γ 0 := by
    fin_cases i <;> assumption
  have h1 (i : Fin 2) : f i 1 = γ (1 / 2) := by
    fin_cases i <;> assumption
  have himage (i : Fin 2) : Graph.edgeArc f i = ![A, B] i := by
    fin_cases i <;> assumption
  have hf : Graph.IsDrawing G f := Graph.isDrawing_curveGraph
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
    (fun _ _ hx => hx.2.elim) (by
      intro i j hij x hx
      rw [h0, h1]
      rw [himage, himage] at hx
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hcut.inter_eq.subset hx
      · exact hcut.inter_eq.subset ⟨hx.2, hx.1⟩
      · exact (hij rfl).elim)
  have hpoint : Graph.pointSet G f ⊆ U := by
    rintro x (hx | hx)
    · rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · exact hx.elim
      · change f i 0 ∈ U
        rw [h0]
        exact hCU hp
      · change f i 1 ∈ U
        rw [h1]
        exact hCU hq
    · obtain ⟨i, _, hx⟩ := mem_iUnion₂.mp hx
      rw [himage] at hx
      apply hCU
      fin_cases i
      · exact hcut.fst_subset hx
      · exact hcut.snd_subset hx
  obtain ⟨e, he, _, hefix, _⟩ := hf.exists_homeomorph_polygonal_edges_dist_lt_const
    zero_lt_one hU hpoint
  have heA : IsPolygonal (e '' A) := by
    simpa only [himage, Matrix.cons_val_zero] using he 0 (mem_univ _)
  have heB : IsPolygonal (e '' B) := by
    simpa only [himage, Matrix.cons_val_one, Matrix.cons_val_zero] using he 1 (mem_univ _)
  have hpoly : IsPolygonal (e '' C) := by
    rw [← hcut.union_eq, image_union]
    exact heA.union heB ⟨e (γ 0), mem_image_of_mem e hcut.fst.left_mem,
      mem_image_of_mem e hcut.snd.left_mem⟩
  exact ⟨e, isPLSphere_one_of_isJordanCurve_of_isPolygonal
    (isJordanCurve_image e ⟨γ, hγ, hγC⟩) hpoly, hefix⟩

theorem exists_image_closed_region_eqOn_compl {C D U : Set Plane}
    (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hCU : closure (inside C) ⊆ U) (hDU : closure (inside D) ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, e '' closure (inside C) = closure (inside D) ∧
      EqOn e id Uᶜ := by
  have hfront (J : Set Plane) (hJ : IsJordanCurve J) : J ⊆ closure (inside J) := by
    intro x hx
    exact frontier_subset_closure ((jordan_curve_theorem hJ).frontier_inside.symm ▸ hx)
  obtain ⟨a, ha, hafix⟩ := exists_isPLSphere_image_eqOn_compl_of_isJordanCurve hC hU
    ((hfront C hC).trans hCU)
  obtain ⟨b, hb, hbfix⟩ := exists_isPLSphere_image_eqOn_compl_of_isJordanCurve hD hU
    ((hfront D hD).trans hDU)
  have him (e : Plane ≃ₜ Plane) (J : Set Plane) :
      e '' closure (inside J) = closure (inside (e '' J)) := by
    rw [e.image_closure, image_inside]
  have hpres (e : Plane ≃ₜ Plane) (hfix : EqOn e id Uᶜ) : e '' U = U := by
    have h := e.image_compl Uᶜ
    simpa only [hfix.image_eq, image_id, compl_compl] using h
  obtain ⟨g, _, hgfix, hgab⟩ := exists_isPLHomeomorphOn_map_disk_eqOn_compl
    (isPLBall_closure_inside_of_isPLSphere_one ha)
    (isPLBall_closure_inside_of_isPLSphere_one hb) hU hc
    (by rw [← him]; exact (image_mono hCU).trans (hpres a hafix).subset)
    (by rw [← him]; exact (image_mono hDU).trans (hpres b hbfix).subset)
  refine ⟨(a.trans g).trans b.symm, ?_, ?_⟩
  · change (b.symm ∘ (g ∘ a)) '' closure (inside C) = closure (inside D)
    rw [image_comp, image_comp, him, hgab, ← him]
    exact b.symm_image_image _
  · intro x hx
    change b.symm (g (a x)) = x
    rw [hafix hx, id_eq, hgfix hx, id_eq]
    exact b.symm_apply_eq.mpr (hbfix hx).symm

end Homeomorph
