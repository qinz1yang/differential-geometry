/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem rotate_mem_cylinder {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    ((-p.1.2, p.1.1), p.2) ∈ spliceCylinder := by
  have h := mem_spliceSquare.mp hp.1
  exact ⟨mem_spliceSquare.mpr ⟨⟨by linarith [h.2.2], by linarith [h.2.1]⟩, h.1⟩, hp.2⟩

private theorem unrotate_mem_cylinder {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    ((p.1.2, -p.1.1), p.2) ∈ spliceCylinder := by
  have h := mem_spliceSquare.mp hp.1
  exact ⟨mem_spliceSquare.mpr ⟨h.2, by linarith [h.1.2], by linarith [h.1.1]⟩, hp.2⟩

theorem PLCrossSeamReading.not_nonempty_quarter_turn {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {chart : (ℝ × ℝ) × ℝ → M}
    {G : SingularTwoCell M} (R : PLCrossSeamReading chart G)
    (hchart : InjOn chart spliceCylinder) :
    ¬ Nonempty (PLCrossSeamReading
      (fun p : (ℝ × ℝ) × ℝ => chart ((-p.1.2, p.1.1), p.2)) G) := by
  rintro ⟨Q⟩
  have hconn : IsPreconnected R.sourcePos := by
    rw [← R.isPLHomeomorphOn_pos.symm.image_eq]
    exact isPLBall_bentSheetPos.isConnected.isPreconnected.image _
      R.isPLHomeomorphOn_pos.symm.isPiecewiseAffineOn.continuousOn
  have hcover : R.sourcePos ⊆ Q.sourcePos ∪ Q.sourceNeg := by
    intro x hx
    have hcx := R.isPLHomeomorphOn_pos.bijOn.mapsTo hx
    have hcy : (R.coord x).2 ∈ spliceCylinder :=
      ⟨bentArcPos_subset_spliceSquare hcx.1, hcx.2⟩
    rw [Q.source_eq]
    refine ⟨R.source_subset_domain (Or.inl hx),
      (((R.coord x).2.1.2, -(R.coord x).2.1.1), (R.coord x).2.2),
      unrotate_mem_cylinder hcy, ?_⟩
    simpa [Function.comp_def, crossSeamInclude] using (R.reglued_eq (Or.inl hx)).symm
  obtain ⟨x, hx, hcx⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn
    (show ((1, 0), (0 : ℝ)) ∈ bentSheetPos by
      simp only [bentSheetPos, mem_prod, mem_bentArcPos]; norm_num)
  obtain ⟨y, hy, hcy⟩ := R.isPLHomeomorphOn_pos.bijOn.surjOn
    (show ((0, -1), (0 : ℝ)) ∈ bentSheetPos by
      simp only [bentSheetPos, mem_prod, mem_bentArcPos]; norm_num)
  have hxpos : x ∈ Q.sourcePos := by
    rcases hcover hx with hxq | hxq
    · exact hxq
    · have hq := Q.isPLHomeomorphOn_neg.bijOn.mapsTo hxq
      have hqc : (Q.coord x).2 ∈ spliceCylinder :=
        ⟨bentArcNeg_subset_spliceSquare hq.1, hq.2⟩
      have heq := hchart (show ((1, 0), (0 : ℝ)) ∈ spliceCylinder by
          norm_num [spliceCylinder, spliceSquare]) (rotate_mem_cylinder hqc)
        (by simpa only [Function.comp_apply, crossSeamInclude, hcx] using
          ((R.reglued_eq (Or.inl hx)).symm.trans (Q.reglued_eq (Or.inr hxq))))
      have h1 := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.1) heq
      have h2 := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.2) heq
      rcases mem_bentArcNeg.mp hq.1 with hq | hq <;> dsimp at h1 h2 <;> linarith
  have hyneg : y ∈ Q.sourceNeg := by
    rcases hcover hy with hyq | hyq
    · have hq := Q.isPLHomeomorphOn_pos.bijOn.mapsTo hyq
      have hqc : (Q.coord y).2 ∈ spliceCylinder :=
        ⟨bentArcPos_subset_spliceSquare hq.1, hq.2⟩
      have heq := hchart (show ((0, -1), (0 : ℝ)) ∈ spliceCylinder by
          norm_num [spliceCylinder, spliceSquare]) (rotate_mem_cylinder hqc)
        (by simpa only [Function.comp_apply, crossSeamInclude, hcy] using
          ((R.reglued_eq (Or.inl hy)).symm.trans (Q.reglued_eq (Or.inl hyq))))
      have h1 := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.1) heq
      have h2 := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.2) heq
      rcases mem_bentArcPos.mp hq.1 with hq | hq <;> dsimp at h1 h2 <;> linarith
    · exact hyq
  obtain ⟨z, -, hzpos, hzneg⟩ := isPreconnected_closed_iff.mp hconn
    Q.sourcePos Q.sourceNeg Q.isPolyhedron_sourcePos.isClosed Q.isPolyhedron_sourceNeg.isClosed
    hcover ⟨x, hx, hxpos⟩ ⟨y, hy, hyneg⟩
  exact Set.disjoint_left.mp Q.disjoint_source hzpos hzneg

end DifferentialGeometry.Topology.PiecewiseLinear
