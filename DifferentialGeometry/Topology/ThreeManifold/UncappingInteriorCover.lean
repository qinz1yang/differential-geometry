import DifferentialGeometry.Topology.ThreeManifold.UncappingLocalMap

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private local instance coverCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
private local instance coverCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem cap_mem_chart_closedBall_of_norm_le (b : T.Boundary) (x : ClosedCell 3)
    (hx : ‖x.val‖ ≤ 1 / 4) : C.cap b x ∈ (C.capBallChart b).chart '' closedBall (0 : E3) 1 := by
  let r : ℝ := if b.2 then 4 else -4
  have habs : |r| = 4 := by dsimp [r]; cases b.2 <;> norm_num
  have heq : (if b.2 then (1 / 4 : ℝ) else -(1 / 4)) • (r • x.val) = x.val := by
    dsimp [r]
    cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, smul_smul] <;> norm_num
  have hnorm : ‖r • x.val‖ ≤ 1 := by rw [norm_smul,Real.norm_eq_abs,habs]; linarith
  refine ⟨r • x.val, mem_closedBall_zero_iff.mpr hnorm, ?_⟩
  rw [C.capBallChart_apply b _ (by rw [heq]; linarith)]
  exact congrArg (C.cap b) (Subtype.ext heq)

theorem uncappingInterior_cover
    (B : T.Boundary → ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
    (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z)
    (v : S2) (y : C.uncappingInterior) :
    letI := C.coreCharts
    (∃ x : T.core, (𝓡∂ 3).IsInteriorPoint x ∧ y.val = C.coreInclusion x) ∨
      (∃ b z, y.val = C.cap b (sphereToClosedCell z)) ∨
      ∃ (b : T.Boundary) (q : S2 × ℝ), q.2 ∈ Ioo (1 / 4 : ℝ) 1 ∧
        y.val = C.capAnnulusInteriorChart b (B b) v q := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  have hcover : y.val ∈ range C.coreInclusion ∪ ⋃ b, range (C.cap b) := C.exhaustive ▸ mem_univ _
  rcases hcover with ⟨x,hx⟩ | hcap
  · by_cases hint : (𝓡∂ 3).IsInteriorPoint x
    · exact Or.inl ⟨x,hint,hx.symm⟩
    · have hb : x ∈ (𝓡∂ 3).boundary T.core :=
        ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint x).mpr hint
      rw [C.core_boundary] at hb
      obtain ⟨b,z,hz⟩ := mem_iUnion.mp hb
      refine Or.inr (Or.inl ⟨b,(C.attaching b).symm z, ?_⟩)
      rw [C.boundary_eq,Diffeomorph.apply_symm_apply,hz]
      exact hx.symm
  · obtain ⟨b,x,hx⟩ := mem_iUnion.mp hcap
    let x' := (B b).symm x
    have hx' : C.cap b (B b x') = y.val := by change C.cap b (B b ((B b).symm x)) = _; rw [Diffeomorph.apply_symm_apply]; exact hx
    have hquarter : 1 / 4 < ‖x'.val‖ := by
      by_contra h
      have hn : ‖x'.val‖ ≤ 1 / 4 := le_of_not_gt h
      have hc := C.cap_mem_chart_closedBall_of_norm_le b x' hn
      rw [← hsmall b x' hn,hx'] at hc
      exact y.property (mem_iUnion.mpr ⟨b,hc⟩)
    by_cases hone : ‖x'.val‖ = 1
    · let z : S2 := ⟨x'.val,mem_sphere_zero_iff_norm.mpr hone⟩
      have hz : sphereToClosedCell z = x' := Subtype.ext rfl
      refine Or.inr (Or.inl ⟨b,z,?_⟩)
      rw [← hx',← hz,hboundary]
    · have hlt : ‖x'.val‖ < 1 := lt_of_le_of_ne x'.property hone
      have hxne : x'.val ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖x'.val‖))
      let z := Manifold.sphereDirection v x'.val
      refine Or.inr (Or.inr ⟨b,(z,‖x'.val‖),⟨hquarter,hlt⟩,?_⟩)
      rw [C.capAnnulusInteriorChart_apply b (B b) v _ ⟨by linarith,hlt⟩]
      have heq : ‖x'.val‖ • z.val = x'.val := Manifold.norm_smul_sphereDirection v hxne
      exact hx'.symm.trans (congrArg (fun w : ClosedCell 3 => C.cap b (B b w)) (Subtype.ext heq.symm))

end DifferentialGeometry.Topology.SphericalCapping
