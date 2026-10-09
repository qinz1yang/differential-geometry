import DifferentialGeometry.Topology.ThreeManifold.UncappingLocalMap
import DifferentialGeometry.Topology.ThreeManifold.UncappingSeam

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem capAnnulusMap_mem_uncappingInterior (b : T.Boundary) (q : Annulus)
    (hq : 1 / 4 < q.2.val) : C.capAnnulusMap b q ∈ C.uncappingInterior := by
  let x : ClosedCell 3 := ⟨q.2.val • q.1.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
      norm_eq_of_mem_sphere, mul_one]
    exact q.2.property.2⟩
  have hx : 1 / 4 < ‖x.val‖ := by
    change 1 / 4 < ‖q.2.val • q.1.val‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
      norm_eq_of_mem_sphere, mul_one]
    exact hq
  exact C.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall b
    (Homeomorph.refl (ClosedCell 3)) (fun _ _ => rfl) x hx

theorem uncappingQuotient_covered_by_interior_and_seam (q : C.UncappingQuotient) :
    (∃ y : C.uncappingInterior,
      C.uncappingProjection (C.uncappingInteriorInclusion y) = q) ∨
    ∃ (a : T.Index) (z : Sphere), C.uncappingSeam a
      (z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩) = q := by
  induction q using Quot.inductionOn with
  | h q =>
    induction q using Quot.inductionOn with
    | h q =>
      cases q with
      | inr x =>
        obtain ⟨x, hx⟩ := x.property
        left
        refine ⟨⟨C.coreInclusion x, C.coreInclusion_mem_uncappingInterior x⟩, ?_⟩
        rw [C.uncappingProjection_of_eq_coreInclusion x _ rfl]
        apply congrArg (Quot.mk C.innerCapRelation)
        apply congrArg (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
          C.capAnnuliAttachingMap)
        exact Subtype.ext hx
      | inl q =>
        obtain ⟨⟨a, side⟩, z, r⟩ := q
        by_cases hr : r.val = 1 / 4
        · right
          refine ⟨a, -z, ?_⟩
          have hr' : r = (⟨1 / 4, by norm_num⟩ : Icc (1 / 4 : ℝ) 1) := Subtype.ext hr
          subst r
          cases side
          · simpa only [neg_neg, add_zero, adjunctionCell, adjunctionMk] using C.uncappingSeam_of_nonneg a
              (-z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩)
              (by norm_num)
          · simpa only [neg_neg, sub_zero, adjunctionCell, adjunctionMk] using C.uncappingSeam_of_nonpos a
              (-z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩)
              (by norm_num)
        · left
          have hlt : 1 / 4 < r.val := lt_of_le_of_ne r.property.1 (Ne.symm hr)
          let y : C.uncappingInterior :=
            ⟨C.capAnnulusMap (a, side) (z, r), C.capAnnulusMap_mem_uncappingInterior (a, side) (z, r) hlt⟩
          exact ⟨y, C.uncappingProjection_annulus (a, side) (z, r) (C.uncappingInteriorInclusion y) rfl⟩

end DifferentialGeometry.Topology.SphericalCapping
