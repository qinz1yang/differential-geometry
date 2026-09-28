import DifferentialGeometry.Topology.ThreeManifold.UncappingProjection
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × Icc (1 / 4 : ℝ) 1
local notation "Collar" => ConnectedSumQuotient.CollarDomain

private def seamRadius (side : Bool) (t : ConnectedSumQuotient.collarInterval) : Icc (1 / 4 : ℝ) 1 :=
  ⟨max 1 (1 + (if side then -t.val else t.val)) / 4, by
    have hlo : (1 : ℝ) ≤ max 1 (1 + (if side then -t.val else t.val)) := le_max_left _ _
    have hhi : max 1 (1 + (if side then -t.val else t.val)) ≤ (4 : ℝ) := by
      apply max_le (by norm_num)
      have ht : -(1 / 2 : ℝ) < t.val ∧ t.val < 1 / 2 := t.property
      cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith
    constructor <;> linarith⟩

private theorem seamRadius_lt_half (side : Bool) (t : ConnectedSumQuotient.collarInterval) :
    (seamRadius side t).val < 1 / 2 := by
  have ht : -(1 / 2 : ℝ) < t.val ∧ t.val < 1 / 2 := t.property
  have h : max 1 (1 + (if side then -t.val else t.val)) < (2 : ℝ) := by
    apply max_lt (by norm_num)
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith
  change max 1 (1 + (if side then -t.val else t.val)) / 4 < 1 / 2
  linarith

private theorem continuous_seamRadius (side : Bool) : Continuous (seamRadius side) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ConnectedSumQuotient.collarInterval =>
    max 1 (1 + (if side then -t.val else t.val)) / 4)
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

private theorem seamRadius_zero (side : Bool) (t : ConnectedSumQuotient.collarInterval)
    (ht : t.val = 0) : seamRadius side t = ⟨1 / 4, by norm_num⟩ := by
  apply Subtype.ext
  simp [seamRadius, ht]

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private def seamSidePoint (a : T.Index) (side : Bool) (p : Collar) :
    ((⋃ b, (C.capBallChart b).chart '' ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
    C.capAnnuliAttachingMap ⟨(a, side), -p.1, seamRadius side p.2⟩)

private theorem continuous_seamSidePoint (a : T.Index) (side : Bool) :
    Continuous (C.seamSidePoint a side) :=
  C.puncturedCappingHomeomorph.continuous.comp
    ((continuous_adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap).comp
      (continuous_sigmaMk.comp
        (continuous_fst.neg.prodMk ((continuous_seamRadius side).comp continuous_snd))))

private theorem seamSidePoint_projection_zero (a : T.Index) (p : Collar) (ht : p.2.val = 0) :
    C.uncappingProjection (C.seamSidePoint a false p) =
      C.uncappingProjection (C.seamSidePoint a true p) := by
  change C.uncappingProjection (C.puncturedCappingHomeomorph _) =
    C.uncappingProjection (C.puncturedCappingHomeomorph _)
  rw [C.uncappingProjection_homeomorph, C.uncappingProjection_homeomorph,
    seamRadius_zero false p.2 ht, seamRadius_zero true p.2 ht]
  exact Quot.sound ⟨a, -p.1, Or.inl ⟨rfl, rfl⟩⟩

def uncappingSeamPoint (a : T.Index) (p : Collar) :
    ((⋃ b, (C.capBallChart b).chart '' ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  if 0 ≤ p.2.val then C.seamSidePoint a false p else C.seamSidePoint a true p

def uncappingSeam (a : T.Index) : C(Collar, C.UncappingQuotient) where
  toFun p := C.uncappingProjection (C.uncappingSeamPoint a p)
  continuous_toFun := by
    change Continuous (fun p : Collar => C.uncappingProjection
      (if 0 ≤ p.2.val then C.seamSidePoint a false p else C.seamSidePoint a true p))
    simp only [apply_ite]
    apply Continuous.if _ (C.uncappingProjection.continuous.comp (C.continuous_seamSidePoint a false))
      (C.uncappingProjection.continuous.comp (C.continuous_seamSidePoint a true))
    intro p hp
    exact C.seamSidePoint_projection_zero a p
      (frontier_half_le_subset_eq_zero
        (fun q : Collar => q.2.val) (continuous_subtype_val.comp continuous_snd) hp)

theorem uncappingSeam_eq_projection (a : T.Index) (p : Collar) :
    C.uncappingSeam a p = C.uncappingProjection (C.uncappingSeamPoint a p) := rfl

theorem uncappingSeam_of_nonneg (a : T.Index) (p : Collar) (ht : 0 ≤ p.2.val) :
    C.uncappingSeam a p = Quot.mk C.innerCapRelation
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a, false), -p.1, ⟨(1 + p.2.val) / 4, by
          have hb : p.2.val < (1 / 2 : ℝ) := p.2.property.2
          constructor <;> linarith⟩⟩) := by
  change C.uncappingProjection (C.uncappingSeamPoint a p) = _
  rw [uncappingSeamPoint, ite_eq_left ht]
  change C.uncappingProjection (C.puncturedCappingHomeomorph _) = _
  rw [C.uncappingProjection_homeomorph]
  have hr : seamRadius false p.2 = (⟨(1 + p.2.val) / 4, by
      have hb : p.2.val < (1 / 2 : ℝ) := p.2.property.2
      constructor <;> linarith⟩ : Icc (1 / 4 : ℝ) 1) := by
    apply Subtype.ext
    simp only [seamRadius, Bool.false_eq_true, ite_false]
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + p.2.val)]
  rw [hr]

theorem uncappingSeam_of_nonpos (a : T.Index) (p : Collar) (ht : p.2.val ≤ 0) :
    C.uncappingSeam a p = Quot.mk C.innerCapRelation
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨(a, true), -p.1, ⟨(1 - p.2.val) / 4, by
          have hb : -(1 / 2 : ℝ) < p.2.val := p.2.property.1
          constructor <;> linarith⟩⟩) := by
  have heq : C.uncappingSeam a p = C.uncappingProjection (C.seamSidePoint a true p) := by
    change C.uncappingProjection (C.uncappingSeamPoint a p) = _
    rw [uncappingSeamPoint]
    split_ifs with h
    · exact C.seamSidePoint_projection_zero a p (le_antisymm ht h)
    · rfl
  rw [heq]
  change C.uncappingProjection (C.puncturedCappingHomeomorph _) = _
  rw [C.uncappingProjection_homeomorph]
  have hr : seamRadius true p.2 = (⟨(1 - p.2.val) / 4, by
      have hb : -(1 / 2 : ℝ) < p.2.val := p.2.property.1
      constructor <;> linarith⟩ : Icc (1 / 4 : ℝ) 1) := by
    apply Subtype.ext
    simp only [seamRadius, ite_true]
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + -p.2.val)]
    ring
  rw [hr]

private theorem capAnnulusMap_eq_capBallChart (a : T.Index) (side : Bool)
    (z : Sphere) (r : Icc (1 / 4 : ℝ) 1) (hr : r.val < 1 / 2) :
    C.capAnnulusMap (a, side) (-z, r) =
      (C.capBallChart (a, side)).chart ((4 * r.val) • (if side then -z.val else z.val)) := by
  have hp : 0 < r.val := by linarith [r.property.1]
  have hs : (if side then (1 / 4 : ℝ) else -(1 / 4)) •
      ((4 * r.val) • (if side then -z.val else z.val)) = r.val • (-z.val) := by
    cases side
    · simp only [Bool.false_eq_true, ite_false, smul_smul]
      rw [show -(1 / 4 : ℝ) * (4 * r.val) = -r.val by ring, neg_smul, smul_neg]
    · simp only [ite_true, smul_smul]
      rw [show (1 / 4 : ℝ) * (4 * r.val) = r.val by ring]
  have hn : ‖r.val • (-z.val)‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, norm_neg, norm_eq_of_mem_sphere, mul_one]
    linarith
  rw [C.capBallChart_apply (a, side) _ (by rw [hs]; exact hn)]
  apply congrArg (C.cap (a, side))
  apply Subtype.ext
  exact hs.symm

theorem uncappingSeamPoint_val_of_nonneg (a : T.Index) (p : Collar) (ht : 0 ≤ p.2.val) :
    (C.uncappingSeamPoint a p).val =
      (C.capBallChart (a, false)).chart ((1 + p.2.val) • p.1.val) := by
  rw [uncappingSeamPoint, ite_eq_left ht]
  change C.capAnnulusMap (a, false) (-p.1, seamRadius false p.2) = _
  rw [C.capAnnulusMap_eq_capBallChart a false p.1 _ (seamRadius_lt_half false p.2)]
  apply congrArg (C.capBallChart (a, false)).chart
  simp only [Bool.false_eq_true, ite_false, seamRadius]
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + p.2.val)]
  congr 1
  ring

theorem uncappingSeamPoint_val_of_neg (a : T.Index) (p : Collar) (ht : p.2.val < 0) :
    (C.uncappingSeamPoint a p).val =
      (C.capBallChart (a, true)).chart ((1 - p.2.val) • (-p.1.val)) := by
  rw [uncappingSeamPoint, ite_eq_right (not_le.mpr ht)]
  change C.capAnnulusMap (a, true) (-p.1, seamRadius true p.2) = _
  rw [C.capAnnulusMap_eq_capBallChart a true p.1 _ (seamRadius_lt_half true p.2)]
  apply congrArg (C.capBallChart (a, true)).chart
  simp only [ite_true, seamRadius]
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + -p.2.val)]
  congr 1
  ring

variable (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
  (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
  (hboundary : ∀ b (z : Sphere), B b (sphereToClosedCell z) = sphereToClosedCell z)

private theorem capAnnulusHomeomorph_eq_self_of_radius_le_half
    (hhalf : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x)
    (b : T.Boundary) (q : Annulus) (hq : q.2.val ≤ 1 / 2) :
    C.capAnnulusHomeomorph b (B b) (hsmall b) q = q := by
  apply C.capAnnulusMap_injective b
  rw [C.capAnnulusHomeomorph_apply]
  rw [hhalf b _ (by
    change ‖q.2.val • q.1.val‖ ≤ 1 / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
      norm_eq_of_mem_sphere, mul_one]
    exact hq)]
  rfl

private theorem reparametrization_seamSidePoint
    (hhalf : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x)
    (a : T.Index) (side : Bool) (p : Collar) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (C.uncappingProjection (C.seamSidePoint a side p)) =
      C.uncappingProjection (C.seamSidePoint a side p) := by
  unfold seamSidePoint
  rw [C.uncappingProjection_homeomorph, C.uncappingQuotientReparametrization_annulus]
  rw [C.capAnnulusHomeomorph_eq_self_of_radius_le_half B hsmall hhalf (a, side)
    (-p.1, seamRadius side p.2) (seamRadius_lt_half side p.2).le]

theorem uncappingQuotientReparametrization_uncappingSeam
    (hhalf : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x)
    (a : T.Index) (p : Collar) :
    C.uncappingQuotientReparametrization B hsmall hboundary (C.uncappingSeam a p) =
      C.uncappingSeam a p := by
  change C.uncappingQuotientReparametrization B hsmall hboundary
    (C.uncappingProjection (C.uncappingSeamPoint a p)) =
      C.uncappingProjection (C.uncappingSeamPoint a p)
  rw [uncappingSeamPoint]
  split_ifs
  · exact C.reparametrization_seamSidePoint B hsmall hboundary hhalf a false p
  · exact C.reparametrization_seamSidePoint B hsmall hboundary hhalf a true p

end DifferentialGeometry.Topology.SphericalCapping
