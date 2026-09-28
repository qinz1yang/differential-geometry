import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.Manifold.SphereDirection

noncomputable section

open Set Metric Manifold Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "A" => S2 × Icc (1 / 4 : ℝ) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
local instance : Fact ((1 / 4 : ℝ) < 1) := ⟨by norm_num⟩
local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

private def capAnnulusPoint (q : A) : ClosedCell 3 :=
  ⟨q.2.val • q.1.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
      mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
    exact q.2.property.2⟩

private theorem capAnnulusPoint_norm (q : A) : ‖(capAnnulusPoint q).val‖ = q.2.val := by
  change ‖q.2.val • q.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
    mem_sphere_zero_iff_norm.mp q.1.property, mul_one]

private theorem capAnnulusPoint_contMDiff : ContMDiff CI (𝓡∂ 3) ∞ capAnnulusPoint := by
  have hinc : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : ClosedCell 3 → E3) :=
    Manifold.isSmoothEmbedding_closedCell_inclusion 2
  apply (ContMDiff.iff_comp_isImmersion hinc.isImmersion).mpr
  have hc : ContMDiff CI (𝓡 3) ∞ (fun q : A => q.2.val • q.1.val) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_snd).smul (contMDiff_coe_sphere.comp contMDiff_fst)
  exact ⟨hc.continuous.subtype_mk _, hc⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def capAnnulusMap (b : T.Boundary) : C(A, N.Carrier) :=
  ⟨fun q => C.cap b (capAnnulusPoint q),
    (C.cap b).continuous.comp capAnnulusPoint_contMDiff.continuous⟩

theorem contMDiff_capAnnulusMap (b : T.Boundary) :
    ContMDiff CI (𝓡 3) ∞ (C.capAnnulusMap b) :=
  (C.cap_embedding b).contMDiff.comp capAnnulusPoint_contMDiff

theorem capAnnulusMap_injective (b : T.Boundary) : Injective (C.capAnnulusMap b) := by
  intro p q h
  have hpq := (C.cap_embedding b).isEmbedding.injective h
  have hr : p.2 = q.2 := by
    apply Subtype.ext
    have hn := congrArg (fun x : ClosedCell 3 => ‖x.val‖) hpq
    rwa [capAnnulusPoint_norm, capAnnulusPoint_norm] at hn
  apply Prod.ext
  · apply Subtype.ext
    have heq := congrArg Subtype.val hpq
    change p.2.val • p.1.val = q.2.val • q.1.val at heq
    rw [← hr] at heq
    exact smul_right_injective E3 (by linarith [p.2.property.1] : p.2.val ≠ 0) heq
  · exact hr

theorem range_capAnnulusMap (b : T.Boundary) :
    range (C.capAnnulusMap b) = C.cap b '' {x : ClosedCell 3 | 1 / 4 ≤ ‖x.val‖} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨capAnnulusPoint q, by change 1 / 4 ≤ ‖(capAnnulusPoint q).val‖; rw [capAnnulusPoint_norm]; exact q.2.property.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change 1 / 4 ≤ ‖x.val‖ at hx
    have hxn : x.val ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖x.val‖))
    let z : S2 := ⟨‖x.val‖⁻¹ • x.val, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hxn)⟩
    refine ⟨(z, ⟨‖x.val‖, hx, x.property⟩), ?_⟩
    change C.cap b (capAnnulusPoint _) = C.cap b x
    apply congrArg (C.cap b)
    apply Subtype.ext
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hxn), one_smul]

def capAnnulusHomeomorphRange (b : T.Boundary) : A ≃ₜ range (C.capAnnulusMap b) :=
  ((C.capAnnulusMap b).continuous.isClosedEmbedding
    (C.capAnnulusMap_injective b)).isEmbedding.toHomeomorph

@[simp] theorem capAnnulusHomeomorphRange_apply (b : T.Boundary) (q : A) :
    (C.capAnnulusHomeomorphRange b q).val = C.capAnnulusMap b q := rfl

private theorem quarter_norm (z : S2) : ‖(1 / 4 : ℝ) • z.val‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
  norm_num


theorem capAnnulusMap_inner (b : T.Boundary) (z : S2) :
    C.capAnnulusMap b (z, ⟨1 / 4, by norm_num⟩) =
      ((C.capBallChart b).toBallChart.boundaryMap (if b.2 then z else -z)).val := by
  cases hb : b.2 with
  | true =>
    simp only [ite_true]
    change C.cap b (capAnnulusPoint _) = (C.capBallChart b).chart z.val
    rw [C.capBallChart_apply b z.val (by simpa only [hb, ite_true] using quarter_norm z)]
    apply congrArg (C.cap b)
    apply Subtype.ext
    simp [capAnnulusPoint, hb]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    change C.cap b (capAnnulusPoint _) = (C.capBallChart b).chart (-z.val)
    rw [C.capBallChart_apply b (-z.val) (by
      simp only [hb, Bool.false_eq_true, ite_false, smul_neg, neg_smul, neg_neg]
      exact quarter_norm z)]
    apply congrArg (C.cap b)
    apply Subtype.ext
    change (1 / 4 : ℝ) • z.val = (if b.2 then (1 / 4 : ℝ) else -(1 / 4)) • (-z.val)
    simp [hb]

@[simp] theorem capAnnulusMap_outer (b : T.Boundary) (z : S2) :
    C.capAnnulusMap b (z, ⟨1, by norm_num⟩) =
      C.coreInclusion (T.coreBoundarySphere b (C.attaching b z)) := by
  change C.cap b (capAnnulusPoint _) = _
  have heq : capAnnulusPoint (z, ⟨1, by norm_num⟩) = sphereToClosedCell z := by
    apply Subtype.ext
    exact one_smul ℝ z.val
  rw [heq, C.boundary_eq]

private theorem norm_capAnnulusPoint_le_quarter (z : S2) :
    ‖(capAnnulusPoint (z, ⟨1 / 4, by norm_num⟩)).val‖ ≤ 1 / 4 := by
  rw [capAnnulusPoint_norm]

private theorem capAnnulusPoint_outer (z : S2) :
    capAnnulusPoint (z, ⟨1, by norm_num⟩) = sphereToClosedCell z := by
  apply Subtype.ext
  exact one_smul ℝ z.val

private theorem norm_ge_quarter_of_fixes_small
    (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x)
    (x : ClosedCell 3) (hx : 1 / 4 ≤ ‖x.val‖) : 1 / 4 ≤ ‖(B x).val‖ := by
  by_contra! h
  have hfix := hsmall (B x) h.le
  have heq : B x = x := B.injective hfix
  rw [heq] at h
  exact not_lt_of_ge hx h

private theorem symm_fixes_small
    (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x)
    (x : ClosedCell 3) (hx : ‖x.val‖ ≤ 1 / 4) : B.symm x = x := by
  have h := B.symm_apply_apply x
  rw [hsmall x hx] at h
  exact h

private def capAnnulusMapHomeomorph (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (q : A) : A :=
  (C.capAnnulusHomeomorphRange b).symm
    ⟨C.cap b (B (capAnnulusPoint q)), by
      rw [C.range_capAnnulusMap]
      exact ⟨B (capAnnulusPoint q), norm_ge_quarter_of_fixes_small B hsmall _
        (by rw [capAnnulusPoint_norm]; exact q.2.property.1), rfl⟩⟩

private theorem capAnnulusMapHomeomorph_equation (b : T.Boundary)
    (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (q : A) :
    C.capAnnulusMap b (C.capAnnulusMapHomeomorph b B hsmall q) =
      C.cap b (B (capAnnulusPoint q)) := by
  exact congrArg Subtype.val ((C.capAnnulusHomeomorphRange b).apply_symm_apply _)

private theorem capAnnulusMapHomeomorph_point (b : T.Boundary)
    (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (q : A) :
    capAnnulusPoint (C.capAnnulusMapHomeomorph b B hsmall q) = B (capAnnulusPoint q) :=
  (C.cap_embedding b).isEmbedding.injective (C.capAnnulusMapHomeomorph_equation b B hsmall q)

private theorem capAnnulusMapHomeomorph_continuous (b : T.Boundary)
    (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) :
    Continuous (C.capAnnulusMapHomeomorph b B hsmall) :=
  (C.capAnnulusHomeomorphRange b).symm.continuous.comp
    (((C.cap b).continuous.comp (B.continuous.comp capAnnulusPoint_contMDiff.continuous)).subtype_mk _)

def capAnnulusHomeomorph (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) : A ≃ₜ A where
  toFun := C.capAnnulusMapHomeomorph b B hsmall
  invFun := C.capAnnulusMapHomeomorph b B.symm (symm_fixes_small B hsmall)
  left_inv q := by
    apply C.capAnnulusMap_injective b
    rw [C.capAnnulusMapHomeomorph_equation, C.capAnnulusMapHomeomorph_point,
      B.symm_apply_apply]
    rfl
  right_inv q := by
    apply C.capAnnulusMap_injective b
    rw [C.capAnnulusMapHomeomorph_equation, C.capAnnulusMapHomeomorph_point,
      B.apply_symm_apply]
    rfl
  continuous_toFun := C.capAnnulusMapHomeomorph_continuous b B hsmall
  continuous_invFun := C.capAnnulusMapHomeomorph_continuous b B.symm (symm_fixes_small B hsmall)

theorem capAnnulusHomeomorph_apply (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (q : A) :
    C.capAnnulusMap b (C.capAnnulusHomeomorph b B hsmall q) =
      C.cap b (B ⟨q.2.val • q.1.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
          norm_eq_of_mem_sphere, mul_one]
        exact q.2.property.2⟩) :=
  C.capAnnulusMapHomeomorph_equation b B hsmall q

theorem capAnnulusHomeomorph_symm_apply (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (q : A) :
    C.capAnnulusMap b ((C.capAnnulusHomeomorph b B hsmall).symm q) =
      C.cap b (B.symm ⟨q.2.val • q.1.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
          norm_eq_of_mem_sphere, mul_one]
        exact q.2.property.2⟩) :=
  C.capAnnulusMapHomeomorph_equation b B.symm (symm_fixes_small B hsmall) q

theorem capAnnulusHomeomorph_inner (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (z : S2) :
    C.capAnnulusHomeomorph b B hsmall (z, ⟨1 / 4, by norm_num⟩) = (z, ⟨1 / 4, by norm_num⟩) := by
  apply C.capAnnulusMap_injective b
  rw [show C.capAnnulusHomeomorph b B hsmall (z, ⟨1 / 4, by norm_num⟩) =
    C.capAnnulusMapHomeomorph b B hsmall (z, ⟨1 / 4, by norm_num⟩) from rfl,
    C.capAnnulusMapHomeomorph_equation, hsmall _ (norm_capAnnulusPoint_le_quarter z)]
  rfl

@[simp] theorem capAnnulusHomeomorph_outer (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x)
    (hboundary : ∀ z : S2, B (sphereToClosedCell z) = sphereToClosedCell z) (z : S2) :
    C.capAnnulusHomeomorph b B hsmall (z, ⟨1, by norm_num⟩) = (z, ⟨1, by norm_num⟩) := by
  apply C.capAnnulusMap_injective b
  rw [show C.capAnnulusHomeomorph b B hsmall (z, ⟨1, by norm_num⟩) =
    C.capAnnulusMapHomeomorph b B hsmall (z, ⟨1, by norm_num⟩) from rfl,
    C.capAnnulusMapHomeomorph_equation, capAnnulusPoint_outer, hboundary]
  change C.cap b (sphereToClosedCell z) = C.cap b (capAnnulusPoint (z, ⟨1, by norm_num⟩))
  rw [capAnnulusPoint_outer]

end DifferentialGeometry.Topology.SphericalCapping
