/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.InvariantMeasure
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection

noncomputable section

open Set Filter MeasureTheory Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.GeodesicFlow

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology AsymptoticRays HorosphereProjection MobiusBoundary LorentzExtremal

variable {n m : ℕ}

theorem continuous_lor_boundary :
    Continuous (fun p : LorGrp n × BoundaryH n => p.1 • p.2) := by
  apply isEmbedding_val.continuous_iff.mpr
  have hmat : Continuous (matOf : LorGrp n →
      Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
    (MatrixSum.continuous_ofMatrix_symm (Fin n) (Fin 1) ℝ).comp continuous_subtype_val
  have hm : Continuous (fun p : LorGrp n × BoundaryH n => matOf p.1 *ᵥ p.2.val) :=
    Continuous.matrix_mulVec
      (hmat.comp continuous_fst)
      (isEmbedding_val.continuous.comp continuous_snd)
  exact (((continuous_apply (Sum.inr 0)).comp hm).inv₀
    (fun p => tc_matOf_mulVec_ne_zero p.1 p.2)).smul hm

theorem continuous_po_boundary (hn : 1 ≤ n) :
    Continuous (fun p : PO n 1 × BoundaryH n => (poBoundaryMulAction hn).smul p.1 p.2) := by
  have hq : IsOpenQuotientMap (fun A : LorGrp n =>
      (QuotientGroup.mk' _ A : PO n 1)) := QuotientGroup.isOpenQuotientMap_mk
  have hp := hq.prodMap (IsOpenQuotientMap.id (X := BoundaryH n))
  rw [← hp.continuous_comp_iff]
  exact continuous_lor_boundary

abbrev IsometryGroup (m : ℕ) := PO (m + 1) 1

abbrev Tangent (m : ℕ) := HUpper (m + 1) × BoundaryH (m + 1)

instance : MeasurableSpace (Tangent m) := borel _
instance : BorelSpace (Tangent m) := ⟨rfl⟩

local instance : MulAction (IsometryGroup m) (HUpper (m + 1)) := poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (HUpper (m + 1)) :=
  ⟨ContinuousAction.continuous_po_smul (by omega)⟩
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

def flow (t : ℝ) (v : Tangent m) : Tangent m := (rayTo v.1 v.2 t, v.2)

@[simp] theorem flow_zero (v : Tangent m) : flow 0 v = v := by
  simp [flow, rayTo_zero]

theorem flow_add (s t : ℝ) (v : Tangent m) :
    flow (s + t) v = flow t (flow s v) := by
  simp only [flow, rayTo_add]

theorem flow_smul (t : ℝ) (g : IsometryGroup m) (v : Tangent m) :
    flow (m := m) t (g • v : Tangent m) = g • (flow (m := m) t v : Tangent m) := by
  apply Prod.ext
  · exact (BoundaryExtension.po_smul_rayTo (by omega) g v.1 v.2 t).symm
  · rfl

theorem continuous_flow : Continuous (fun p : ℝ × Tangent m => flow p.1 p.2) := by
  apply Continuous.prodMk _ continuous_snd.snd
  apply StratumDeformation.continuous_of_val
  have hx : Continuous (fun p : ℝ × Tangent m => p.2.1.val) :=
    continuous_val.comp continuous_snd.fst
  have hξ : Continuous (fun p : ℝ × Tangent m => p.2.2.val) :=
    isEmbedding_val.continuous.comp continuous_snd.snd
  have hL : Continuous (fun p : ℝ × Tangent m => -lorB p.2.1.val p.2.2.val) :=
    (ContinuousAction.continuous_lorB_pair.comp (hx.prodMk hξ)).neg
  have h := ((Real.continuous_exp.comp continuous_fst.neg).smul hx).add
    (((Real.continuous_sinh.comp continuous_fst).div hL
      (fun p => (Busemann.neg_lorB_upper_boundary_pos p.2.1 p.2.2).ne')).smul hξ)
  exact h.congr (fun p => (rayTo_val_exp p.2.1 p.2.2 p.1).symm)

def flowHomeomorph (t : ℝ) : Tangent m ≃ₜ Tangent m where
  toFun := flow t
  invFun := flow (-t)
  left_inv v := by rw [← flow_add, add_neg_cancel, flow_zero]
  right_inv v := by rw [← flow_add, neg_add_cancel, flow_zero]
  continuous_toFun := continuous_flow.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := continuous_flow.comp (continuous_const.prodMk continuous_id)

abbrev GeodesicQuotient (Γ : Subgroup (IsometryGroup m)) :=
  MulAction.orbitRel.Quotient Γ (Tangent m)

def projection (Γ : Subgroup (IsometryGroup m)) : Tangent m → GeodesicQuotient Γ :=
  Quotient.mk''

theorem measurable_projection (Γ : Subgroup (IsometryGroup m)) :
    Measurable (projection Γ) := measurable_quotient_mk''

def quotientFlow (Γ : Subgroup (IsometryGroup m)) (t : ℝ) :
    GeodesicQuotient Γ → GeodesicQuotient Γ :=
  Quotient.map (flow t) fun v w h => by
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ, ?_⟩
    change (γ : IsometryGroup m) • w = v at hγ
    change (γ : IsometryGroup m) • flow t w = flow t v
    rw [← flow_smul, hγ]

@[simp] theorem quotientFlow_projection (Γ : Subgroup (IsometryGroup m))
    (t : ℝ) (v : Tangent m) :
    quotientFlow Γ t (projection Γ v) = projection Γ (flow t v) := rfl

@[simp] theorem quotientFlow_zero (Γ : Subgroup (IsometryGroup m)) (v : GeodesicQuotient Γ) :
    quotientFlow Γ 0 v = v := by
  induction v using Quotient.inductionOn with
  | h v => change projection Γ (flow 0 v) = projection Γ v; rw [flow_zero]

theorem quotientFlow_add (Γ : Subgroup (IsometryGroup m)) (s t : ℝ)
    (v : GeodesicQuotient Γ) :
    quotientFlow Γ (s + t) v = quotientFlow Γ t (quotientFlow Γ s v) := by
  induction v using Quotient.inductionOn with
  | h v => change projection Γ (flow (s + t) v) = projection Γ (flow t (flow s v))
           rw [flow_add]

theorem measurable_quotientFlow (Γ : Subgroup (IsometryGroup m)) (t : ℝ) :
    Measurable (quotientFlow Γ t) := by
  apply measurable_from_quotient.mpr
  exact (measurable_projection Γ).comp (flowHomeomorph t).continuous.measurable

theorem continuous_quotientFlow (Γ : Subgroup (IsometryGroup m)) :
    Continuous (fun p : ℝ × GeodesicQuotient Γ => quotientFlow Γ p.1 p.2) := by
  have hq : IsOpenQuotientMap (projection Γ) := MulAction.isOpenQuotientMap_quotientMk
  have hp := (IsOpenQuotientMap.id (X := ℝ)).prodMap hq
  rw [← hp.continuous_comp_iff]
  change Continuous (fun p : ℝ × Tangent m => projection Γ (flow p.1 p.2))
  exact continuous_quotient_mk'.comp continuous_flow

def quotientFlowHomeomorph (Γ : Subgroup (IsometryGroup m)) (t : ℝ) :
    GeodesicQuotient Γ ≃ₜ GeodesicQuotient Γ where
  toFun := quotientFlow Γ t
  invFun := quotientFlow Γ (-t)
  left_inv q := by rw [← quotientFlow_add, add_neg_cancel, quotientFlow_zero]
  right_inv q := by rw [← quotientFlow_add, neg_add_cancel, quotientFlow_zero]
  continuous_toFun := (continuous_quotientFlow Γ).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (continuous_quotientFlow Γ).comp (continuous_const.prodMk continuous_id)

@[instance_reducible]
def realAction (Γ : Subgroup (IsometryGroup m)) :
    MulAction (Multiplicative ℝ) (GeodesicQuotient Γ) where
  smul t q := quotientFlow Γ t.toAdd q
  one_smul q := quotientFlow_zero Γ q
  mul_smul s t q := by
    change quotientFlow Γ (s.toAdd + t.toAdd) q =
      quotientFlow Γ s.toAdd (quotientFlow Γ t.toAdd q)
    rw [add_comm, quotientFlow_add]

def standardTangent : Tangent m := (basepointH, ptInfty)

def frameProjection (Γ : Subgroup (IsometryGroup m)) :
    DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ → GeodesicQuotient Γ :=
  Quotient.map (fun g : IsometryGroup m => g • (standardTangent : Tangent m)) fun g h hgh => by
    obtain ⟨γ, hγ⟩ := hgh
    refine ⟨γ, ?_⟩
    change (γ : IsometryGroup m) * h = g at hγ
    change (γ : IsometryGroup m) • (h • (standardTangent : Tangent m)) = g • standardTangent
    rw [← mul_smul, hγ]

@[simp] theorem frameProjection_projection (Γ : Subgroup (IsometryGroup m))
    (g : IsometryGroup m) :
    frameProjection Γ (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g) =
      projection Γ (g • (standardTangent : Tangent m)) := rfl

theorem measurable_frameProjection (Γ : Subgroup (IsometryGroup m)) :
    Measurable (frameProjection Γ) := by
  apply measurable_from_quotient.mpr
  exact (measurable_projection Γ).comp
    ((continuous_id.smul continuous_const).measurable :
      Measurable (fun g : IsometryGroup m => g • (standardTangent : Tangent m)))

def diagonal (t : ℝ) : IsometryGroup m :=
  QuotientGroup.mk' _ (dilateLor (Real.exp t) (Real.exp_pos t))

theorem diagonal_standardTangent (t : ℝ) :
    (diagonal t : IsometryGroup m) • (standardTangent : Tangent m) =
      flow t standardTangent := by
  apply Prod.ext
  · change actH (dilateLor (Real.exp t) (Real.exp_pos t)) basepointH =
      rayTo basepointH ptInfty t
    apply HUpper.ext
    have he : matOf (dilateLor (Real.exp t) (Real.exp_pos t)) *ᵥ
        (basepointH : HUpper (m + 1)).val = (rayTo basepointH ptInfty t).val := by
      rw [dilateLor_matOf, rayTo_val_exp]
      have hB : -lorB (basepointH : HUpper (m + 1)).val
          (ptInfty : BoundaryH (m + 1)).val = 1 := by
        simp [basepointH, lorB, sdot, eTime, tc, ptInfty_val_time]
      rw [hB, div_one]
      funext i
      rcases i with j | j
      · refine Fin.lastCases ?_ (fun k => ?_) j
        · rw [HyperbolicTransitive.boostMat_mulVec_inl_self]
          simp [basepointH, eTime, ptInfty_val_last, Real.sinh_eq, Real.exp_neg]
        · rw [HyperbolicTransitive.boostMat_mulVec_inl_ne _ _ _ _ (Fin.castSucc_ne_last k)]
          simp [basepointH, eTime, ptInfty_val_castSucc]
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [HyperbolicTransitive.boostMat_mulVec_inr]
        simp [basepointH, eTime, ptInfty_val_time, Real.sinh_eq, Real.exp_neg]
        ring
    change upperize _ = _
    rw [he, upperize, ite_eq_left (rayTo basepointH ptInfty t).future]
  · change actB (dilateLor (Real.exp t) (Real.exp_pos t)) ptInfty = ptInfty
    apply BoundaryFixedPoints.boundary_fixed_of_eigen _ _ (Real.exp_ne_zero t)
    rw [dilateLor_matOf]
    funext i
    rcases i with j | j
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [HyperbolicTransitive.boostMat_mulVec_inl_self]
        simp only [ptInfty_val_last, ptInfty_val_time, Pi.smul_apply, smul_eq_mul]
        ring
      · rw [HyperbolicTransitive.boostMat_mulVec_inl_ne _ _ _ _ (Fin.castSucc_ne_last k)]
        simp [ptInfty_val_castSucc]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [HyperbolicTransitive.boostMat_mulVec_inr]
      simp only [ptInfty_val_last, ptInfty_val_time, Pi.smul_apply, smul_eq_mul]
      ring

theorem frameProjection_right_diagonal (Γ : Subgroup (IsometryGroup m))
    (t : ℝ) (q : DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ) :
    frameProjection Γ (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (diagonal t) q) =
      quotientFlow Γ t (frameProjection Γ q) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change projection Γ ((g * diagonal t) • (standardTangent : Tangent m)) =
      projection Γ (flow (m := m) t (g • standardTangent))
    rw [mul_smul, diagonal_standardTangent, flow_smul]

theorem exists_invariant_probability (Γ : Subgroup (IsometryGroup m))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (IsometryGroup m)]
    (hcov : covolume Γ (IsometryGroup m) ≠ ⊤) :
    ∃ ν : Measure (GeodesicQuotient Γ), IsProbabilityMeasure ν ∧
      (∀ t : ℝ, MeasurePreserving (quotientFlow Γ t) ν ν) ∧
      (∀ U : Set (GeodesicQuotient Γ), MeasurableSet U →
        (ν U = 0 ↔ volume ((fun g : IsometryGroup m =>
          projection Γ (g • standardTangent)) ⁻¹' U) = 0)) := by
  obtain ⟨μ, hμ, hr, hn⟩ := DifferentialGeometry.HomogeneousSpaceMeasure.exists_invariant_probability Γ disc hcov
  let := hμ
  let ν := μ.map (frameProjection Γ)
  refine ⟨ν, by
    dsimp [ν]
    infer_instance,
    fun t => ⟨measurable_quotientFlow Γ t, ?_⟩, fun U hU => ?_⟩
  · change (μ.map (frameProjection Γ)).map (quotientFlow Γ t) = μ.map (frameProjection Γ)
    rw [Measure.map_map (measurable_quotientFlow Γ t) (measurable_frameProjection Γ)]
    have he : quotientFlow Γ t ∘ frameProjection Γ =
        frameProjection Γ ∘ DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (diagonal t) :=
      funext (fun q => (frameProjection_right_diagonal Γ t q).symm)
    rw [he, ← Measure.map_map (measurable_frameProjection Γ)
      (DifferentialGeometry.HomogeneousSpaceMeasure.measurable_right Γ (diagonal t)), (hr (diagonal t)).map_eq]
  · change μ.map (frameProjection Γ) U = 0 ↔ _
    rw [Measure.map_apply (measurable_frameProjection Γ) hU,
      hn _ ((measurable_frameProjection Γ) hU)]
    rfl

end DifferentialGeometry.GeodesicFlow
