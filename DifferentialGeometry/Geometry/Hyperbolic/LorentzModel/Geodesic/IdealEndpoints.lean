/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Measure

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryGeodesic

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary BoundaryTopology
open MobiusBoundary Horospherical AsymptoticRays HorosphereProjection
open EuclideanBoundary GeodesicFlow BoundaryMeasure

variable {n m : ℕ}

def reverseVector (x ξ : LorVec n) : LorVec n := (2 * -lorB x ξ) • x - ξ

theorem reverseVector_neg_left (x ξ : LorVec n) :
    reverseVector (-x) ξ = reverseVector x ξ := by
  simp only [reverseVector, lorB_neg_left, neg_neg, smul_neg, ← neg_smul]
  congr 2
  ring

theorem reverseVector_smul_right (c : ℝ) (x ξ : LorVec n) :
    reverseVector x (c • ξ) = c • reverseVector x ξ := by
  simp only [reverseVector, lorB_smul_right, smul_sub, smul_smul]
  congr 2
  ring

theorem reverseVector_lor (A : LorGrp n) (x ξ : LorVec n) :
    reverseVector (matOf A *ᵥ x) (matOf A *ᵥ ξ) = matOf A *ᵥ reverseVector x ξ := by
  simp only [reverseVector, lorB_matOf_mulVec, mulVec_sub, mulVec_smul]

theorem reverseVector_null (x : HUpper n) (ξ : BoundaryH n) :
    lorB (reverseVector x.val ξ.val) (reverseVector x.val ξ.val) = 0 := by
  simp only [reverseVector, lorB_sub_left, lorB_sub_right, lorB_smul_left,
    lorB_smul_right, x.is_unit, ξ.is_null, lorB_comm ξ.val x.val]
  ring

theorem lorB_reverseVector (x : HUpper n) (ξ : BoundaryH n) :
    lorB x.val (reverseVector x.val ξ.val) = lorB x.val ξ.val := by
  simp only [reverseVector, lorB_sub_right, lorB_smul_right, x.is_unit]
  ring

theorem reverseVector_time_ne_zero (x : HUpper n) (ξ : BoundaryH n) :
    tc (reverseVector x.val ξ.val) ≠ 0 := by
  intro ht
  have hz := eq_zero_of_lorB_self_eq_zero (reverseVector_null x ξ) ht
  have h := lorB_reverseVector x ξ
  rw [hz] at h
  have hn := lorB_hUpper_boundary_neg x ξ
  have hzero : lorB x.val (0 : LorVec n) = 0 := by simp [lorB, sdot, tc]
  rw [hzero] at h
  linarith

def backwardEndpoint (v : Tangent m) : BoundaryH (m + 1) :=
  ⟨boundaryRep (reverseVector v.1.val v.2.val),
    lorB_boundaryRep_self (reverseVector_null v.1 v.2),
    tc_boundaryRep (reverseVector_time_ne_zero v.1 v.2)⟩

theorem continuous_backwardEndpoint : Continuous (backwardEndpoint (m := m)) := by
  apply isEmbedding_val.continuous_iff.mpr
  have hx : Continuous (fun v : Tangent m => v.1.val) :=
    LorentzExtremal.continuous_val.comp continuous_fst
  have hξ : Continuous (fun v : Tangent m => v.2.val) :=
    isEmbedding_val.continuous.comp continuous_snd
  have hL := (ContinuousAction.continuous_lorB_pair.comp (hx.prodMk hξ)).neg
  have hr : Continuous (fun v : Tangent m => reverseVector v.1.val v.2.val) :=
    ((continuous_const.mul hL).smul hx).sub hξ
  exact (((continuous_apply (Sum.inr 0)).comp hr).inv₀
    (fun v => reverseVector_time_ne_zero v.1 v.2)).smul hr

local instance : MulAction (IsometryGroup m) (HUpper (m + 1)) := poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)

theorem backwardEndpoint_lor (A : LorGrp (m + 1)) (v : Tangent m) :
    backwardEndpoint (actH A v.1, actB A v.2) = actB A (backwardEndpoint v) := by
  have hc := tc_matOf_mulVec_ne_zero A v.2
  have ht := tc_matOf_mulVec_ne_zero_of_null A (reverseVector_null v.1 v.2)
    (reverseVector_time_ne_zero v.1 v.2)
  have he : reverseVector (actH A v.1).val (actB A v.2).val =
      (tc (matOf A *ᵥ v.2.val))⁻¹ • (matOf A *ᵥ reverseVector v.1.val v.2.val) := by
    change reverseVector (upperize (matOf A *ᵥ v.1.val))
      (boundaryRep (matOf A *ᵥ v.2.val)) = _
    rw [boundaryRep, reverseVector_smul_right]
    unfold upperize
    split_ifs
    · rw [reverseVector_lor]
    · rw [reverseVector_neg_left, reverseVector_lor]
  apply BoundaryH.ext
  change boundaryRep (reverseVector (actH A v.1).val (actB A v.2).val) =
    boundaryRep (matOf A *ᵥ boundaryRep (reverseVector v.1.val v.2.val))
  rw [he, boundaryRep_smul _ (inv_ne_zero hc),
    show boundaryRep (reverseVector v.1.val v.2.val) =
      (tc (reverseVector v.1.val v.2.val))⁻¹ • reverseVector v.1.val v.2.val from rfl,
    mulVec_smul, boundaryRep_smul _ (inv_ne_zero (reverseVector_time_ne_zero v.1 v.2))]

theorem backwardEndpoint_smul (g : IsometryGroup m) (v : Tangent m) :
    backwardEndpoint (g • v) = g • backwardEndpoint v := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  exact backwardEndpoint_lor A v

theorem reverseVector_rayTo (x : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    reverseVector (rayTo x ξ t).val ξ.val =
      (Real.exp (-t)) ^ 2 • reverseVector x.val ξ.val := by
  have hL : -lorB x.val ξ.val ≠ 0 := (neg_pos.mpr (lorB_hUpper_boundary_neg x ξ)).ne'
  have hL' : lorB x.val ξ.val ≠ 0 := neg_ne_zero.mp hL
  rw [reverseVector, neg_lorB_rayTo, rayTo_val_exp, reverseVector]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.sinh_eq, Real.exp_neg]
  field_simp [hL']
  ring

theorem backwardEndpoint_flow (t : ℝ) (v : Tangent m) :
    backwardEndpoint (flow t v) = backwardEndpoint v := by
  apply BoundaryH.ext
  change boundaryRep (reverseVector (rayTo v.1 v.2 t).val v.2.val) =
    boundaryRep (reverseVector v.1.val v.2.val)
  rw [reverseVector_rayTo, boundaryRep_smul _
    (pow_ne_zero _ (Real.exp_ne_zero _))]

theorem backwardEndpoint_standard :
    backwardEndpoint (standardTangent : Tangent m) = embed (0 : Horizontal m) := by
  have he : reverseVector (basepointH : HUpper (m + 1)).val (ptInfty : BoundaryH (m + 1)).val =
      (2 : ℝ) • horoVec (0 : Fin m → ℝ) := by
    have hL : -lorB (basepointH : HUpper (m + 1)).val (ptInfty : BoundaryH (m + 1)).val = 1 := by
      simp [basepointH, lorB, sdot, eTime, tc, ptInfty_val_time]
    rw [reverseVector, hL]
    funext i
    rcases i with j | j
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · norm_num [basepointH, eTime, Pi.single_apply, ptInfty_val_last, horoVec_last, normSq]
      · simp [basepointH, eTime, ptInfty_val_castSucc, horoVec_castSucc]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      norm_num [basepointH, eTime, ptInfty_val_time, horoVec_time, normSq]
  apply BoundaryH.ext
  change boundaryRep (reverseVector (basepointH : HUpper (m + 1)).val ptInfty.val) =
    boundaryRep (horoVec (0 : Fin m → ℝ))
  rw [he, boundaryRep_smul 2 (by norm_num)]

def endpoints (v : Tangent m) : BoundaryH (m + 1) × BoundaryH (m + 1) :=
  (v.2, backwardEndpoint v)

theorem continuous_endpoints : Continuous (endpoints (m := m)) :=
  continuous_snd.prodMk continuous_backwardEndpoint

theorem endpoints_smul (g : IsometryGroup m) (v : Tangent m) :
    endpoints (g • v) = g • endpoints v :=
  Prod.ext rfl (backwardEndpoint_smul g v)

theorem endpoints_flow (t : ℝ) (v : Tangent m) : endpoints (flow t v) = endpoints v :=
  Prod.ext rfl (backwardEndpoint_flow t v)

theorem endpoints_standard :
    endpoints (standardTangent : Tangent m) = (ptInfty, embed (0 : Horizontal m)) :=
  Prod.ext rfl backwardEndpoint_standard

theorem endpoints_smul_standard (g : IsometryGroup m) :
    endpoints (g • (standardTangent : Tangent m)) = endpointPair g := by
  rw [endpoints_smul, endpoints_standard]
  rfl

end DifferentialGeometry.BoundaryGeodesic
