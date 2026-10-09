/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Charts
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.GeodesicFlow

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.LorentzGenerators

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology MobiusBoundary Horospherical AsymptoticRays HorosphereProjection
open GeodesicFlow

variable {m : ℕ}

theorem lor_ext {n : ℕ} {A B : LorGrp n} (h : matOf A = matOf B) : A = B :=
  Subtype.ext (MatrixSum.ofMatrix.symm.injective h)

local instance : MulAction (IsometryGroup m) (HUpper (m + 1)) := poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (HUpper (m + 1)) :=
  ⟨ContinuousAction.continuous_po_smul (by omega)⟩
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

def translation (b : Fin m → ℝ) : IsometryGroup m := QuotientGroup.mk' _ (transLor b)
def inversion : IsometryGroup m := QuotientGroup.mk' _ invertLor

def transverse : Subgroup (IsometryGroup m) :=
  MulAction.stabilizer (IsometryGroup m) (standardTangent : Tangent m)

theorem mem_transverse (g : IsometryGroup m) :
    g ∈ transverse ↔ g • (standardTangent : Tangent m) = standardTangent := Iff.rfl

theorem isCompact_transverse : IsCompact (↑(transverse (m := m)) : Set (IsometryGroup m)) := by
  have hclosed : IsClosed (↑(transverse (m := m)) : Set (IsometryGroup m)) :=
    isClosed_eq (continuous_id.smul continuous_const) continuous_const
  apply (StabilizerCompact.isCompact_stabilizer_basepoint (by omega : 1 ≤ m + 1)).of_isClosed_subset
    hclosed
  intro g hg
  exact congrArg Prod.fst (mem_transverse g |>.mp hg)

theorem same_tangent_iff (g h : IsometryGroup m) :
    g • (standardTangent : Tangent m) = h • standardTangent ↔ h⁻¹ * g ∈ transverse := by
  rw [mem_transverse, mul_smul, inv_smul_eq_iff]

theorem eq_of_horo (hm : 1 ≤ m) {g h : IsometryGroup m}
    (he : ∀ x : Fin m → ℝ, g • horo x = h • horo x) : g = h := by
  apply eq_of_po_boundary_smul_eq (by omega : 2 ≤ m + 1)
  exact eq_on_boundary_of_eq_on_horo (continuous_const_smul g) (continuous_const_smul h) hm he

@[simp] theorem translation_horo (b x : Fin m → ℝ) :
    translation b • horo x = horo (x + b) := trans_po_smul_horo b x

theorem diagonal_horo (t : ℝ) (x : Fin m → ℝ) :
    (GeodesicFlow.diagonal t : IsometryGroup m) • horo x = horo (Real.exp t • x) :=
  dilate_po_smul_horo _ _ _

theorem translation_infty (b : Fin m → ℝ) :
    translation b • (ptInfty : BoundaryH (m + 1)) = ptInfty := by
  change actB (transLor b) ptInfty = ptInfty
  exact BoundaryFixedPoints.boundary_fixed_of_eigen _ _ one_ne_zero
    (by simpa only [one_smul] using transLor_fix_ptInfty b)

theorem inversion_infty : (inversion : IsometryGroup m) • ptInfty = horo (0 : Fin m → ℝ) :=
  CuspCharts.invert_po_smul_ptInfty

theorem diagonal_infty (t : ℝ) :
    (GeodesicFlow.diagonal t : IsometryGroup m) • (ptInfty : BoundaryH (m + 1)) = ptInfty :=
  congrArg Prod.snd (diagonal_standardTangent t)

theorem translation_zero (hm : 1 ≤ m) : translation (0 : Fin m → ℝ) = 1 := by
  apply eq_of_horo hm
  intro x
  simp

theorem diagonal_zero (hm : 1 ≤ m) : (GeodesicFlow.diagonal 0 : IsometryGroup m) = 1 := by
  apply eq_of_horo hm
  intro x
  simp [diagonal_horo]

theorem diagonal_add (hm : 1 ≤ m) (s t : ℝ) :
    (GeodesicFlow.diagonal (s + t) : IsometryGroup m) =
      GeodesicFlow.diagonal s * GeodesicFlow.diagonal t := by
  apply eq_of_horo hm
  intro x
  simp only [mul_smul, diagonal_horo, Real.exp_add, mul_smul]

theorem diagonal_inv (hm : 1 ≤ m) (t : ℝ) :
    (GeodesicFlow.diagonal t : IsometryGroup m)⁻¹ = GeodesicFlow.diagonal (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← diagonal_add hm, add_neg_cancel, diagonal_zero hm]

theorem diagonal_translation (hm : 1 ≤ m) (t : ℝ) (b : Fin m → ℝ) :
    GeodesicFlow.diagonal (m := m) t * translation b * (GeodesicFlow.diagonal (m := m) t)⁻¹ =
      translation (Real.exp t • b) := by
  apply eq_of_horo hm
  intro x
  rw [diagonal_inv hm]
  simp only [mul_smul, diagonal_horo, translation_horo, smul_add]
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem inversion_sq : (inversion : IsometryGroup m) * inversion = 1 := by
  have h : (invertLor : LorGrp (m + 1)) * invertLor = 1 := by
    apply Subtype.ext
    exact DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat_sq (Fin.last m)
  simpa only [inversion, map_mul, map_one] using congrArg (QuotientGroup.mk' _) h

@[simp] theorem inversion_inv : (inversion : IsometryGroup m)⁻¹ = inversion :=
  inv_eq_of_mul_eq_one_right inversion_sq

theorem inversion_diagonal (t : ℝ) :
    (inversion : IsometryGroup m) * GeodesicFlow.diagonal t * inversion =
      GeodesicFlow.diagonal (-t) := by
  have h : (invertLor : LorGrp (m + 1)) * dilateLor (Real.exp t) (Real.exp_pos t) * invertLor =
      dilateLor (Real.exp (-t)) (Real.exp_pos (-t)) := by
    apply lor_ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [matOf_mul, invertLor_matOf, dilateLor_matOf, ← mulVec_mulVec]
    funext i
    rcases i with j | j
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [signMat_mulVec_apply, Sum.elim_inl, ite_true,
          HyperbolicTransitive.boostMat_mulVec_inl_self, Sum.elim_inr, one_mul,
          Real.exp_neg, inv_inv]
        ring
      · simp only [signMat_mulVec_apply, Sum.elim_inl, Fin.castSucc_ne_last, ite_false, one_mul,
          HyperbolicTransitive.boostMat_mulVec_inl_ne _ _ _ _ (Fin.castSucc_ne_last k)]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [signMat_mulVec_apply, Sum.elim_inr, one_mul,
        HyperbolicTransitive.boostMat_mulVec_inr, Sum.elim_inl, ite_true,
        Real.exp_neg, inv_inv]
      ring
  simpa only [inversion, GeodesicFlow.diagonal, map_mul] using congrArg (QuotientGroup.mk' _) h

def oppositeTranslation (b : Fin m → ℝ) : IsometryGroup m :=
  inversion * translation b * inversion

theorem diagonal_oppositeTranslation (hm : 1 ≤ m) (t : ℝ) (b : Fin m → ℝ) :
    GeodesicFlow.diagonal (m := m) t * oppositeTranslation b *
      (GeodesicFlow.diagonal (m := m) t)⁻¹ =
      oppositeTranslation (Real.exp (-t) • b) := by
  have hcomm (s : ℝ) :
      (GeodesicFlow.diagonal s : IsometryGroup m) * inversion =
        inversion * GeodesicFlow.diagonal (-s) := by
    have h := inversion_diagonal (m := m) s
    have h' := congrArg (fun z : IsometryGroup m => inversion * z) h
    simpa only [← mul_assoc, inversion_sq, one_mul] using h'
  rw [oppositeTranslation, diagonal_inv hm]
  calc
    _ = (GeodesicFlow.diagonal t * inversion) * translation b *
          (inversion * GeodesicFlow.diagonal (-t)) := by group
    _ = (inversion * GeodesicFlow.diagonal (-t)) * translation b *
          (GeodesicFlow.diagonal t * inversion) := by rw [hcomm t]
    _ = inversion * (GeodesicFlow.diagonal (-t) * translation b *
          GeodesicFlow.diagonal t) * inversion := by group
    _ = _ := by
      have hi : (GeodesicFlow.diagonal (-t) : IsometryGroup m)⁻¹ = GeodesicFlow.diagonal t := by
        simpa only [neg_neg] using diagonal_inv hm (-t)
      rw [← hi, diagonal_translation hm]
      rfl

theorem continuous_translation : Continuous (translation : (Fin m → ℝ) → IsometryGroup m) := by
  apply QuotientGroup.isOpenQuotientMap_mk.continuous.comp
  apply continuous_induced_rng.mpr
  apply (MatrixSum.continuous_ofMatrix (Fin (m + 1)) (Fin 1) ℝ).comp
  change Continuous (fun b : Fin m → ℝ => matOf (transLor b))
  simp only [transLor_matOf]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun b : Fin m → ℝ => transBlock b (toIdx3 i) (toIdx3 j))
  cases toIdx3 i <;> cases toIdx3 j <;> simp only [transBlock, normSq] <;> fun_prop

theorem continuous_oppositeTranslation :
    Continuous (oppositeTranslation : (Fin m → ℝ) → IsometryGroup m) :=
  (continuous_const.mul continuous_translation).mul continuous_const

theorem tendsto_conjugate_translation (hm : 1 ≤ m) (b : Fin m → ℝ) :
    Tendsto (fun k : ℕ => GeodesicFlow.diagonal (m := m) (-(k : ℝ)) * translation b *
      (GeodesicFlow.diagonal (m := m) (-(k : ℝ)))⁻¹) atTop (𝓝 1) := by
  simp only [diagonal_translation hm]
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ)) • b) atTop (𝓝 0) := by
    simpa using he.smul_const b
  simpa only [translation_zero hm, Function.comp_def] using (continuous_translation.tendsto 0).comp hb

theorem tendsto_conjugate_oppositeTranslation (hm : 1 ≤ m) (b : Fin m → ℝ) :
    Tendsto (fun k : ℕ => GeodesicFlow.diagonal (m := m) (k : ℝ) * oppositeTranslation b *
      (GeodesicFlow.diagonal (m := m) (k : ℝ))⁻¹) atTop (𝓝 1) := by
  simp only [diagonal_oppositeTranslation hm]
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ)) • b) atTop (𝓝 0) := by
    simpa using he.smul_const b
  simpa only [oppositeTranslation, translation_zero hm, mul_one, inversion_sq, Function.comp_def] using
    (continuous_oppositeTranslation.tendsto 0).comp hb

end DifferentialGeometry.LorentzGenerators
