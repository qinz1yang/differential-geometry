/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.HorosphericalGenerators

noncomputable section

open Set Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.TransverseGeneration

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology MobiusBoundary Horospherical AsymptoticRays HorosphereProjection
open GeodesicFlow LorentzGenerators

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (HUpper (m + 1)) := poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)

def reflectionLor (k : Fin m) : LorGrp (m + 1) :=
  ⟨DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMatM k.castSucc, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat_mem k.castSucc⟩

def reflection (k : Fin m) : IsometryGroup m := QuotientGroup.mk' _ (reflectionLor k)

theorem reflection_mem_transverse (k : Fin m) : reflection k ∈ transverse := by
  rw [mem_transverse]
  have hp : matOf (reflectionLor k) *ᵥ (ptInfty : BoundaryH (m + 1)).val = ptInfty.val := by
    funext i
    change (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat k.castSucc *ᵥ ptInfty.val) i = _
    rw [signMat_mulVec_apply]
    rcases i with j | j
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · simp [(Fin.castSucc_ne_last k).symm]
      · simp [ptInfty_val_castSucc]
    · simp
  have hb : matOf (reflectionLor k) *ᵥ (basepointH : HUpper (m + 1)).val = basepointH.val := by
    funext i
    change (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat k.castSucc *ᵥ (basepointH : HUpper (m + 1)).val) i = _
    rw [signMat_mulVec_apply]
    rcases i with j | j <;> simp [basepointH, eTime]
  apply Prod.ext
  · change actH (reflectionLor k) basepointH = basepointH
    apply HUpper.ext
    change upperize _ = _
    rw [hb, upperize, ite_eq_left (basepointH : HUpper (m + 1)).future]
  · change actB (reflectionLor k) ptInfty = ptInfty
    exact BoundaryFixedPoints.boundary_fixed_of_eigen _ _ one_ne_zero (by simpa using hp)

theorem normSq_single (k : Fin m) (c : ℝ) : normSq (Pi.single k c) = c ^ 2 := by
  simp [normSq, Pi.single_apply]

theorem dotB_single (k : Fin m) (c : ℝ) (v : Fin m → ℝ) :
    dotB (Pi.single k c) v = c * v k := by
  simp [dotB, Pi.single_apply]

theorem three_unipotents (k : Fin m) :
    translation (Pi.single k 1) * oppositeTranslation (Pi.single k (-1)) *
        translation (Pi.single k 1) = reflection k * inversion := by
  have h : transLor (Pi.single k 1) * invertLor * transLor (Pi.single k (-1)) *
      invertLor * transLor (Pi.single k 1) = reflectionLor k * invertLor := by
    apply lor_ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    simp only [matOf_mul, transLor_matOf, invertLor_matOf, ← mulVec_mulVec]
    change (transMat (Pi.single k 1) *ᵥ
      (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat (Fin.last m) *ᵥ (transMat (Pi.single k (-1)) *ᵥ
        (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat (Fin.last m) *ᵥ (transMat (Pi.single k 1) *ᵥ v))))) =
      DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat k.castSucc *ᵥ (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.signMat (Fin.last m) *ᵥ v)
    funext i
    rcases i with j | j
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · simp [transMat_mulVec_axis, transMat_mulVec_time, transMat_mulVec_horiz,
          normSq_single, dotB_single, horizOf, signMat_mulVec_apply,
          (Fin.castSucc_ne_last k).symm, -mulVec_mulVec]
        ring
      · by_cases hl : l = k
        · subst l
          simp [transMat_mulVec_axis, transMat_mulVec_time, transMat_mulVec_horiz,
            normSq_single, dotB_single, horizOf, signMat_mulVec_apply, -mulVec_mulVec]
          ring
        · simp [transMat_mulVec_horiz, signMat_mulVec_apply, hl,
            -mulVec_mulVec]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [transMat_mulVec_axis, transMat_mulVec_time, transMat_mulVec_horiz,
        normSq_single, dotB_single, horizOf, signMat_mulVec_apply, -mulVec_mulVec]
      ring
  simpa only [translation, oppositeTranslation, reflection, inversion, map_mul, mul_assoc] using
    congrArg (QuotientGroup.mk' _) h

theorem inversion_mem (hm : 1 ≤ m) (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    (hM : transverse ≤ H) : (inversion : IsometryGroup m) ∈ H := by
  let k : Fin m := ⟨0, hm⟩
  have hw := H.mul_mem (H.mul_mem (hT (Pi.single k 1)) (hO (Pi.single k (-1))))
    (hT (Pi.single k 1))
  rw [three_unipotents] at hw
  have hr := hM (reflection_mem_transverse k)
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hr) hw

theorem diagonal_basepoint (t : ℝ) :
    (GeodesicFlow.diagonal t : IsometryGroup m) • (basepointH : HUpper (m + 1)) =
      ofCoords 0 (Real.exp t) (Real.exp_pos t) := by
  have he := congrArg Prod.fst (diagonal_standardTangent (m := m) t)
  change (GeodesicFlow.diagonal t : IsometryGroup m) • basepointH =
    rayTo basepointH ptInfty t at he
  rw [he]
  apply HUpper.ext
  rw [rayTo_val_exp]
  have hB : -lorB (basepointH : HUpper (m + 1)).val
      (ptInfty : BoundaryH (m + 1)).val = 1 := by
    simp [basepointH, lorB, sdot, eTime, tc, ptInfty_val_time]
  rw [hB, div_one]
  change Real.exp (-t) • (basepointH : HUpper (m + 1)).val + Real.sinh t • ptInfty.val =
    ofCoordsVec (0 : Horizontal m) (Real.exp t)
  rw [ofCoordsVec]
  funext i
  rcases i with j | j
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [basepointH, eTime, ptInfty_val_last, horoVec_last, normSq,
        Real.sinh_eq, Real.exp_neg]
      ring
    · simp [basepointH, eTime, ptInfty_val_castSucc, horoVec_castSucc]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [basepointH, eTime, ptInfty_val_time, horoVec_time, normSq,
      Real.sinh_eq, Real.exp_neg]
    ring

theorem affine_standard (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    (translation (fun i => x i) * GeodesicFlow.diagonal (Real.log h)) •
      (standardTangent : Tangent m) = (ofCoords x h hh, ptInfty) := by
  apply Prod.ext
  · change (translation (fun i => x i) * GeodesicFlow.diagonal (Real.log h)) •
      (basepointH : HUpper (m + 1)) = ofCoords x h hh
    rw [mul_smul, diagonal_basepoint]
    simp only [Real.exp_log hh]
    change actH (transLor (fun i => x i)) (ofCoords 0 h hh) = ofCoords x h hh
    have ht := transLor_smul_ofCoords x (0 : Horizontal m) h hh
    change actH (transLor (fun i => x i)) (ofCoords 0 h hh) =
      ofCoords ((0 : Horizontal m) + x) h hh at ht
    simpa only [zero_add] using ht
  · change (translation (fun i => x i) * GeodesicFlow.diagonal (Real.log h)) •
      (ptInfty : BoundaryH (m + 1)) = ptInfty
    rw [mul_smul, diagonal_infty, translation_infty]

theorem exists_mem_normalizing (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H) (hW : (inversion : IsometryGroup m) ∈ H)
    (ξ : BoundaryH (m + 1)) :
    ∃ a : IsometryGroup m, a ∈ H ∧ a • ξ = ptInfty := by
  by_cases hξ : ξ = ptInfty
  · exact ⟨1, H.one_mem, by simpa using hξ⟩
  obtain ⟨x, rfl⟩ := exists_horo_eq_of_ne_ptInfty ξ hξ
  let a : IsometryGroup m := translation x * inversion
  have ha : a • (ptInfty : BoundaryH (m + 1)) = horo x := by
    simp [a, mul_smul, inversion_infty]
  exact ⟨a⁻¹, H.inv_mem (H.mul_mem (hT x) hW), by rw [← ha, inv_smul_smul]⟩

theorem exists_mem_smul_standard (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hD : ∀ t : ℝ, GeodesicFlow.diagonal (m := m) t ∈ H)
    (hW : (inversion : IsometryGroup m) ∈ H) (v : Tangent m) :
    ∃ g : IsometryGroup m, g ∈ H ∧ g • (standardTangent : Tangent m) = v := by
  obtain ⟨a, ha, hξ⟩ := exists_mem_normalizing H hT hW v.2
  let p : HUpper (m + 1) := a • v.1
  let b : IsometryGroup m := translation (fun i => horizontal p i) *
    GeodesicFlow.diagonal (Real.log (height p))
  have hb : b ∈ H := H.mul_mem (hT _) (hD _)
  have hbs : b • (standardTangent : Tangent m) = a • v := by
    rw [show b = _ from rfl, affine_standard _ _ (height_pos p), ofCoords_horizontal_height]
    exact Prod.ext rfl hξ.symm
  exact ⟨a⁻¹ * b, H.mul_mem (H.inv_mem ha) hb, by rw [mul_smul, hbs, inv_smul_smul]⟩

theorem eq_top_of_transverse_and_horospherical (hm : 1 ≤ m) (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    (hD : ∀ t : ℝ, GeodesicFlow.diagonal (m := m) t ∈ H)
    (hM : transverse ≤ H) : H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro g
  obtain ⟨h, hh, he⟩ := exists_mem_smul_standard H hT hD (inversion_mem hm H hT hO hM)
    (g • (standardTangent : Tangent m))
  have hm' := hM ((same_tangent_iff g h).mp he.symm)
  simpa only [mul_inv_cancel_left] using H.mul_mem hh hm'

theorem exists_smul_standard (v : Tangent m) :
    ∃ g : IsometryGroup m, g • (standardTangent : Tangent m) = v := by
  obtain ⟨g, _, hg⟩ := exists_mem_smul_standard ⊤ (fun _ => trivial)
    (fun _ => trivial) (by trivial) v
  exact ⟨g, hg⟩

theorem frameProjection_surjective (Γ : Subgroup (IsometryGroup m)) :
    Function.Surjective (frameProjection Γ) := by
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨g, hg⟩ := exists_smul_standard v
    refine ⟨DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g, ?_⟩
    change GeodesicFlow.projection Γ (g • (standardTangent : Tangent m)) =
      GeodesicFlow.projection Γ v
    rw [hg]

theorem frameProjection_right_transverse (Γ : Subgroup (IsometryGroup m))
    {h : IsometryGroup m} (hh : h ∈ transverse)
    (q : DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ) :
    frameProjection Γ (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ h q) = frameProjection Γ q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change GeodesicFlow.projection Γ ((g * h) • (standardTangent : Tangent m)) =
      GeodesicFlow.projection Γ (g • standardTangent)
    rw [mul_smul, mem_transverse h |>.mp hh]

end DifferentialGeometry.TransverseGeneration
