/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.AsymptoticRays

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.BoundaryExtension

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary DifferentialGeometry.BoundaryTopology
open DifferentialGeometry.AsymptoticRays DifferentialGeometry.GromovBoundary
open Matrix

variable {n : ℕ}

theorem dirTo_actH_actB_of_tc_pos (A : LorGrp n) (o : HUpper n) (ξ : BoundaryH n)
    (hA : 0 < tc (matOf A *ᵥ o.val)) :
    dirTo (A • o) (A • ξ) = matOf A *ᵥ dirTo o ξ := by
  have hv1 : (A • o).val = matOf A *ᵥ o.val := by
    change upperize (matOf A *ᵥ o.val) = matOf A *ᵥ o.val
    exact ite_eq_left hA
  have hv2 : (A • ξ).val = (tc (matOf A *ᵥ ξ.val))⁻¹ • (matOf A *ᵥ ξ.val) := rfl
  have htcV : tc (matOf A *ᵥ ξ.val) ≠ 0 := tc_matOf_mulVec_ne_zero A ξ
  have hL0 : lorB o.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o ξ).ne
  have hL' : lorB (A • o).val (A • ξ).val
      = (tc (matOf A *ᵥ ξ.val))⁻¹ * lorB o.val ξ.val := by
    rw [hv1, hv2, lorB_smul_right, lorB_matOf_mulVec]
  have hW : matOf A *ᵥ dirTo o ξ
      = (- lorB o.val ξ.val)⁻¹
        • (matOf A *ᵥ ξ.val + lorB o.val ξ.val • (matOf A *ᵥ o.val)) := by
    change matOf A *ᵥ ((- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hW]
  rw [show dirTo (A • o) (A • ξ)
      = (- lorB (A • o).val (A • ξ).val)⁻¹
        • ((A • ξ).val + lorB (A • o).val (A • ξ).val • (A • o).val) from rfl]
  rw [hL', hv1, hv2]
  have hinner : (tc (matOf A *ᵥ ξ.val))⁻¹ • (matOf A *ᵥ ξ.val)
      + ((tc (matOf A *ᵥ ξ.val))⁻¹ * lorB o.val ξ.val) • (matOf A *ᵥ o.val)
      = (tc (matOf A *ᵥ ξ.val))⁻¹
        • (matOf A *ᵥ ξ.val + lorB o.val ξ.val • (matOf A *ᵥ o.val)) := by
    rw [smul_add, (smul_smul _ _ _).symm]
  rw [hinner, smul_smul]
  have hsc : (-((tc (matOf A *ᵥ ξ.val))⁻¹ * lorB o.val ξ.val))⁻¹ * (tc (matOf A *ᵥ ξ.val))⁻¹
      = (- lorB o.val ξ.val)⁻¹ := by
    field_simp [hL0, htcV, inv_ne_zero htcV]
  rw [hsc]

theorem actH_rayTo_of_tc_pos (A : LorGrp n) (o : HUpper n) (ξ : BoundaryH n) (t : ℝ)
    (hA : 0 < tc (matOf A *ᵥ o.val)) :
    A • rayTo o ξ t = rayTo (A • o) (A • ξ) t := by
  apply HUpper.ext
  have hlor : lorB (matOf A *ᵥ o.val) (matOf A *ᵥ (rayTo o ξ t).val) = - Real.cosh t := by
    rw [lorB_matOf_mulVec]
    change lorB o.val (Real.cosh t • o.val + Real.sinh t • dirTo o ξ) = _
    rw [lorB_add_right, lorB_smul_right, lorB_smul_right, o.is_unit,
      lorB_comm o.val (dirTo o ξ), lorB_dirTo_left o ξ]
    ring
  have hUU : lorB (matOf A *ᵥ o.val) (matOf A *ᵥ o.val) = -1 := by
    rw [lorB_matOf_mulVec]; exact o.is_unit
  have hXX : lorB (matOf A *ᵥ (rayTo o ξ t).val) (matOf A *ᵥ (rayTo o ξ t).val) = -1 := by
    rw [lorB_matOf_mulVec]; exact (rayTo o ξ t).is_unit
  have hneg : lorB (matOf A *ᵥ o.val) (matOf A *ᵥ (rayTo o ξ t).val) < 0 := by
    rw [hlor]
    exact neg_lt_zero.mpr (Real.cosh_pos t)
  have hX : 0 < tc (matOf A *ᵥ (rayTo o ξ t).val) :=
    (tc_pos_iff_tc_pos_of_lorB_neg hUU hXX hneg).mp hA
  change upperize (matOf A *ᵥ (rayTo o ξ t).val)
    = Real.cosh t • (A • o).val + Real.sinh t • dirTo (A • o) (A • ξ)
  rw [show upperize (matOf A *ᵥ (rayTo o ξ t).val) = matOf A *ᵥ (rayTo o ξ t).val from
    ite_eq_left hX]
  rw [show matOf A *ᵥ (rayTo o ξ t).val
      = Real.cosh t • (matOf A *ᵥ o.val) + Real.sinh t • (matOf A *ᵥ dirTo o ξ) from by
    change matOf A *ᵥ (Real.cosh t • o.val + Real.sinh t • dirTo o ξ) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]]
  rw [show (A • o).val = matOf A *ᵥ o.val from ite_eq_left hA,
    dirTo_actH_actB_of_tc_pos A o ξ hA]

theorem mk'_neg_eq_mk' (A : LorGrp n) :
    (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) (-A)
      : PO n 1)
      = QuotientGroup.mk' _ A := by
  rw [QuotientGroup.mk'_eq_mk']
  have hc : (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n) ∈
      Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)) :=
    DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_center (n := n)
  have hA0 : (-A : LorGrp n)
      = (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n) * A := by
    apply Subtype.ext
    rw [Unitary.coe_neg, Submonoid.coe_mul]
    change -(A.val : MatrixSum (Fin n) (Fin 1) ℝ)
      = (-1 : MatrixSum (Fin n) (Fin 1) ℝ) * A.val
    rw [neg_one_mul]
  refine ⟨(⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)⁻¹, Subgroup.inv_mem _ hc, ?_⟩
  rw [hA0]
  have hc2 := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) A
  calc ((⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n) * A)
        * (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)⁻¹
      = (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)
        * (A * (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)⁻¹) := mul_assoc _ _ _
    _ = (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)
        * ((⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)⁻¹ * A) := by rw [hc2]
    _ = ((⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)
        * (⟨-1, DifferentialGeometry.ProjectiveOrthogonalGroup.Center.neg_one_mem_unitary⟩ : LorGrp n)⁻¹) * A := (mul_assoc _ _ _).symm
    _ = A := by rw [mul_inv_cancel, one_mul]

theorem po_smul_rayTo (hn : 1 ≤ n) (g : PO n 1) (o : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    letI := poMulAction hn
    letI := poBoundaryMulAction hn
    g • rayTo o ξ t = rayTo (g • o) (g • ξ) t := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  obtain ⟨A₀, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) g
  have hne : tc (matOf A₀ *ᵥ o.val) ≠ 0 := matOf_mulVec_ne_tc A₀ o.is_unit
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [← mk'_neg_eq_mk' A₀]
    have hpos2 : 0 < tc (matOf (-A₀) *ᵥ o.val) := by
      have hmat : matOf (-A₀) *ᵥ o.val = - (matOf A₀ *ᵥ o.val) := by
        have hmat0 : matOf (-A₀ : LorGrp n) = - matOf A₀ := by
          change MatrixSum.ofMatrix.symm (-A₀ : LorGrp n).val
            = - MatrixSum.ofMatrix.symm (A₀ : LorGrp n).val
          rw [Unitary.coe_neg]
          exact map_neg _ _
        rw [hmat0, Matrix.neg_mulVec]
      rw [hmat, tc_neg]
      linarith [hneg]
    rw [po_smul_mk hn (-A₀), po_smul_mk hn (-A₀), po_boundary_smul_mk hn (-A₀)]
    exact actH_rayTo_of_tc_pos (-A₀) o ξ t hpos2
  · rw [po_smul_mk hn A₀, po_smul_mk hn A₀, po_boundary_smul_mk hn A₀]
    exact actH_rayTo_of_tc_pos A₀ o ξ t hpos

noncomputable def bExt {Φ : HUpper n → HUpper n}
    (hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))))
    (ξ : BoundaryH n) : BoundaryH n :=
  (exists_convergesToBoundary (hGC basepointH ξ)).choose

theorem bExt_spec {Φ : HUpper n → HUpper n}
    (hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))))
    (ξ : BoundaryH n) :
    ConvergesToBoundary (fun m : ℕ => Φ (rayTo basepointH ξ (m : ℝ))) (bExt hGC ξ) :=
  (exists_convergesToBoundary (hGC basepointH ξ)).choose_spec

theorem bExt_spec_rayTo {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ)
    (hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))))
    (o : HUpper n) (ξ : BoundaryH n) :
    ConvergesToBoundary (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))) (bExt hGC ξ) := by
  apply ConvergesToBoundary.of_bounded_dist
    (B := K * Real.arcosh (max (- lorB basepointH.val o.val)
      ((lorB basepointH.val ξ.val / lorB o.val ξ.val
        + lorB o.val ξ.val / lorB basepointH.val ξ.val) / 2)) + C)
    (bExt_spec hGC ξ) _ ((hGC o ξ).of_basepoint basepointH).1
  intro m
  calc dist (Φ (rayTo basepointH ξ (m:ℝ))) (Φ (rayTo o ξ (m:ℝ)))
      ≤ K * dist (rayTo basepointH ξ (m:ℝ)) (rayTo o ξ (m:ℝ)) + C := hΦ.upper _ _
    _ ≤ K * Real.arcosh (max (- lorB basepointH.val o.val)
        ((lorB basepointH.val ξ.val / lorB o.val ξ.val
          + lorB o.val ξ.val / lorB basepointH.val ξ.val) / 2)) + C := by
        have h := dist_rayTo_rayTo_le basepointH o ξ (Nat.cast_nonneg m)
        have h2 := mul_le_mul_of_nonneg_left h (zero_le_one.trans hΦ.hK)
        linarith [h2]

theorem bExt_equivariant {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {K C : ℝ}
    {Φ : HUpper n → HUpper n} (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ)
    (hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))))
    (hn : 1 ≤ n) (hf : PseudoIsometry.IsFEquivariant f hn Φ) (γ : Γ) (ξ : BoundaryH n) :
    bExt hGC ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ)
      = (poBoundaryMulAction hn).smul ((f γ : Λ) : PO n 1) (bExt hGC ξ) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  have hf' : ∀ (γ : Γ) (x : HUpper n), Φ ((γ : PO n 1) • x) = (f γ : PO n 1) • Φ x :=
    fun γ x => hf γ x
  have h1 : ConvergesToBoundary (fun m : ℕ => Φ ((γ : PO n 1) • rayTo basepointH ξ (m:ℝ)))
      (bExt hGC ((γ : PO n 1) • ξ)) := by
    have heq : (fun m : ℕ => Φ ((γ : PO n 1) • rayTo basepointH ξ (m:ℝ)))
        = (fun m : ℕ => Φ (rayTo ((γ : PO n 1) • basepointH) ((γ : PO n 1) • ξ) (m:ℝ))) :=
      funext fun m => by rw [po_smul_rayTo hn]
    rw [heq]
    exact bExt_spec_rayTo hΦ hGC ((γ : PO n 1) • basepointH) ((γ : PO n 1) • ξ)
  have h2 : ConvergesToBoundary (fun m : ℕ => Φ ((γ : PO n 1) • rayTo basepointH ξ (m:ℝ)))
      ((f γ : PO n 1) • (bExt hGC ξ)) := by
    have heq : (fun m : ℕ => Φ ((γ : PO n 1) • rayTo basepointH ξ (m:ℝ)))
        = (fun m : ℕ => (f γ : PO n 1) • Φ (rayTo basepointH ξ (m:ℝ))) :=
      funext fun m => hf' γ _
    rw [heq]
    exact convergesToBoundary_smul hn (f γ : PO n 1) (bExt_spec hGC ξ)
  exact convergesToBoundary_unique h1 h2

end DifferentialGeometry.BoundaryExtension
