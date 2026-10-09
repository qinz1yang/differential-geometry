/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Basic

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter Topology

namespace DifferentialGeometry.BusemannCocycle

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary DifferentialGeometry.HyperbolicGeometry DifferentialGeometry.AsymptoticRays
open DifferentialGeometry.Busemann
open Matrix

variable {n : ℕ}

theorem tc_pos_mul_tc_of_lorB_neg_null {u w : LorVec n} (hu : lorB u u = -1)
    (hw : lorB w w = 0) (htw : tc w ≠ 0) (h : lorB u w < 0) :
    0 < tc u * tc w := by
  have htu : tc u ≠ 0 := by
    intro h0
    have hs : lorB u u = sdot u u := by simp [lorB, h0]
    rw [hs] at hu
    have := sdot_self_nonneg u
    linarith
  have hsu : sdot u u = tc u ^ 2 - 1 := by
    have h0 := hu
    simp only [lorB] at h0
    nlinarith [h0, pow_two (tc u)]
  have hsw : sdot w w = tc w ^ 2 := by
    have h0 := hw
    simp only [lorB] at h0
    nlinarith [h0, pow_two (tc w)]
  have hcs : |sdot u w| ≤ Real.sqrt (tc u ^ 2 - 1) * |tc w| := by
    have hh := abs_sdot_le u w
    rw [hsu, hsw, Real.sqrt_sq_eq_abs] at hh
    exact hh
  have hsqrt_lt : Real.sqrt (tc u ^ 2 - 1) < |tc u| := by
    have h1 : (0:ℝ) ≤ tc u ^ 2 - 1 := by rw [← hsu]; exact sdot_self_nonneg u
    have h2 : tc u ^ 2 - 1 < |tc u| ^ 2 := by
      rw [sq_abs]
      nlinarith [mul_self_pos.mpr htu, pow_two (tc u)]
    calc Real.sqrt (tc u ^ 2 - 1) < Real.sqrt (|tc u| ^ 2) := Real.sqrt_lt_sqrt h1 h2
      _ = |tc u| := by rw [Real.sqrt_sq_eq_abs, abs_abs]
  have habs_lt : |sdot u w| < |tc u * tc w| := by
    rw [abs_mul]
    have hw' : (0:ℝ) < |tc w| := abs_pos.mpr htw
    calc |sdot u w| ≤ Real.sqrt (tc u ^ 2 - 1) * |tc w| := hcs
      _ < |tc u| * |tc w| := mul_lt_mul_of_pos_right hsqrt_lt hw'
  by_contra hcon
  have hle : tc u * tc w ≤ 0 := not_lt.mp hcon
  have habs : |tc u * tc w| = - (tc u * tc w) := abs_of_nonpos hle
  have h1 : tc u * tc w < - |sdot u w| := by rw [habs] at habs_lt; linarith
  have h2 : - |sdot u w| ≤ sdot u w := neg_abs_le _
  have h3 : tc u * tc w < sdot u w := lt_of_lt_of_le h1 h2
  have hlor : lorB u w = sdot u w - tc u * tc w := rfl
  rw [hlor] at h
  linarith

theorem neg_lorB_upperize_boundaryRep (g : LorGrp n) (x : HUpper n) (ξ : BoundaryH n) :
    - lorB (upperize (matOf g *ᵥ x.val)) (boundaryRep (matOf g *ᵥ ξ.val))
      = |tc (matOf g *ᵥ ξ.val)|⁻¹ * (- lorB x.val ξ.val) := by
  set u := matOf g *ᵥ x.val with hudef
  set w := matOf g *ᵥ ξ.val with hwdef
  have huu : lorB u u = -1 := by rw [hudef, lorB_matOf_mulVec]; exact x.is_unit
  have hww : lorB w w = 0 := by rw [hwdef, lorB_matOf_mulVec]; exact ξ.is_null
  have htw : tc w ≠ 0 := tc_matOf_mulVec_ne_zero g ξ
  have hluw : lorB u w < 0 := by
    rw [hudef, hwdef, lorB_matOf_mulVec]; exact lorB_upper_boundary_neg x ξ
  have hcoh : 0 < tc u * tc w := tc_pos_mul_tc_of_lorB_neg_null huu hww htw hluw
  have hlor : lorB u w = lorB x.val ξ.val := by
    rw [hudef, hwdef, lorB_matOf_mulVec]
  change - lorB (upperize u) (boundaryRep w) = |tc w|⁻¹ * (- lorB x.val ξ.val)
  rw [show boundaryRep w = (tc w)⁻¹ • w from rfl, lorB_smul_right]
  by_cases hu : 0 < tc u
  · rw [show upperize u = u from by unfold upperize; rw [ite_eq_left hu]]
    have htw' : 0 < tc w := by
      rcases mul_pos_iff.mp hcoh with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    rw [abs_of_pos htw', hlor]
    ring
  · rw [show upperize u = -u from by unfold upperize; rw [ite_eq_right hu]]
    have htu : tc u ≤ 0 := not_lt.mp hu
    have htw' : tc w < 0 := by
      rcases mul_pos_iff.mp hcoh with ⟨h2, _⟩ | ⟨_, h2⟩
      · linarith
      · exact h2
    rw [lorB_neg_left, abs_of_neg htw', hlor]
    rw [show (- tc w)⁻¹ = - (tc w)⁻¹ from neg_inv.symm]
    ring

theorem busemann_smul (g : LorGrp n) (ξ : BoundaryH n) (x : HUpper n) :
    busemann (g • ξ) (g • x) = busemann ξ x - Real.log |tc (matOf g *ᵥ ξ.val)| := by
  have hpair := neg_lorB_upperize_boundaryRep g x ξ
  have htw : tc (matOf g *ᵥ ξ.val) ≠ 0 := tc_matOf_mulVec_ne_zero g ξ
  have hpos : (0:ℝ) < |tc (matOf g *ᵥ ξ.val)| := abs_pos.mpr htw
  have hneg : (0:ℝ) < - lorB x.val ξ.val := neg_lorB_upper_boundary_pos x ξ
  have hgx : (g • x).val = upperize (matOf g *ᵥ x.val) := smul_val g x
  have hgξ : (g • ξ).val = boundaryRep (matOf g *ᵥ ξ.val) := rfl
  change Real.log (- lorB (g • x).val (g • ξ).val)
      = Real.log (- lorB x.val ξ.val) - Real.log |tc (matOf g *ᵥ ξ.val)|
  rw [hgx, hgξ, hpair]
  rw [Real.log_mul (inv_ne_zero (ne_of_gt hpos)) (ne_of_gt hneg)]
  rw [Real.log_inv]
  ring

noncomputable def confFactor (g : LorGrp n) (ξ : BoundaryH n) : ℝ :=
  |tc (matOf g *ᵥ ξ.val)|

theorem confFactor_pos (g : LorGrp n) (ξ : BoundaryH n) : 0 < confFactor g ξ :=
  abs_pos.mpr (tc_matOf_mulVec_ne_zero g ξ)

theorem busemann_smul_confFactor (g : LorGrp n) (ξ : BoundaryH n) (x : HUpper n) :
    busemann (g • ξ) (g • x) = busemann ξ x - Real.log (confFactor g ξ) :=
  busemann_smul g ξ x

theorem busemann_smul_sub (g : LorGrp n) (ξ : BoundaryH n) (x y : HUpper n) :
    busemann (g • ξ) (g • x) - busemann (g • ξ) (g • y)
      = busemann ξ x - busemann ξ y := by
  rw [busemann_smul g ξ x, busemann_smul g ξ y]
  ring

theorem confFactor_mul (g h : LorGrp n) (ξ : BoundaryH n) :
    confFactor (g * h) ξ = confFactor h ξ * confFactor g (h • ξ) := by
  have hξ : (h • ξ).val = (tc (matOf h *ᵥ ξ.val))⁻¹ • (matOf h *ᵥ ξ.val) := rfl
  have hw' : matOf h *ᵥ ξ.val = tc (matOf h *ᵥ ξ.val) • (h • ξ).val := by
    rw [hξ, smul_smul, mul_inv_cancel₀ (tc_matOf_mulVec_ne_zero h ξ), one_smul]
  have veckey : matOf (g * h) *ᵥ ξ.val
      = tc (matOf h *ᵥ ξ.val) • (matOf g *ᵥ (h • ξ).val) := by
    calc matOf (g * h) *ᵥ ξ.val
        = matOf g *ᵥ (matOf h *ᵥ ξ.val) := by rw [matOf_mul, ← Matrix.mulVec_mulVec]
      _ = matOf g *ᵥ (tc (matOf h *ᵥ ξ.val) • (h • ξ).val) := congrArg (matOf g *ᵥ ·) hw'
      _ = tc (matOf h *ᵥ ξ.val) • (matOf g *ᵥ (h • ξ).val) := Matrix.mulVec_smul _ _ _
  change |tc (matOf (g * h) *ᵥ ξ.val)| = |tc (matOf h *ᵥ ξ.val)| * |tc (matOf g *ᵥ (h • ξ).val)|
  rw [veckey, tc_smul, abs_mul]

theorem busemann_smul_of_eigen (g : LorGrp n) (ξ : BoundaryH n) (c : ℝ)
    (heig : matOf g *ᵥ ξ.val = c • ξ.val) (x : HUpper n) :
    busemann ξ (g • x) = busemann ξ x - Real.log |c| := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 : matOf g *ᵥ ξ.val = 0 := by rw [heig, zero_smul]
    have hne := tc_matOf_mulVec_ne_zero g ξ
    rw [h0] at hne
    exact hne rfl
  have hfix : g • ξ = ξ := by
    apply BoundaryH.ext
    change boundaryRep (matOf g *ᵥ ξ.val) = ξ.val
    rw [heig]
    change (tc (c • ξ.val))⁻¹ • (c • ξ.val) = ξ.val
    rw [tc_smul, ξ.tc_eq, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have htc : tc (matOf g *ᵥ ξ.val) = c := by rw [heig, tc_smul, ξ.tc_eq, mul_one]
  have h := busemann_smul g ξ x
  rw [hfix, htc] at h
  exact h

theorem busemann_smul_of_fix_one (g : LorGrp n) (ξ : BoundaryH n)
    (hfix : matOf g *ᵥ ξ.val = ξ.val) (x : HUpper n) :
    busemann ξ (g • x) = busemann ξ x := by
  have h := busemann_smul_of_eigen g ξ 1 (by rw [one_smul]; exact hfix) x
  rw [abs_one, Real.log_one, sub_zero] at h
  exact h

theorem busemann_smul_lt_of_eigen_one_lt (g : LorGrp n) (ξ : BoundaryH n) (c : ℝ)
    (hc : 1 < |c|) (heig : matOf g *ᵥ ξ.val = c • ξ.val) (x : HUpper n) :
    busemann ξ (g • x) < busemann ξ x := by
  rw [busemann_smul_of_eigen g ξ c heig x]
  have h : 0 < Real.log |c| := Real.log_pos hc
  linarith

theorem busemann_smul_gt_of_eigen_lt_one (g : LorGrp n) (ξ : BoundaryH n) (c : ℝ)
    (hc0 : c ≠ 0) (hc : |c| < 1) (heig : matOf g *ᵥ ξ.val = c • ξ.val) (x : HUpper n) :
    busemann ξ x < busemann ξ (g • x) := by
  rw [busemann_smul_of_eigen g ξ c heig x]
  have h : Real.log |c| < 0 := Real.log_neg (abs_pos.mpr hc0) hc
  linarith

theorem smul_mem_horoball_of_eigen (g : LorGrp n) (ξ : BoundaryH n) (c : ℝ)
    (heig : matOf g *ᵥ ξ.val = c • ξ.val) (c₀ : ℝ) {x : HUpper n} :
    g • x ∈ horoball ξ c₀ ↔ x ∈ horoball ξ (c₀ + Real.log |c|) := by
  have h := busemann_smul_of_eigen g ξ c heig x
  change busemann ξ (g • x) ≤ c₀ ↔ busemann ξ x ≤ c₀ + Real.log |c|
  rw [h]
  constructor <;> intro h' <;> linarith

theorem confFactor_center_left (hn : 1 ≤ n) (z g : LorGrp n)
    (hz : z ∈ Subgroup.center (LorGrp n)) (ξ : BoundaryH n) :
    confFactor (z * g) ξ = confFactor g ξ := by
  change |tc (matOf (z * g) *ᵥ ξ.val)| = |tc (matOf g *ᵥ ξ.val)|
  rw [matOf_mul, ← Matrix.mulVec_mulVec]
  rcases DifferentialGeometry.ProjectiveOrthogonalGroup.Center.center_coe_eq hn hz with h1 | h1
  · have hm : matOf z = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := h1
    rw [hm, Matrix.one_mulVec]
  · have hm : matOf z = (-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := h1
    rw [hm]
    have hneg : ((-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ (matOf g *ᵥ ξ.val))
        = - (matOf g *ᵥ ξ.val) := by
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [hneg, tc_neg, abs_neg]

theorem confFactor_center_right (hn : 1 ≤ n) (g z : LorGrp n)
    (hz : z ∈ Subgroup.center (LorGrp n)) (ξ : BoundaryH n) :
    confFactor (g * z) ξ = confFactor g ξ := by
  have hcomm : g * z = z * g := Subgroup.mem_center_iff.mp hz g
  rw [hcomm]
  exact confFactor_center_left hn z g hz ξ

noncomputable def poConfFactor (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n) : ℝ :=
  Quotient.lift (fun A : LorGrp n => confFactor A ξ) (fun A B hAB => by
    have hmem : A⁻¹ * B ∈ Subgroup.center (LorGrp n) := QuotientGroup.leftRel_apply.mp hAB
    have hB : B = A * (A⁻¹ * B) := by group
    rw [hB, confFactor_center_right hn A (A⁻¹ * B) hmem ξ]) g

theorem poConfFactor_mk (hn : 1 ≤ n) (A : LorGrp n) (ξ : BoundaryH n) :
    poConfFactor hn (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A)
      ξ = confFactor A ξ := rfl

theorem poConfFactor_pos (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n) :
    0 < poConfFactor hn g ξ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [poConfFactor_mk]
  exact confFactor_pos A ξ

theorem poConfFactor_mul (hn : 1 ≤ n) (g h : PO n 1) (ξ : BoundaryH n) :
    letI := poBoundaryMulAction hn
    poConfFactor hn (g * h) ξ = poConfFactor hn h ξ * poConfFactor hn g (h • ξ) := by
  let := poBoundaryMulAction hn
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective _ h
  rw [← map_mul (QuotientGroup.mk' _) A B]
  rw [poConfFactor_mk, poConfFactor_mk, poConfFactor_mk]
  rw [po_boundary_smul_mk hn B ξ]
  exact confFactor_mul A B ξ

theorem po_busemann_smul (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n) (x : HUpper n) :
    busemann ((poBoundaryMulAction hn).smul g ξ) ((poMulAction hn).smul g x)
      = busemann ξ x - Real.log (poConfFactor hn g ξ) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  exact busemann_smul_confFactor A ξ x

theorem po_smul_mem_horoball_iff (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (c : ℝ) (x : HUpper n) :
    (poMulAction hn).smul g x ∈
        horoball ((poBoundaryMulAction hn).smul g ξ) (c - Real.log (poConfFactor hn g ξ))
      ↔ x ∈ horoball ξ c := by
  change busemann ((poBoundaryMulAction hn).smul g ξ) ((poMulAction hn).smul g x)
      ≤ c - Real.log (poConfFactor hn g ξ) ↔ busemann ξ x ≤ c
  rw [po_busemann_smul]
  exact sub_le_sub_iff_right _

end DifferentialGeometry.BusemannCocycle
