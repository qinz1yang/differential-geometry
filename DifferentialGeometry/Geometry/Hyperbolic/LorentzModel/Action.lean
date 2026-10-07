/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Defs
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Center

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicAction

open DifferentialGeometry.Hyperbolic
open Matrix

variable {n : ℕ}

abbrev LorGrp (n : ℕ) := unitary (MatrixSum (Fin n) (Fin 1) ℝ)

def matOf (g : LorGrp n) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  MatrixSum.ofMatrix.symm g.val

theorem lorB_eq_dotProduct (x y : LorVec n) :
    lorB x y = x ⬝ᵥ ((pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ y) := by
  rw [DifferentialGeometry.ProjectiveOrthogonalGroup.Center.pmOneMat_eq_diagonal]
  change lorB x y = ∑ a : Fin n ⊕ Fin 1, x a * (Matrix.diagonal _ *ᵥ y) a
  rw [Fintype.sum_sum_type]
  simp only [Matrix.mulVec_diagonal, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_one]
  simp only [lorB, sdot, tc, one_mul, neg_one_mul]
  ring

theorem transpose_matOf_mul_pmOneMat (g : LorGrp n) :
    (matOf g)ᵀ * pmOneMat * matOf g
      = (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
  have hu : star g.val * g.val = (1 : MatrixSum (Fin n) (Fin 1) ℝ) :=
    (Unitary.mem_iff.mp g.prop).1
  have hu2 : ((pmOneMat * (matOf g)ᴴ * pmOneMat) * matOf g
      : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) = 1 := hu
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hu2
  have hpm : (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) * pmOneMat = 1 :=
    pmOneMat_mul_pmOneMat (Fin n) (Fin 1) ℝ
  have h1 : pmOneMat * (pmOneMat * (matOf g)ᵀ * pmOneMat * matOf g) = pmOneMat * 1 :=
    congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ => pmOneMat * M) hu2
  rw [Matrix.mul_one] at h1
  have h2 : pmOneMat * (pmOneMat * (matOf g)ᵀ * pmOneMat * matOf g)
      = (pmOneMat * pmOneMat) * ((matOf g)ᵀ * pmOneMat * matOf g) := by
    simp only [Matrix.mul_assoc]
  rw [h2, hpm, Matrix.one_mul] at h1
  exact h1

theorem dotProduct_mulVec_mulVec (A N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (x y : LorVec n) :
    (A *ᵥ x) ⬝ᵥ (N *ᵥ y) = x ⬝ᵥ ((Aᵀ * N) *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec]

theorem lorB_matOf_mulVec (g : LorGrp n) (x y : LorVec n) :
    lorB (matOf g *ᵥ x) (matOf g *ᵥ y) = lorB x y := by
  rw [lorB_eq_dotProduct, lorB_eq_dotProduct, Matrix.mulVec_mulVec, dotProduct_mulVec_mulVec,
    ← Matrix.mul_assoc, transpose_matOf_mul_pmOneMat]

noncomputable def upperize (v : LorVec n) : LorVec n := if 0 < tc v then v else -v

theorem lorB_upperize_upperize (v : LorVec n) : lorB (upperize v) (upperize v) = lorB v v := by
  unfold upperize
  split_ifs with h
  · rfl
  · rw [lorB_neg_left, lorB_neg_right, neg_neg]

theorem tc_upperize_nonneg (v : LorVec n) : 0 ≤ tc (upperize v) := by
  unfold upperize
  split_ifs with h
  · exact le_of_lt h
  · rw [tc_neg]
    linarith [not_lt.mp h]

theorem tc_upperize (v : LorVec n) : tc (upperize v) = |tc v| := by
  unfold upperize
  split_ifs with h
  · rw [abs_of_pos h]
  · rw [tc_neg, abs_of_nonpos (not_lt.mp h)]

theorem upperize_neg {w : LorVec n} (hw : tc w ≠ 0) : upperize (-w) = upperize w := by
  unfold upperize
  rw [tc_neg]
  by_cases h : 0 < tc w
  · rw [ite_eq_left h, ite_eq_right (by linarith : ¬ 0 < -tc w), neg_neg]
  · have h' : tc w < 0 := lt_of_le_of_ne (not_lt.mp h) hw
    rw [ite_eq_right h, ite_eq_left (by linarith : 0 < -tc w)]

theorem lorB_pos_of_tc_pos_of_tc_neg {u v : LorVec n} (hu : lorB u u = -1) (hv : lorB v v = -1)
    (htu : 0 < tc u) (htv : tc v < 0) : 0 < lorB u v := by
  have hsu : sdot u u = tc u * tc u - 1 := by
    have h0 := hu; simp only [lorB] at h0; linarith
  have hsv : sdot v v = tc v * tc v - 1 := by
    have h0 := hv; simp only [lorB] at h0; linarith
  have hsu0 : 0 ≤ sdot u u := sdot_self_nonneg u
  have hsv0 : 0 ≤ sdot v v := sdot_self_nonneg v
  have habs : |sdot u v| ≤ Real.sqrt (sdot u u * sdot v v) := by
    have h := abs_sdot_le u v
    rw [← Real.sqrt_mul hsu0] at h
    exact h
  have hsdot : - Real.sqrt (sdot u u * sdot v v) ≤ sdot u v := by
    have hnn := neg_abs_le (sdot u v); linarith [hnn, habs]
  have htvabs : |tc v| = - tc v := abs_of_neg htv
  have hprod : tc u * |tc v| = Real.sqrt ((1 + sdot u u) * (1 + sdot v v)) := by
    have hpos : 0 ≤ tc u * |tc v| := by positivity
    have e1 : tc u ^ 2 = 1 + sdot u u := by rw [pow_two]; linarith [hsu]
    have e2 : tc v ^ 2 = 1 + sdot v v := by rw [pow_two]; linarith [hsv]
    have hsq : (tc u * |tc v|)^2 = (1 + sdot u u)*(1 + sdot v v) := by
      rw [mul_pow, sq_abs, e1, e2]
    rw [← hsq]; exact (Real.sqrt_sq hpos).symm
  have hgt : Real.sqrt (sdot u u * sdot v v) < tc u * |tc v| := by
    rw [hprod]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hsu0, hsv0]
  have htc : tc u * tc v = - (tc u * |tc v|) := by rw [htvabs]; ring
  have heq : lorB u v = sdot u v + tc u * |tc v| := by
    simp only [lorB]; rw [htc]; ring
  rw [heq]
  linarith [hsdot, hgt]

theorem tc_pos_iff_tc_pos_of_lorB_neg {u v : LorVec n} (hu : lorB u u = -1) (hv : lorB v v = -1)
    (h : lorB u v < 0) : 0 < tc u ↔ 0 < tc v := by
  have htu0 : tc u ≠ 0 := by
    intro htc
    have h0 := hu
    simp only [lorB, htc, mul_zero, sub_zero] at h0
    have := sdot_self_nonneg u
    linarith
  have htv0 : tc v ≠ 0 := by
    intro htc
    have h0 := hv
    simp only [lorB, htc, mul_zero, sub_zero] at h0
    have := sdot_self_nonneg v
    linarith
  constructor
  · intro htu
    by_contra hcv
    have htv : tc v < 0 := lt_of_le_of_ne (not_lt.mp hcv) htv0
    have := lorB_pos_of_tc_pos_of_tc_neg hu hv htu htv
    linarith [h, this]
  · intro htv
    by_contra hcu
    have htu : tc u < 0 := lt_of_le_of_ne (not_lt.mp hcu) htu0
    have h' : lorB v u < 0 := by rw [lorB_comm]; exact h
    have := lorB_pos_of_tc_pos_of_tc_neg hv hu htv htu
    linarith [h', this]

theorem lorB_upperize_upperize_of_neg {u v : LorVec n} (hu : lorB u u = -1) (hv : lorB v v = -1)
    (h : lorB u v < 0) : lorB (upperize u) (upperize v) = lorB u v := by
  have hsame := tc_pos_iff_tc_pos_of_lorB_neg hu hv h
  unfold upperize
  by_cases hu' : 0 < tc u
  · have hv' : 0 < tc v := hsame.mp hu'
    rw [ite_eq_left hu', ite_eq_left hv']
  · have hv' : ¬ 0 < tc v := fun hc => hu' (hsame.mpr hc)
    rw [ite_eq_right hu', ite_eq_right hv', lorB_neg_left, lorB_neg_right, neg_neg]

noncomputable def actH (g : LorGrp n) (x : HUpper n) : HUpper n :=
  { val := upperize (matOf g *ᵥ x.val)
    is_unit := by
      rw [lorB_upperize_upperize, lorB_matOf_mulVec]; exact x.is_unit
    future := by
      have h1 : lorB (matOf g *ᵥ x.val) (matOf g *ᵥ x.val) = -1 := by
        rw [lorB_matOf_mulVec]; exact x.is_unit
      have hne : tc (matOf g *ᵥ x.val) ≠ 0 := by
        intro htc
        have h0 := h1
        simp only [lorB, htc, mul_zero, sub_zero] at h0
        have hs := sdot_self_nonneg (matOf g *ᵥ x.val)
        linarith
      rw [tc_upperize]
      exact abs_pos.mpr hne }

theorem matOf_one : matOf (1 : LorGrp n) = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := rfl

theorem matOf_mul (g h : LorGrp n) : matOf (g * h) = matOf g * matOf h := rfl

theorem matOf_mulVec_ne_tc (g : LorGrp n) {v : LorVec n} (hv : lorB v v = -1) :
    tc (matOf g *ᵥ v) ≠ 0 := by
  intro htc
  have h1 : lorB (matOf g *ᵥ v) (matOf g *ᵥ v) = -1 := by rw [lorB_matOf_mulVec]; exact hv
  simp only [lorB, htc, mul_zero, sub_zero] at h1
  have hs := sdot_self_nonneg (matOf g *ᵥ v)
  linarith

noncomputable instance : MulAction (LorGrp n) (HUpper n) where
  smul g x := actH g x
  one_smul x := by
    apply HUpper.ext
    change upperize (matOf (1 : LorGrp n) *ᵥ x.val) = x.val
    rw [matOf_one, Matrix.one_mulVec]
    unfold upperize
    rw [ite_eq_left x.future]
  mul_smul g h x := by
    apply HUpper.ext
    change upperize (matOf (g * h) *ᵥ x.val) = upperize (matOf g *ᵥ (actH h x).val)
    rw [matOf_mul, ← Matrix.mulVec_mulVec]
    change upperize (matOf g *ᵥ (matOf h *ᵥ x.val)) = upperize (matOf g *ᵥ upperize (matOf h *ᵥ x.val))
    by_cases hcase : 0 < tc (matOf h *ᵥ x.val)
    · rw [show upperize (matOf h *ᵥ x.val) = matOf h *ᵥ x.val from by
        unfold upperize; rw [ite_eq_left hcase]]
    · rw [show upperize (matOf h *ᵥ x.val) = - (matOf h *ᵥ x.val) from by
        unfold upperize; rw [ite_eq_right hcase]]
      rw [← neg_one_smul ℝ (matOf h *ᵥ x.val), Matrix.mulVec_smul, neg_one_smul]
      rw [upperize_neg (matOf_mulVec_ne_tc g (by rw [lorB_matOf_mulVec]; exact x.is_unit))]

theorem smul_val (g : LorGrp n) (x : HUpper n) :
    (g • x).val = upperize (matOf g *ᵥ x.val) := rfl

theorem dist_smul (g : LorGrp n) (x y : HUpper n) :
    dist (g • x) (g • y) = dist x y := by
  have hu : lorB (matOf g *ᵥ x.val) (matOf g *ᵥ x.val) = -1 := by
    rw [lorB_matOf_mulVec]; exact x.is_unit
  have hv : lorB (matOf g *ᵥ y.val) (matOf g *ᵥ y.val) = -1 := by
    rw [lorB_matOf_mulVec]; exact y.is_unit
  have hneg : lorB (matOf g *ᵥ x.val) (matOf g *ᵥ y.val) < 0 := by
    rw [lorB_matOf_mulVec]
    have h1 := HUpper.one_le_neg_lorB x y
    linarith
  change HUpper.hdist (g • x) (g • y) = HUpper.hdist x y
  unfold HUpper.hdist
  rw [smul_val, smul_val, lorB_upperize_upperize_of_neg hu hv hneg, lorB_matOf_mulVec]

theorem smul_eq_self_of_mem_center (hn : 1 ≤ n) (z : LorGrp n)
    (hz : z ∈ Subgroup.center (LorGrp n)) (x : HUpper n) : z • x = x := by
  rcases DifferentialGeometry.ProjectiveOrthogonalGroup.Center.center_coe_eq hn hz with h1 | h1
  · have hz1 : z = 1 := by
      apply Subtype.ext
      exact h1
    rw [hz1]
    exact one_smul _ x
  · apply HUpper.ext
    change upperize (matOf z *ᵥ x.val) = x.val
    have hm : matOf z = (-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := h1
    have hmx : matOf z *ᵥ x.val = -x.val := by
      rw [hm]
      calc ((-1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) *ᵥ x.val)
          = -(1 *ᵥ x.val) := Matrix.neg_mulVec _ _
        _ = -x.val := by rw [Matrix.one_mulVec]
    rw [hmx]
    have hne : tc x.val ≠ 0 := ne_of_gt x.future
    rw [upperize_neg hne]
    unfold upperize
    rw [ite_eq_left x.future]

noncomputable def poPermHom (hn : 1 ≤ n) : PO n 1 →* Equiv.Perm (HUpper n) :=
  QuotientGroup.lift (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)))
    (MulAction.toPermHom ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ)) (HUpper n)) (by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hact : ∀ x : HUpper n, z • x = x := fun x => smul_eq_self_of_mem_center hn z hz x
    apply Equiv.Perm.ext
    intro x
    exact hact x)

@[instance_reducible]
noncomputable def poMulAction (hn : 1 ≤ n) : MulAction (PO n 1) (HUpper n) where
  smul g x := poPermHom hn g x
  one_smul x := by
    change poPermHom hn 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change poPermHom hn (g * h) x = poPermHom hn g (poPermHom hn h x)
    rw [map_mul]
    rfl

theorem po_smul_mk (hn : 1 ≤ n) (A : LorGrp n) (x : HUpper n) :
    letI := poMulAction hn
    (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A : PO n 1) • x
      = A • x := by
  let := poMulAction hn
  change poPermHom hn (QuotientGroup.mk' _ A) x = A • x
  rfl

theorem po_dist_smul (hn : 1 ≤ n) (g : PO n 1) (x y : HUpper n) :
    letI := poMulAction hn
    dist (g • x) (g • y) = dist x y := by
  let := poMulAction hn
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (LorGrp n)) g
  rw [po_smul_mk hn, po_smul_mk hn]
  exact dist_smul A x y

end HyperbolicAction

end DifferentialGeometry
