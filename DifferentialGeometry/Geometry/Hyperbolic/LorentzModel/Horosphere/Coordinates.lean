/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Extension
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.MobiusTransformations
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Cocycle
import Mathlib.Analysis.Normed.Affine.MazurUlam

noncomputable section

open DifferentialGeometry.ProjectiveOrthogonalGroup Matrix

namespace DifferentialGeometry.Horospherical

open Hyperbolic HyperbolicAction HyperbolicBoundary MobiusBoundary Busemann

variable {m : ℕ}

abbrev Horizontal (m : ℕ) := EuclideanSpace ℝ (Fin m)

def vHeight (v : LorVec (m + 1)) : ℝ := tc v - v (Sum.inl (Fin.last m))

theorem vHeight_add (v w : LorVec (m + 1)) :
    vHeight (v + w) = vHeight v + vHeight w := by
  simp only [vHeight, tc_add, Pi.add_apply]
  ring

theorem vHeight_smul (c : ℝ) (v : LorVec (m + 1)) :
    vHeight (c • v) = c * vHeight v := by
  simp only [vHeight, tc_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem lorB_ptInfty (v : LorVec (m + 1)) :
    lorB v ptInfty.val = -vHeight v := by
  rw [lorB, sdot, Fin.sum_univ_castSucc]
  simp only [ptInfty_val_castSucc, ptInfty_val_last, mul_zero,
    Finset.sum_const_zero, zero_add, mul_one, ptInfty.tc_eq]
  unfold vHeight
  ring

theorem lorB_ptInfty_left (v : LorVec (m + 1)) :
    lorB ptInfty.val v = -vHeight v := by
  rw [lorB_comm, lorB_ptInfty]

theorem vHeight_ptInfty : vHeight (ptInfty : BoundaryH (m + 1)).val = 0 := by
  simp [vHeight, ptInfty.tc_eq, ptInfty_val_last]

theorem vHeight_horoVec (x : Fin m → ℝ) : vHeight (horoVec x) = 1 := by
  rw [vHeight, tc_horoVec, horoVec_last]
  ring

theorem horizOf_ptInfty : horizOf (ptInfty : BoundaryH (m + 1)).val = 0 := by
  ext i
  exact ptInfty_val_castSucc i

theorem normSq_horizontal (x : Horizontal m) :
    normSq (fun i => x i) = ‖x‖ ^ 2 :=
  x.real_norm_sq_eq.symm

theorem normSq_sub (x y : Fin m → ℝ) :
    normSq (x - y) = normSq x + normSq y - 2 * dotB x y := by
  have h : ∀ i, (x i - y i) ^ 2 = x i ^ 2 + y i ^ 2 - 2 * (x i * y i) :=
    fun i => by ring
  simp only [normSq, Pi.sub_apply, h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, dotB]

theorem lorB_horoVec_horoVec (x y : Fin m → ℝ) :
    lorB (horoVec x) (horoVec y) = -normSq (x - y) / 2 := by
  rw [lorB, sdot, Fin.sum_univ_castSucc]
  simp only [horoVec_castSucc, horoVec_last, tc_horoVec]
  rw [normSq_sub]
  unfold dotB
  ring

def ofCoordsVec (x : Horizontal m) (h : ℝ) : LorVec (m + 1) :=
  h⁻¹ • horoVec (fun i => x i) + (h / 2) • ptInfty.val

theorem horizOf_ofCoordsVec (x : Horizontal m) (h : ℝ) :
    horizOf (ofCoordsVec x h) = h⁻¹ • (fun i => x i) := by
  ext i
  simp only [horizOf, ofCoordsVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    horoVec_castSucc, ptInfty_val_castSucc, mul_zero, add_zero]

theorem vHeight_ofCoordsVec (x : Horizontal m) (h : ℝ) :
    vHeight (ofCoordsVec x h) = h⁻¹ := by
  rw [ofCoordsVec, vHeight_add, vHeight_smul, vHeight_smul,
    vHeight_horoVec, vHeight_ptInfty]
  ring

theorem lorB_ofCoordsVec_self (x : Horizontal m) {h : ℝ} (hh : h ≠ 0) :
    lorB (ofCoordsVec x h) (ofCoordsVec x h) = -1 := by
  simp only [ofCoordsVec, lorB_add_left, lorB_add_right, lorB_smul_left,
    lorB_smul_right, lorB_horoVec_self, lorB_ptInfty, lorB_ptInfty_left,
    vHeight_add, vHeight_smul, vHeight_horoVec, vHeight_ptInfty]
  field_simp
  ring

theorem tc_ofCoordsVec_pos (x : Horizontal m) {h : ℝ} (hh : 0 < h) :
    0 < tc (ofCoordsVec x h) := by
  rw [ofCoordsVec, tc_add, tc_smul, tc_smul, tc_horoVec, ptInfty.tc_eq]
  have := normSq_nonneg (fun i => x i)
  positivity

def ofCoords (x : Horizontal m) (h : ℝ) (hh : 0 < h) : HUpper (m + 1) where
  val := ofCoordsVec x h
  is_unit := lorB_ofCoordsVec_self x hh.ne'
  future := tc_ofCoordsVec_pos x hh

theorem vHeight_pos (X : HUpper (m + 1)) : 0 < vHeight X.val := by
  have h := neg_lorB_upper_boundary_pos X ptInfty
  simpa only [lorB_ptInfty, neg_neg] using h

def height (X : HUpper (m + 1)) : ℝ := (vHeight X.val)⁻¹

theorem height_pos (X : HUpper (m + 1)) : 0 < height X :=
  inv_pos.mpr (vHeight_pos X)

def horizontal (X : HUpper (m + 1)) : Horizontal m :=
  height X • WithLp.toLp 2 (horizOf X.val)

@[simp] theorem height_ofCoords (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    height (ofCoords x h hh) = h := by
  change (vHeight (ofCoordsVec x h))⁻¹ = h
  rw [vHeight_ofCoordsVec, inv_inv]

@[simp] theorem horizontal_ofCoords (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    horizontal (ofCoords x h hh) = x := by
  ext i
  change height (ofCoords x h hh) * horizOf (ofCoordsVec x h) i = x i
  rw [height_ofCoords, horizOf_ofCoordsVec]
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

theorem unit_eq_horizontal (X : HUpper (m + 1)) :
    normSq (horizOf X.val) + X.val (Sum.inl (Fin.last m)) ^ 2 - tc X.val ^ 2 = -1 := by
  have h := X.is_unit
  simpa only [lorB, sdot, Fin.sum_univ_castSucc, ← pow_two, normSq, horizOf] using h

theorem tc_mul_vHeight (X : HUpper (m + 1)) :
    2 * tc X.val * vHeight X.val = normSq (horizOf X.val) + vHeight X.val ^ 2 + 1 := by
  have h := unit_eq_horizontal X
  unfold vHeight
  nlinarith

theorem ext_of_horizOf_vHeight {X Y : HUpper (m + 1)}
    (hh : horizOf X.val = horizOf Y.val) (hv : vHeight X.val = vHeight Y.val) :
    X = Y := by
  have hX := tc_mul_vHeight X
  have hY := tc_mul_vHeight Y
  rw [← hh, ← hv] at hY
  have ht : tc X.val = tc Y.val := by
    apply mul_right_cancel₀ (vHeight_pos X).ne'
    nlinarith
  have ha : X.val (Sum.inl (Fin.last m)) = Y.val (Sum.inl (Fin.last m)) := by
    unfold vHeight at hv
    linarith
  apply HUpper.ext
  funext a
  rcases a with j | k
  · refine Fin.lastCases ha (fun i => ?_) j
    exact congrFun hh i
  · have hk : k = 0 := Subsingleton.elim k 0
    subst k
    exact ht

@[simp] theorem ofCoords_horizontal_height (X : HUpper (m + 1)) :
    ofCoords (horizontal X) (height X) (height_pos X) = X := by
  apply ext_of_horizOf_vHeight
  · change horizOf (ofCoordsVec (horizontal X) (height X)) = horizOf X.val
    rw [horizOf_ofCoordsVec]
    ext i
    change (height X)⁻¹ * (height X * horizOf X.val i) = horizOf X.val i
    rw [← mul_assoc, inv_mul_cancel₀ (height_pos X).ne', one_mul]
  · change vHeight (ofCoordsVec (horizontal X) (height X)) = vHeight X.val
    rw [vHeight_ofCoordsVec, height, inv_inv]

def coordsEquiv : HUpper (m + 1) ≃ Horizontal m × {h : ℝ // 0 < h} where
  toFun X := (horizontal X, ⟨height X, height_pos X⟩)
  invFun p := ofCoords p.1 p.2.1 p.2.2
  left_inv := ofCoords_horizontal_height
  right_inv p := by
    apply Prod.ext
    · exact horizontal_ofCoords p.1 p.2.1 p.2.2
    · apply Subtype.ext
      exact height_ofCoords p.1 p.2.1 p.2.2

theorem busemann_ofCoords (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    busemann ptInfty (ofCoords x h hh) = -Real.log h := by
  change Real.log (-lorB (ofCoordsVec x h) ptInfty.val) = _
  rw [lorB_ptInfty, neg_neg, vHeight_ofCoordsVec, Real.log_inv]

theorem busemann_eq_neg_log_height (X : HUpper (m + 1)) :
    busemann ptInfty X = -Real.log (height X) := by
  conv_lhs => rw [← ofCoords_horizontal_height X]
  exact busemann_ofCoords _ _ _

theorem mem_horoball_iff_height (X : HUpper (m + 1)) (c : ℝ) :
    X ∈ horoball ptInfty c ↔ Real.exp (-c) ≤ height X := by
  change busemann ptInfty X ≤ c ↔ _
  rw [busemann_eq_neg_log_height]
  constructor
  · intro h
    have h' := Real.exp_le_exp.mpr (show -c ≤ Real.log (height X) by linarith)
    simpa only [Real.exp_log (height_pos X)] using h'
  · intro h
    have h' := Real.log_le_log (Real.exp_pos (-c)) h
    rw [Real.log_exp] at h'
    linarith

theorem cosh_dist_ofCoords (x y : Horizontal m) (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    Real.cosh (dist (ofCoords x h hh) (ofCoords y k hk))
      = (‖x - y‖ ^ 2 + h ^ 2 + k ^ 2) / (2 * h * k) := by
  rw [HyperbolicConvexity.cosh_dist]
  change -lorB (ofCoordsVec x h) (ofCoordsVec y k) = _
  simp only [ofCoordsVec, lorB_add_left, lorB_add_right, lorB_smul_left,
    lorB_smul_right, lorB_horoVec_horoVec, lorB_ptInfty, lorB_ptInfty_left,
    vHeight_add, vHeight_smul, vHeight_horoVec, vHeight_ptInfty]
  have hn : normSq ((fun i => x i) - (fun i => y i)) = ‖x - y‖ ^ 2 :=
    normSq_horizontal (x - y)
  rw [hn]
  field_simp
  ring

theorem eq_horoVec_of_null_vHeight {v : LorVec (m + 1)}
    (hv : lorB v v = 0) (hh : vHeight v = 1) :
    v = horoVec (horizOf v) := by
  have hunit : normSq (horizOf v) + v (Sum.inl (Fin.last m)) ^ 2 - tc v ^ 2 = 0 := by
    simpa only [lorB, sdot, Fin.sum_univ_castSucc, ← pow_two, normSq, horizOf] using hv
  have ha : v (Sum.inl (Fin.last m)) = tc v - 1 := by
    unfold vHeight at hh
    linarith
  rw [ha] at hunit
  have ht : tc v = (normSq (horizOf v) + 1) / 2 := by nlinarith
  funext a
  rcases a with j | k
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [horoVec_last, ha, ht]
      ring
    · rw [horoVec_castSucc]
      rfl
  · have hk : k = 0 := Subsingleton.elim k 0
    subst k
    exact ht

theorem vHeight_mulVec_of_fix (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) (v : LorVec (m + 1)) :
    vHeight (matOf g *ᵥ v) = vHeight v := by
  have h := lorB_matOf_mulVec g v ptInfty.val
  rw [hg, lorB_ptInfty, lorB_ptInfty] at h
  linarith

def flatMap (g : LorGrp (m + 1)) (x : Horizontal m) : Horizontal m :=
  WithLp.toLp 2 (horizOf (matOf g *ᵥ horoVec (fun i => x i)))

theorem mulVec_horoVec_of_fix (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) (x : Horizontal m) :
    matOf g *ᵥ horoVec (fun i => x i) = horoVec (fun i => flatMap g x i) := by
  apply eq_horoVec_of_null_vHeight
  · rw [lorB_matOf_mulVec, lorB_horoVec_self]
  · rw [vHeight_mulVec_of_fix g hg, vHeight_horoVec]

theorem isometry_flatMap (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) : Isometry (flatMap g) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h := lorB_matOf_mulVec g (horoVec (fun i => x i)) (horoVec (fun i => y i))
  rw [mulVec_horoVec_of_fix g hg x, mulVec_horoVec_of_fix g hg y,
    lorB_horoVec_horoVec, lorB_horoVec_horoVec] at h
  have hx : normSq ((fun i => x i) - (fun i => y i)) = ‖x - y‖ ^ 2 :=
    normSq_horizontal (x - y)
  have hfx : normSq ((fun i => flatMap g x i) - (fun i => flatMap g y i))
      = ‖flatMap g x - flatMap g y‖ ^ 2 :=
    normSq_horizontal (flatMap g x - flatMap g y)
  rw [hx, hfx] at h
  nlinarith [norm_nonneg (x - y), norm_nonneg (flatMap g x - flatMap g y)]

theorem inv_fix_ptInfty (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) :
    matOf g⁻¹ *ᵥ ptInfty.val = ptInfty.val := by
  have h := congrArg (fun v => matOf g⁻¹ *ᵥ v) hg
  rw [Matrix.mulVec_mulVec, ← matOf_mul, inv_mul_cancel, matOf_one, Matrix.one_mulVec] at h
  exact h.symm

@[simp] theorem flatMap_one (x : Horizontal m) : flatMap 1 x = x := by
  simp only [flatMap, matOf_one, Matrix.one_mulVec, horizOf_horoVec]

theorem flatMap_mul (g h : LorGrp (m + 1))
    (hh : matOf h *ᵥ ptInfty.val = ptInfty.val) (x : Horizontal m) :
    flatMap (g * h) x = flatMap g (flatMap h x) := by
  change WithLp.toLp 2 (horizOf (matOf (g * h) *ᵥ horoVec (fun i => x i))) = _
  rw [matOf_mul, ← Matrix.mulVec_mulVec, mulVec_horoVec_of_fix h hh x]
  rfl

def flatIsometryEquiv (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) : Horizontal m ≃ᵢ Horizontal m where
  toFun := flatMap g
  invFun := flatMap g⁻¹
  left_inv x := by
    rw [← flatMap_mul g⁻¹ g hg, inv_mul_cancel, flatMap_one]
  right_inv x := by
    rw [← flatMap_mul g g⁻¹ (inv_fix_ptInfty g hg), mul_inv_cancel, flatMap_one]
  isometry_toFun := isometry_flatMap g hg

theorem smul_ofCoords_of_fix (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    g • ofCoords x h hh = ofCoords (flatMap g x) h hh := by
  apply HUpper.ext
  rw [smul_val]
  change upperize (matOf g *ᵥ ofCoordsVec x h) = ofCoordsVec (flatMap g x) h
  have hv : matOf g *ᵥ ofCoordsVec x h = ofCoordsVec (flatMap g x) h := by
    simp only [ofCoordsVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      mulVec_horoVec_of_fix g hg x, hg]
  rw [hv, upperize, ite_eq_left (tc_ofCoordsVec_pos _ hh)]

theorem exists_affineIsometry_of_fix (g : LorGrp (m + 1))
    (hg : matOf g *ᵥ ptInfty.val = ptInfty.val) :
    ∃ a : Horizontal m ≃ᵃⁱ[ℝ] Horizontal m, ∀ (x : Horizontal m) (h : ℝ) (hh : 0 < h),
      g • ofCoords x h hh = ofCoords (a x) h hh := by
  refine ⟨(flatIsometryEquiv g hg).toRealAffineIsometryEquiv, ?_⟩
  exact smul_ofCoords_of_fix g hg

theorem transLor_fix_ptInfty (b : Fin m → ℝ) :
    matOf (transLor b) *ᵥ ptInfty.val = ptInfty.val := by
  rw [transLor_matOf]
  funext a
  rcases a with j | k
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [transMat_mulVec_axis, horizOf_ptInfty, ptInfty_val_time,
        ptInfty_val_last, dotB]
    · simp [transMat_mulVec_horiz, ptInfty_val_castSucc, ptInfty_val_time, ptInfty_val_last]
  · have hk : k = 0 := Subsingleton.elim k 0
    subst k
    simp [transMat_mulVec_time, horizOf_ptInfty, ptInfty_val_time, ptInfty_val_last, dotB]

theorem flatMap_transLor (b x : Horizontal m) :
    flatMap (transLor (fun i => b i)) x = x + b := by
  ext i
  change horizOf (matOf (transLor (fun j => b j)) *ᵥ horoVec (fun j => x j)) i = (x + b) i
  rw [transLor_matOf, transMat_horoVec, horizOf_horoVec]
  rfl

theorem transLor_smul_ofCoords (b x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    transLor (fun i => b i) • ofCoords x h hh = ofCoords (x + b) h hh := by
  rw [smul_ofCoords_of_fix _ (transLor_fix_ptInfty _) x h hh, flatMap_transLor]

theorem trans_po_smul_ofCoords (b x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    (poMulAction (by omega : 1 ≤ m + 1)).smul
      (QuotientGroup.mk' _ (transLor (fun i => b i)) : PO (m + 1) 1) (ofCoords x h hh)
      = ofCoords (x + b) h hh := by
  exact (po_smul_mk (by omega : 1 ≤ m + 1) (transLor (fun i => b i))
    (ofCoords x h hh)).trans (transLor_smul_ofCoords b x h hh)

theorem exists_lor_fix_of_po_fix_scale_one (g : PO (m + 1) 1)
    (hg : (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul g ptInfty = ptInfty)
    (hc : BusemannCocycle.poConfFactor (by omega) g ptInfty = 1) :
    ∃ A : LorGrp (m + 1), QuotientGroup.mk' _ A = g ∧ matOf A *ᵥ ptInfty.val = ptInfty.val := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hA : A • ptInfty = ptInfty :=
    (po_boundary_smul_mk (by omega : 1 ≤ m + 1) A ptInfty).symm.trans hg
  have heig := eigen_of_boundary_fixed hA
  change |tc (matOf A *ᵥ ptInfty.val)| = 1 at hc
  rcases le_total 0 (tc (matOf A *ᵥ ptInfty.val)) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hc
    refine ⟨A, rfl, ?_⟩
    rw [heig, hc, one_smul]
  · rw [abs_of_nonpos hneg] at hc
    have hc' : tc (matOf A *ᵥ ptInfty.val) = -1 := by linarith
    refine ⟨-A, BoundaryExtension.mk'_neg_eq_mk' A, ?_⟩
    have hmat : matOf (-A) = -matOf A := by
      change MatrixSum.ofMatrix.symm (-A : LorGrp (m + 1)).val = -MatrixSum.ofMatrix.symm A.val
      rw [Unitary.coe_neg]
      exact map_neg _ _
    rw [hmat, Matrix.neg_mulVec, heig, hc', neg_one_smul, neg_neg]

theorem exists_affineIsometry_of_po_fix_scale_one (g : PO (m + 1) 1)
    (hg : (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul g ptInfty = ptInfty)
    (hc : BusemannCocycle.poConfFactor (by omega) g ptInfty = 1) :
    ∃ a : Horizontal m ≃ᵃⁱ[ℝ] Horizontal m, ∀ (x : Horizontal m) (h : ℝ) (hh : 0 < h),
      (poMulAction (by omega : 1 ≤ m + 1)).smul g (ofCoords x h hh)
        = ofCoords (a x) h hh := by
  obtain ⟨A, hA, hfix⟩ := exists_lor_fix_of_po_fix_scale_one g hg hc
  obtain ⟨a, ha⟩ := exists_affineIsometry_of_fix A hfix
  refine ⟨a, fun x h hh => ?_⟩
  rw [← hA]
  exact (po_smul_mk (by omega : 1 ≤ m + 1) A (ofCoords x h hh)).trans (ha x h hh)

end DifferentialGeometry.Horospherical
