import DifferentialGeometry.Topology.MetricSpace.CircleDistance

set_option autoImplicit false

open Set Metric

namespace IsometryEquiv

noncomputable def ballCongr {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (p : X) (R : ℝ) : ball p R ≃ᵢ ball (e p) R where
  toFun x := ⟨e x.val, by simpa only [mem_ball, e.dist_eq] using x.property⟩
  invFun y := ⟨e.symm y.val, by
    have h := y.property
    simpa only [mem_ball, ← e.symm.dist_eq, e.symm_apply_apply] using h⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  isometry_toFun := Isometry.of_dist_eq (fun x y => e.dist_eq x.val y.val)

@[simp] theorem ballCongr_apply {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (p : X) (R : ℝ) (x : ball p R) :
    (e.ballCongr p R x).val = e x.val := rfl

noncomputable def ballCongrAt {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (p : X) (q : Y) (he : e p = q) (R : ℝ) :
    ball p R ≃ᵢ ball q R := by
  subst q
  exact e.ballCongr p R

@[simp] theorem ballCongrAt_apply {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (p : X) (q : Y) (he : e p = q) (R : ℝ) (x : ball p R) :
    (e.ballCongrAt p q he R x).val = e x.val := by
  subst q
  rfl

noncomputable def realSubsetBall {s : Set ℝ} (a : s) (R : ℝ)
    (h : ball a.val R ⊆ s) : ball a R ≃ᵢ ball (0 : ℝ) R where
  toFun x := ⟨x.val.val - a.val, by
    change |x.val.val - a.val - 0| < R
    simpa only [mem_ball, Subtype.dist_eq, Real.dist_eq, sub_zero] using x.property⟩
  invFun y := ⟨⟨y.val + a.val, h (by
    change |y.val + a.val - a.val| < R
    simpa only [mem_ball, add_sub_cancel_right, Real.dist_eq, sub_zero] using y.property)⟩, by
      change |y.val + a.val - a.val| < R
      simpa only [mem_ball, add_sub_cancel_right, Real.dist_eq, sub_zero] using y.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact sub_add_cancel _ _
  right_inv y := Subtype.ext (add_sub_cancel_right _ _)
  isometry_toFun := Isometry.of_dist_eq (by
    intro x y
    change |(x.val.val - a.val) - (y.val.val - a.val)| = |x.val.val - y.val.val|
    rw [sub_sub_sub_cancel_right])

@[simp] theorem realSubsetBall_apply {s : Set ℝ} (a : s) (R : ℝ)
    (h : ball a.val R ⊆ s) (x : ball a R) :
    (realSubsetBall a R h x).val = x.val.val - a.val := rfl


noncomputable def reflectIcc (L : ℝ) : Icc (0 : ℝ) L ≃ᵢ Icc (0 : ℝ) L where
  toFun x := ⟨L - x.val, by constructor <;> linarith [x.property.1, x.property.2]⟩
  invFun x := ⟨L - x.val, by constructor <;> linarith [x.property.1, x.property.2]⟩
  left_inv x := by apply Subtype.ext; dsimp; ring
  right_inv x := by apply Subtype.ext; dsimp; ring
  isometry_toFun := Isometry.of_dist_eq (by
    intro x y
    change |(L - x.val) - (L - y.val)| = |x.val - y.val|
    rw [sub_sub_sub_cancel_left, abs_sub_comm])

@[simp] theorem reflectIcc_apply (L : ℝ) (x : Icc (0 : ℝ) L) :
    (reflectIcc L x).val = L - x.val := rfl

end IsometryEquiv

namespace AddCircle

noncomputable def realBallIsometry {L R : ℝ} (hL : 0 < L) (hR : 4 * R ≤ L) :
    ball (0 : ℝ) R ≃ᵢ ball (0 : AddCircle L) R := by
  let F : ball (0 : ℝ) R → ball (0 : AddCircle L) R := fun x => ⟨(x.val : AddCircle L), by
    have hx : |x.val| < R := by simpa only [mem_ball, Real.dist_eq, sub_zero] using x.property
    have hn := (norm_coe_eq_abs_iff L hL.ne').mpr
      (show |x.val| ≤ |L| / 2 by rw [abs_of_pos hL]; linarith)
    simpa only [mem_ball, dist_zero_right, hn] using hx⟩
  have hi : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    have hx : |x.val| < R := by simpa only [mem_ball, Real.dist_eq, sub_zero] using x.property
    have hy : |y.val| < R := by simpa only [mem_ball, Real.dist_eq, sub_zero] using y.property
    change dist (x.val : AddCircle L) (y.val : AddCircle L) = |x.val - y.val|
    apply dist_coe_eq_abs_of_le_half_period hL
    linarith [abs_sub x.val y.val]
  have hs : Function.Surjective F := by
    intro y
    let : Fact (0 < L) := ⟨hL⟩
    let v := equivIco L (-L / 2) y.val
    have hcoe : (v.val : AddCircle L) = y.val := coe_equivIco
    have hv : |v.val| ≤ L / 2 := by
      rw [abs_le]
      constructor <;> linarith [v.property.1, v.property.2]
    have hn : |v.val| = ‖y.val‖ := by
      rw [← hcoe]
      exact ((norm_coe_eq_abs_iff L hL.ne').mpr (by rwa [abs_of_pos hL])).symm
    have hvR : v.val ∈ ball (0 : ℝ) R := by
      rw [mem_ball, Real.dist_eq, sub_zero, hn]
      simpa only [mem_ball, dist_zero_right] using y.property
    exact ⟨⟨v.val, hvR⟩, Subtype.ext hcoe⟩
  exact ⟨Equiv.ofBijective F ⟨hi.injective, hs⟩, hi⟩

@[simp] theorem realBallIsometry_apply {L R : ℝ} (hL : 0 < L) (hR : 4 * R ≤ L)
    (x : ball (0 : ℝ) R) :
    (realBallIsometry hL hR x).val = (x.val : AddCircle L) := rfl

end AddCircle
