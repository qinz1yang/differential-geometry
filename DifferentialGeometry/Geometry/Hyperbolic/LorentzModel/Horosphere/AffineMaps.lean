/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Homeomorphism
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Coordinates

noncomputable section

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HoroballMaps

open Hyperbolic HyperbolicAction HyperbolicBoundary MobiusBoundary Busemann Horospherical

variable {m : ℕ}

def lift (F : Horizontal m → Horizontal m) (X : HUpper (m + 1)) : HUpper (m + 1) :=
  ofCoords (F (horizontal X)) (height X) (height_pos X)

@[simp] theorem lift_ofCoords (F : Horizontal m → Horizontal m)
    (x : Horizontal m) (h : ℝ) (hh : 0 < h) :
    lift F (ofCoords x h hh) = ofCoords (F x) h hh := by
  simp [lift]

@[simp] theorem horizontal_lift (F : Horizontal m → Horizontal m) (X : HUpper (m + 1)) :
    horizontal (lift F X) = F (horizontal X) :=
  horizontal_ofCoords _ _ _

@[simp] theorem height_lift (F : Horizontal m → Horizontal m) (X : HUpper (m + 1)) :
    height (lift F X) = height X :=
  height_ofCoords _ _ _

theorem busemann_lift (F : Horizontal m → Horizontal m) (X : HUpper (m + 1)) :
    busemann ptInfty (lift F X) = busemann ptInfty X := by
  rw [busemann_eq_neg_log_height, height_lift, busemann_eq_neg_log_height]

theorem lift_mem_horoball_iff (F : Horizontal m → Horizontal m)
    (X : HUpper (m + 1)) (c : ℝ) :
    lift F X ∈ horoball ptInfty c ↔ X ∈ horoball ptInfty c := by
  change busemann ptInfty (lift F X) ≤ c ↔ busemann ptInfty X ≤ c
  rw [busemann_lift]

theorem cosh_dist_lift_le (F : Horizontal m → Horizontal m) {Q : ℝ} (hQ : 1 ≤ Q)
    (hF : ∀ x y, ‖F x - F y‖ ^ 2 ≤ Q * ‖x - y‖ ^ 2) (X Y : HUpper (m + 1)) :
    Real.cosh (dist (lift F X) (lift F Y)) ≤ Q * Real.cosh (dist X Y) := by
  obtain ⟨⟨x, h, hh⟩, rfl⟩ := coordsEquiv.symm.surjective X
  obtain ⟨⟨y, k, hk⟩, rfl⟩ := coordsEquiv.symm.surjective Y
  change Real.cosh (dist (lift F (ofCoords x h hh)) (lift F (ofCoords y k hk)))
    ≤ Q * Real.cosh (dist (ofCoords x h hh) (ofCoords y k hk))
  rw [lift_ofCoords, lift_ofCoords, cosh_dist_ofCoords, cosh_dist_ofCoords,
    ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * h * k)).mpr
  have hhQ : h ^ 2 ≤ Q * h ^ 2 := le_mul_of_one_le_left (sq_nonneg h) hQ
  have hkQ : k ^ 2 ≤ Q * k ^ 2 := le_mul_of_one_le_left (sq_nonneg k) hQ
  nlinarith [hF x y]

theorem cosh_dist_lift_sub_one_le (F : Horizontal m → Horizontal m) {Q : ℝ} (hQ : 1 ≤ Q)
    (hF : ∀ x y, ‖F x - F y‖ ^ 2 ≤ Q * ‖x - y‖ ^ 2) (X Y : HUpper (m + 1)) :
    Real.cosh (dist (lift F X) (lift F Y)) - 1 ≤ Q * (Real.cosh (dist X Y) - 1) := by
  obtain ⟨⟨x, h, hh⟩, rfl⟩ := coordsEquiv.symm.surjective X
  obtain ⟨⟨y, k, hk⟩, rfl⟩ := coordsEquiv.symm.surjective Y
  change Real.cosh (dist (lift F (ofCoords x h hh)) (lift F (ofCoords y k hk))) - 1
    ≤ Q * (Real.cosh (dist (ofCoords x h hh) (ofCoords y k hk)) - 1)
  rw [lift_ofCoords, lift_ofCoords, cosh_dist_ofCoords, cosh_dist_ofCoords]
  have hform (a : ℝ) :
      (a + h ^ 2 + k ^ 2) / (2 * h * k) - 1 = (a + (h - k) ^ 2) / (2 * h * k) := by
    field_simp
    ring
  rw [hform, hform, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * h * k)).mpr
  have hv : (h - k) ^ 2 ≤ Q * (h - k) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hQ
  nlinarith [hF x y]

theorem uniformContinuous_lift (F : Horizontal m → Horizontal m) {Q : ℝ} (hQ : 1 ≤ Q)
    (hF : ∀ x y, ‖F x - F y‖ ^ 2 ≤ Q * ‖x - y‖ ^ 2) :
    UniformContinuous (lift F) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have hcε : 1 < Real.cosh ε := by
    have h : Real.cosh 0 < Real.cosh ε :=
      Real.cosh_lt_cosh.mpr (by simpa only [abs_zero, abs_of_pos hε] using hε)
    simpa only [Real.cosh_zero] using h
  have hneigh : {t : ℝ | 1 + Q * (Real.cosh t - 1) < Real.cosh ε} ∈ nhds 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hcε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨δ, hδ, fun X Y hXY => ?_⟩
  have hval := hball (show dist X Y ∈ Metric.ball (0 : ℝ) δ by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hXY)
  have hbound := cosh_dist_lift_sub_one_le F hQ hF X Y
  have hcosh : Real.cosh (dist (lift F X) (lift F Y)) < Real.cosh ε := by
    change 1 + Q * (Real.cosh (dist X Y) - 1) < Real.cosh ε at hval
    linarith
  simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hε] using Real.cosh_lt_cosh.mp hcosh

theorem le_add_log_of_cosh_le {a d Q : ℝ} (hd : 0 ≤ d) (hQ : 0 < Q)
    (h : Real.cosh a ≤ Q * Real.cosh d) :
    a ≤ d + Real.log (2 * Q) := by
  have ha : Real.exp a ≤ 2 * Real.cosh a := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-a)]
  have hc : Real.cosh d ≤ Real.exp d := by
    have he : Real.exp (-d) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith)
    rw [Real.cosh_eq]
    linarith
  have hcQ := mul_le_mul_of_nonneg_left hc hQ.le
  apply Real.exp_le_exp.mp
  rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * Q)]
  nlinarith

theorem dist_lift_le (F : Horizontal m → Horizontal m) {Q : ℝ} (hQ : 1 ≤ Q)
    (hF : ∀ x y, ‖F x - F y‖ ^ 2 ≤ Q * ‖x - y‖ ^ 2) (X Y : HUpper (m + 1)) :
    dist (lift F X) (lift F Y) ≤ dist X Y + Real.log (2 * Q) :=
  le_add_log_of_cosh_le dist_nonneg (lt_of_lt_of_le zero_lt_one hQ)
    (cosh_dist_lift_le F hQ hF X Y)

def affine (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) :
    HUpper (m + 1) → HUpper (m + 1) :=
  lift (fun x => L x + b)

@[simp] theorem affine_ofCoords (L : Horizontal m ≃L[ℝ] Horizontal m) (b x : Horizontal m)
    (h : ℝ) (hh : 0 < h) :
    affine L b (ofCoords x h hh) = ofCoords (L x + b) h hh :=
  lift_ofCoords _ _ _ _

@[simp] theorem horizontal_affine (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) (X : HUpper (m + 1)) :
    horizontal (affine L b X) = L (horizontal X) + b :=
  horizontal_lift _ _

@[simp] theorem height_affine (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) (X : HUpper (m + 1)) :
    height (affine L b X) = height X :=
  height_lift _ _

@[simp] theorem affine_symm_affine (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) (X : HUpper (m + 1)) :
    affine L.symm (-L.symm b) (affine L b X) = X := by
  simp [affine, lift, map_add]

def affineEquiv (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) :
    HUpper (m + 1) ≃ HUpper (m + 1) where
  toFun := affine L b
  invFun := affine L.symm (-L.symm b)
  left_inv := affine_symm_affine L b
  right_inv X := by
    have h := affine_symm_affine L.symm (-L.symm b) X
    simpa using h

def distortion (L : Horizontal m ≃L[ℝ] Horizontal m) : ℝ :=
  max 1 (max (‖L.toContinuousLinearMap‖ ^ 2) (‖L.symm.toContinuousLinearMap‖ ^ 2))

theorem one_le_distortion (L : Horizontal m ≃L[ℝ] Horizontal m) :
    1 ≤ distortion L := le_max_left _ _

theorem norm_sq_le_distortion (L : Horizontal m ≃L[ℝ] Horizontal m) :
    ‖L.toContinuousLinearMap‖ ^ 2 ≤ distortion L :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_symm_sq_le_distortion (L : Horizontal m ≃L[ℝ] Horizontal m) :
    ‖L.symm.toContinuousLinearMap‖ ^ 2 ≤ distortion L :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem affine_norm_sub_sq_le (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) {Q : ℝ} (hQ : ‖L.toContinuousLinearMap‖ ^ 2 ≤ Q)
    (x y : Horizontal m) :
    ‖(L x + b) - (L y + b)‖ ^ 2 ≤ Q * ‖x - y‖ ^ 2 := by
  rw [add_sub_add_right_eq_sub, ← map_sub]
  calc
    ‖L (x - y)‖ ^ 2 ≤ (‖L.toContinuousLinearMap‖ * ‖x - y‖) ^ 2 := by
      gcongr
      exact L.toContinuousLinearMap.le_opNorm (x - y)
    _ = ‖L.toContinuousLinearMap‖ ^ 2 * ‖x - y‖ ^ 2 := mul_pow _ _ _
    _ ≤ Q * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg _)

theorem dist_affine_le (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m)
    (X Y : HUpper (m + 1)) :
    dist (affine L b X) (affine L b Y) ≤ dist X Y + Real.log (2 * distortion L) :=
  dist_lift_le _ (one_le_distortion L)
    (affine_norm_sub_sq_le L b (norm_sq_le_distortion L)) X Y

theorem affine_isPseudoIsometry (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) :
    PseudoIsometry.IsPseudoIsometry 1 (Real.log (2 * distortion L)) (affine L b) where
  hK := le_rfl
  hC := Real.log_nonneg (by have := one_le_distortion L; linarith)
  upper X Y := by simpa only [one_mul] using dist_affine_le L b X Y
  lower X Y := by
    have h := dist_lift_le _ (one_le_distortion L)
      (affine_norm_sub_sq_le L.symm (-L.symm b) (norm_symm_sq_le_distortion L))
      (affine L b X) (affine L b Y)
    change dist (affine L.symm (-L.symm b) (affine L b X))
      (affine L.symm (-L.symm b) (affine L b Y))
        ≤ dist (affine L b X) (affine L b Y) + Real.log (2 * distortion L) at h
    rw [affine_symm_affine, affine_symm_affine] at h
    simp only [inv_one, one_mul]
    linarith

theorem uniformContinuous_affine (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) :
    UniformContinuous (affine L b) :=
  uniformContinuous_lift _ (one_le_distortion L)
    (affine_norm_sub_sq_le L b (norm_sq_le_distortion L))

theorem uniformContinuous_affineEquiv_symm (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) : UniformContinuous (affineEquiv L b).symm :=
  uniformContinuous_affine L.symm (-L.symm b)

theorem affine_mem_horoball_iff (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) (X : HUpper (m + 1)) (c : ℝ) :
    affine L b X ∈ horoball ptInfty c ↔ X ∈ horoball ptInfty c :=
  lift_mem_horoball_iff _ X c

theorem affine_image_horoball (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b : Horizontal m) (c : ℝ) :
    affine L b '' horoball ptInfty c = horoball ptInfty c := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (affine_mem_horoball_iff L b X c).mpr hX
  · intro hY
    obtain ⟨X, rfl⟩ := (affineEquiv L b).surjective Y
    exact ⟨X, (affine_mem_horoball_iff L b X c).mp hY, rfl⟩

theorem affine_translation_equivariant (L : Horizontal m ≃L[ℝ] Horizontal m)
    (b u : Horizontal m) (X : HUpper (m + 1)) :
    affine L b ((poMulAction (by omega : 1 ≤ m + 1)).smul
        (QuotientGroup.mk' _ (transLor (fun i => u i))) X)
      = (poMulAction (by omega : 1 ≤ m + 1)).smul
          (QuotientGroup.mk' _ (transLor (fun i => L u i))) (affine L b X) := by
  obtain ⟨⟨x, h, hh⟩, rfl⟩ := coordsEquiv.symm.surjective X
  change affine L b ((poMulAction _).smul _ (ofCoords x h hh))
    = (poMulAction _).smul _ (affine L b (ofCoords x h hh))
  rw [trans_po_smul_ofCoords, affine_ofCoords, affine_ofCoords, trans_po_smul_ofCoords]
  congr 1
  rw [map_add]
  abel

def affineBoundaryHomeomorph (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) :
    BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1) :=
  BoundaryHomeomorph.bExtHomeomorph (affine_isPseudoIsometry L b)
    (affine_isPseudoIsometry L.symm (-L.symm b))
    (E := 0) (E' := 0)
    (fun X => by rw [affine_symm_affine]; simp only [dist_self, le_refl])
    (fun X => by
      have h := (affineEquiv L b).apply_symm_apply X
      change dist ((affineEquiv L b) ((affineEquiv L b).symm X)) X ≤ 0
      rw [h]
      simp only [dist_self, le_refl])
    (by omega)

theorem affineBoundaryHomeomorph_converges
    (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m) (ξ : BoundaryH (m + 1)) :
    BoundaryTopology.ConvergesToBoundary
      (fun k : ℕ => affine L b (BoundaryTopology.geodesicRay ξ (k : ℝ)))
      (affineBoundaryHomeomorph L b ξ) := by
  unfold affineBoundaryHomeomorph
  rw [BoundaryHomeomorph.bExtHomeomorph_apply]
  simpa only [MorseStability.rayTo_basepointH_eq_geodesicRay] using
    BoundaryExtension.bExt_spec
      (BoundaryHomeomorph.gromovCauchy_image_ray (affine_isPseudoIsometry L b) (by omega)) ξ

end DifferentialGeometry.HoroballMaps
