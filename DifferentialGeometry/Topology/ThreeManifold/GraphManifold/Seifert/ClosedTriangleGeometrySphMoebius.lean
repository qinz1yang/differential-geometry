import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphDescent

/-!
# The isometries of the round three-sphere in the Hopf chart

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §3). A
point of `RoundThree` is a pair `(w₁, w₂)` of complex numbers (`hopfC`); the Hopf
parametrisation is `hopfParam (z, t) = (e^{it}, z e^{it})/√(1 + |z|²)` (`hopfAmbient_eq`). For
`(α, β)` with `|α|² + |β|² = 1` the unit quaternion `suQuat α β` acts on the left by
`(w₁, w₂) ↦ (α w₁ - β w₂, β̄ w₁ + ᾱ w₂)` and the fibre unit by the scalar `e^{is}`
(`s3Act_suLift_hopfC`). In the chart this is the Möbius map `z ↦ (β̄ + ᾱ z)/(α - β z)` with the
fibre shift `t ↦ t + s + arg (α - β z)`, wherever `α - β z ≠ 0`
(`s3Diffeo_suLift_hopfParam`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped Topology ContDiff Manifold ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

local instance factFinrankEuclideanFourSphM :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

def suQuat (α β : ℂ) : Quaternion ℝ := ⟨α.re, β.im, β.re, -α.im⟩

theorem suQuat_mem {α β : ℂ} (h : normSq α + normSq β = 1) :
    suQuat α β ∈ unitary (Quaternion ℝ) := by
  have hn : Quaternion.normSq (suQuat α β) = 1 := by
    rw [Quaternion.normSq_def']
    simp only [suQuat, normSq_apply] at h ⊢
    linear_combination h
  exact Unitary.mem_iff.mpr ⟨by rw [Quaternion.star_mul_self, hn]; rfl,
    by rw [Quaternion.self_mul_star, hn]; rfl⟩

def suLift (α β : ℂ) (h : normSq α + normSq β = 1) (s : ℝ) : S3Lift :=
  (⟨suQuat α β, suQuat_mem h⟩, Multiplicative.ofAdd s)

def hopfC (w₁ w₂ : ℂ) : EuclideanSpace ℝ (Fin 4) := !₂[w₁.re, w₁.im, w₂.re, w₂.im]

theorem s3Quat_hopfC (w₁ w₂ : ℂ) :
    s3Quat (hopfC w₁ w₂) = ⟨w₁.re, -w₂.im, w₂.re, -w₁.im⟩ := by
  ext <;> simp [hopfC]

theorem s3Act_suLift_hopfC {α β : ℂ} (h : normSq α + normSq β = 1) (s : ℝ) (w₁ w₂ : ℂ) :
    s3Act (suLift α β h s) (hopfC w₁ w₂) =
      hopfC ((α * w₁ - β * w₂) * exp (s * I)) ((conj β * w₁ + conj α * w₂) * exp (s * I)) := by
  apply s3Quat.injective
  rw [s3Act_apply, s3Quat_hopfC, s3Quat_hopfC]
  change suQuat α β * _ * s3FibreUnit s = _
  ext <;> simp [suQuat, s3FibreUnit, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] <;> ring

theorem hopfAmbient_eq (x : ModelCoordinates) :
    hopfAmbient x = hopfC (((Real.sqrt (stereoDenom x))⁻¹ : ℝ) * exp (x 2 * I))
      (((Real.sqrt (stereoDenom x))⁻¹ : ℝ) * (planeOf x * exp (x 2 * I))) := by
  ext i
  fin_cases i <;>
    simp [hopfAmbient, hopfFrame, hopfC, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]

theorem stereoDenom_ofPlane (w : ℂ) (t : ℝ) : stereoDenom (ofPlane w t) = 1 + normSq w := by
  rw [stereoDenom, normSq_apply]
  simp only [ofPlane]
  simp
  ring

theorem stereoDenom_moebius {α β : ℂ} (h : normSq α + normSq β = 1) {z : ℂ}
    (hq : α - β * z ≠ 0) (t : ℝ) :
    stereoDenom (ofPlane ((conj β + conj α * z) / (α - β * z)) t) =
      (1 + normSq z) / normSq (α - β * z) := by
  have hn : normSq (α - β * z) ≠ 0 := (normSq_pos.2 hq).ne'
  have key : normSq (α - β * z) + normSq (conj β + conj α * z) = 1 + normSq z := by
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, conj_re,
      conj_im] at h ⊢
    linear_combination (1 + z.re * z.re + z.im * z.im) * h
  rw [stereoDenom_ofPlane, normSq_div, eq_div_iff hn, add_mul, div_mul_cancel₀ _ hn, one_mul]
  linarith

theorem s3Diffeo_suLift_hopfParam {α β : ℂ} (h : normSq α + normSq β = 1) (s : ℝ)
    (x : ModelCoordinates) (hq : α - β * planeOf x ≠ 0) :
    s3Diffeo (suLift α β h s) (hopfParam x) =
      hopfParam (ofPlane ((conj β + conj α * planeOf x) / (α - β * planeOf x))
        (x 2 + s + arg (α - β * planeOf x))) := by
  set z := planeOf x with hz
  set q := α - β * z with hqdef
  set y := ofPlane ((conj β + conj α * z) / q) (x 2 + s + arg q) with hy
  apply Subtype.ext
  change s3Act (suLift α β h s) (hopfAmbient x) = hopfAmbient y
  rw [hopfAmbient_eq, hopfAmbient_eq, s3Act_suLift_hopfC]
  have hD := stereoDenom_pos x
  have hnq : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hsq : Real.sqrt (stereoDenom y) = Real.sqrt (stereoDenom x) / ‖q‖ := by
    rw [hy, stereoDenom_moebius h hq]
    have hx : stereoDenom x = 1 + normSq z := by
      simp [stereoDenom, hz, normSq_apply]
      ring
    rw [hx, Real.sqrt_div' _ (normSq_nonneg q)]
    rw [normSq_eq_norm_sq q, Real.sqrt_sq hnq.le]
  have hr : ((Real.sqrt (stereoDenom y))⁻¹ : ℝ) = ‖q‖ * (Real.sqrt (stereoDenom x))⁻¹ := by
    rw [hsq, inv_div, div_eq_mul_inv]
  have hy2 : y 2 = x 2 + s + arg q := by rw [hy, ofPlane_apply_two]
  have hpy : planeOf y = (conj β + conj α * z) / q := by rw [hy, planeOf_ofPlane]
  have hexp : exp ((y 2 : ℂ) * I) = exp ((x 2 : ℂ) * I) * exp ((s : ℂ) * I) * (q / ‖q‖) := by
    rw [hy2]
    have harg : exp ((arg q : ℂ) * I) = q / ‖q‖ := by
      have := norm_mul_exp_arg_mul_I q
      rw [eq_div_iff (ofReal_ne_zero.2 hnq.ne'), mul_comm]
      exact this
    rw [← harg, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have hq' : (‖q‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 hnq.ne'
  rw [hr, hpy, hexp]
  congr 1
  · push_cast
    field_simp
    rfl
  · push_cast
    field_simp
    rfl

def cNorm (v : ℂ) : ℝ := (Real.sqrt (1 + normSq v))⁻¹

theorem cNorm_pos (v : ℂ) : 0 < cNorm v :=
  inv_pos.2 (Real.sqrt_pos.2 (by have := normSq_nonneg v; linarith))

theorem cNorm_sq (v : ℂ) : cNorm v ^ 2 * (1 + normSq v) = 1 := by
  have h : 0 < 1 + normSq v := by have := normSq_nonneg v; linarith
  rw [cNorm, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

theorem normSq_recentre (v : ℂ) :
    normSq (cNorm v : ℂ) + normSq ((cNorm v : ℂ) * conj v) = 1 := by
  rw [normSq_mul, normSq_conj, normSq_ofReal, ← cNorm_sq v]
  ring

theorem normSq_recentreInv (v : ℂ) :
    normSq (cNorm v : ℂ) + normSq (-((cNorm v : ℂ) * conj v)) = 1 := by
  rw [normSq_neg]
  exact normSq_recentre v

def recentreS3 (v : ℂ) : S3Lift :=
  suLift (cNorm v) ((cNorm v : ℂ) * conj v) (normSq_recentre v) 0

def recentreInvS3 (v : ℂ) : S3Lift :=
  suLift (cNorm v) (-((cNorm v : ℂ) * conj v)) (normSq_recentreInv v) 0

theorem recentreInvS3_mul_recentreS3 (v : ℂ) : recentreInvS3 v * recentreS3 v = 1 := by
  have h := cNorm_sq v
  apply Prod.ext
  · apply Subtype.ext
    change suQuat _ _ * suQuat _ _ = 1
    simp only [normSq_apply] at h
    ext <;> simp only [suQuat, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, ofReal_re, ofReal_im, mul_re, mul_im,
      conj_re, conj_im, neg_re, neg_im] <;> first | ring1 | linear_combination h
  · apply Multiplicative.toAdd.injective
    simp [recentreS3, recentreInvS3, suLift]

theorem recentreS3_mul_recentreInvS3 (v : ℂ) : recentreS3 v * recentreInvS3 v = 1 := by
  have h := cNorm_sq v
  apply Prod.ext
  · apply Subtype.ext
    change suQuat _ _ * suQuat _ _ = 1
    simp only [normSq_apply] at h
    ext <;> simp only [suQuat, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, ofReal_re, ofReal_im, mul_re, mul_im,
      conj_re, conj_im, neg_re, neg_im] <;> first | ring1 | linear_combination h
  · apply Multiplicative.toAdd.injective
    simp [recentreS3, recentreInvS3, suLift]

def centred (v : ℂ) (x : ModelCoordinates) : ModelCoordinates :=
  ofPlane ((planeOf x - v) / (1 + conj v * planeOf x)) (x 2 + arg (1 + conj v * planeOf x))

def uncentred (v : ℂ) (y : ModelCoordinates) : ModelCoordinates :=
  ofPlane ((planeOf y + v) / (1 - conj v * planeOf y)) (y 2 + arg (1 - conj v * planeOf y))

theorem s3Diffeo_recentreInvS3 (v : ℂ) (x : ModelCoordinates)
    (hx : 1 + conj v * planeOf x ≠ 0) :
    s3Diffeo (recentreInvS3 v) (hopfParam x) = hopfParam (centred v x) := by
  have hc := cNorm_pos v
  have hq : (cNorm v : ℂ) - -((cNorm v : ℂ) * conj v) * planeOf x =
      (cNorm v : ℂ) * (1 + conj v * planeOf x) := by ring
  have hq0 : (cNorm v : ℂ) - -((cNorm v : ℂ) * conj v) * planeOf x ≠ 0 := by
    rw [hq]
    exact mul_ne_zero (ofReal_ne_zero.2 hc.ne') hx
  have hn : conj (-((cNorm v : ℂ) * conj v)) + conj (cNorm v : ℂ) * planeOf x =
      (cNorm v : ℂ) * (planeOf x - v) := by
    rw [map_neg, map_mul, conj_conj, conj_ofReal]
    ring
  rw [recentreInvS3, s3Diffeo_suLift_hopfParam _ _ x hq0, hq, arg_real_mul _ hc, hn,
    mul_div_mul_left _ _ (ofReal_ne_zero.2 hc.ne'), add_zero]
  rfl

theorem s3Diffeo_recentreS3 (v : ℂ) (y : ModelCoordinates)
    (hy : 1 - conj v * planeOf y ≠ 0) :
    s3Diffeo (recentreS3 v) (hopfParam y) = hopfParam (uncentred v y) := by
  have hc := cNorm_pos v
  have hq : (cNorm v : ℂ) - (cNorm v : ℂ) * conj v * planeOf y =
      (cNorm v : ℂ) * (1 - conj v * planeOf y) := by ring
  have hq0 : (cNorm v : ℂ) - (cNorm v : ℂ) * conj v * planeOf y ≠ 0 := by
    rw [hq]
    exact mul_ne_zero (ofReal_ne_zero.2 hc.ne') hy
  have hn : conj ((cNorm v : ℂ) * conj v) + conj (cNorm v : ℂ) * planeOf y =
      (cNorm v : ℂ) * (planeOf y + v) := by
    rw [map_mul, conj_conj, conj_ofReal]
    ring
  rw [recentreS3, s3Diffeo_suLift_hopfParam _ _ y hq0, hq, arg_real_mul _ hc, hn,
    mul_div_mul_left _ _ (ofReal_ne_zero.2 hc.ne'), add_zero]
  rfl

theorem screwDiffeomorph_eq (θ s : ℝ) (x : ModelCoordinates) :
    screwDiffeomorph θ s x = planeRotation θ x + GC.Geometry.fibreShift s := by
  change planeRotation (θ * ((1 : ℤ) : ℝ)) x + GC.Geometry.fibreShift (s * ((1 : ℤ) : ℝ)) = _
  simp only [Int.cast_one, mul_one]

theorem planeOf_screwDiffeomorph (θ s : ℝ) (x : ModelCoordinates) :
    planeOf (screwDiffeomorph θ s x) = exp (θ * I) * planeOf x := by
  rw [screwDiffeomorph_eq]
  apply Complex.ext
  · simp [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  · simp [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    ring

theorem screwDiffeomorph_two (θ s : ℝ) (x : ModelCoordinates) :
    screwDiffeomorph θ s x 2 = x 2 + s := by
  rw [screwDiffeomorph_eq]
  simp

def screwSph (v : ℂ) (θ s : ℝ) : S3Lift := recentreS3 v * screwLiftS3 0 θ s * recentreInvS3 v

def screwChart (v : ℂ) (θ s : ℝ) (x : ModelCoordinates) : ModelCoordinates :=
  uncentred v (screwDiffeomorph θ s (centred v x))

theorem s3Diffeo_screwSph {v : ℂ} {θ s : ℝ} {x : ModelCoordinates}
    (hx : 1 + conj v * planeOf x ≠ 0)
    (hy : 1 - conj v * planeOf (screwDiffeomorph θ s (centred v x)) ≠ 0) :
    s3Diffeo (screwSph v θ s) (hopfParam x) = hopfParam (screwChart v θ s x) := by
  rw [screwSph, s3Diffeo_mul_apply, s3Diffeo_mul_apply, s3Diffeo_recentreInvS3 v x hx]
  change s3Diffeo (recentreS3 v) (screwS3 0 θ s (hopfParam (centred v x))) = _
  rw [← hopfParam_screwDiffeomorph, s3Diffeo_recentreS3 v _ hy]
  rfl

theorem hopfParam_centred_screwChart {v : ℂ} {θ s : ℝ} {x : ModelCoordinates}
    (hx : 1 + conj v * planeOf x ≠ 0)
    (hy : 1 - conj v * planeOf (screwDiffeomorph θ s (centred v x)) ≠ 0)
    (hx' : 1 + conj v * planeOf (screwChart v θ s x) ≠ 0) :
    hopfParam (centred v (screwChart v θ s x)) =
      hopfParam (screwDiffeomorph θ s (centred v x)) := by
  rw [← s3Diffeo_recentreInvS3 v _ hx', ← s3Diffeo_screwSph hx hy, ← s3Diffeo_mul_apply,
    screwSph, ← mul_assoc, ← mul_assoc, recentreInvS3_mul_recentreS3, one_mul,
    s3Diffeo_mul_apply, s3Diffeo_recentreInvS3 v x hx]
  exact (hopfParam_screwDiffeomorph θ s _).symm

theorem centred_screwChart {v : ℂ} {θ s : ℝ} {x : ModelCoordinates}
    (hx : 1 + conj v * planeOf x ≠ 0)
    (hy : 1 - conj v * planeOf (screwDiffeomorph θ s (centred v x)) ≠ 0)
    (hx' : 1 + conj v * planeOf (screwChart v θ s x) ≠ 0) :
    planeOf (centred v (screwChart v θ s x)) = exp (θ * I) * planeOf (centred v x) ∧
      ∃ m : ℤ, centred v (screwChart v θ s x) 2 = centred v x 2 + s + 2 * Real.pi * m := by
  obtain ⟨h0, h1, m, hm⟩ := (hopfParam_eq_hopfParam_iff _ _).1
    (hopfParam_centred_screwChart hx hy hx').symm
  refine ⟨?_, m, ?_⟩
  · rw [← planeOf_screwDiffeomorph θ s]
    apply Complex.ext <;> simp [h0, h1]
  · rw [hm, screwDiffeomorph_two]

end Sph

end ClosedTriangle

end GC.Seifert
