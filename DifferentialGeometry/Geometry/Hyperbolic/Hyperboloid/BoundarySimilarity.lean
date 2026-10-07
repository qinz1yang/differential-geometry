import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import DifferentialGeometry.Geometry.Coordinates.StereographicComplex
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTranslation
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Equivariance
import Mathlib.Analysis.Complex.Isometry

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def transverse (x : E3) : ℂ := ⟨x 1, x 2⟩

private def transverseLinear (R : ℂ ≃ₗᵢ[ℝ] ℂ) : E3 →ₗ[ℝ] E3 where
  toFun x := WithLp.toLp 2 ![x 0, (R (transverse x)).re, (R (transverse x)).im]
  map_add' x y := by
    have ht : transverse (x + y) = transverse x + transverse y := rfl
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [ht, map_add, PiLp.add_apply]
  map_smul' c x := by
    have ht : transverse (c • x) = c • transverse x := by
      apply Complex.ext <;> simp [transverse, PiLp.smul_apply, smul_eq_mul]
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · change (R (transverse (c • x))).re = c * (R (transverse x)).re
      rw [ht, R.map_smul]
      simp
    · change (R (transverse (c • x))).im = c * (R (transverse x)).im
      rw [ht, R.map_smul]
      simp

private theorem transverseLinear_transverse (R : ℂ ≃ₗᵢ[ℝ] ℂ) (x : E3) :
    transverse (transverseLinear R x) = R (transverse x) := by
  apply Complex.ext <;> rfl

private theorem transverseLinear_leftInverse (R : ℂ ≃ₗᵢ[ℝ] ℂ) (x : E3) :
    transverseLinear R.symm (transverseLinear R x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · change (R.symm (transverse (transverseLinear R x))).re = x 1
    rw [transverseLinear_transverse, R.symm_apply_apply]
    rfl
  · change (R.symm (transverse (transverseLinear R x))).im = x 2
    rw [transverseLinear_transverse, R.symm_apply_apply]
    rfl

private def transverseRotation (R : ℂ ≃ₗᵢ[ℝ] ℂ) : E3 ≃ₗᵢ[ℝ] E3 where
  toLinearEquiv :=
    { transverseLinear R with
      invFun := transverseLinear R.symm
      left_inv := transverseLinear_leftInverse R
      right_inv := by
        intro x
        change transverseLinear R (transverseLinear R.symm x) = x
        simpa only [LinearIsometryEquiv.symm_symm] using transverseLinear_leftInverse R.symm x }
  norm_map' x := by
    have h := congrArg (fun r : ℝ => r ^ 2) (R.norm_map (transverse x))
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change x 0 ^ 2 + ((R (transverse x)).re ^ 2 + (R (transverse x)).im ^ 2) =
      x 0 ^ 2 + (x 1 ^ 2 + x 2 ^ 2)
    dsimp only [transverse] at h ⊢
    nlinarith only [h]

private def axialPoint (r : ℝ) (hr : 0 < r) : Hyperboloid E3 where
  time := (r + r⁻¹) / 2
  space := ((r - r⁻¹) / 2) • (sphereNorthPole : E3)
  time_pos := by positivity
  time_sq_sub_inner_self := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere]
    field_simp
    ring

private theorem axial_lorentzBoost_apply (r : ℝ) (hr : 0 < r) (v : ℝ × E3) :
    lorentzBoost (axialPoint r hr) v =
      (((r + r⁻¹) / 2) * v.1 + ((r - r⁻¹) / 2) * v.2 0,
        WithLp.toLp 2 ![((r - r⁻¹) / 2) * v.1 + ((r + r⁻¹) / 2) * v.2 0,
          v.2 1, v.2 2]) := by
  let c := (r + r⁻¹) / 2
  let s := (r - r⁻¹) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c + 1 ≠ 0 := by positivity
  have hid : c ^ 2 - s ^ 2 = 1 := by dsimp [c, s]; field_simp; ring
  rw [lorentzBoost_apply]
  have hi : inner ℝ (axialPoint r hr).space v.2 = s * v.2 0 := by
    rw [axialPoint, real_inner_smul_left, sphereNorthPole_coe, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    rfl
  rw [hi]
  apply Prod.ext
  · rfl
  · apply PiLp.ext
    intro i
    fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero]
      have hp0 : (axialPoint r hr).space 0 = s := by
        simp [axialPoint, s, sphereNorthPole_coe, EuclideanSpace.single]
      rw [hp0]
      change v.2 0 + (v.1 + s * v.2 0 / (c + 1)) * s = s * v.1 + c * v.2 0
      field_simp [hc1]
      have h := congrArg (fun z : ℝ => z * v.2 0) hid
      nlinarith only [h]
    · simp [axialPoint, sphereNorthPole_coe, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]
    · simp [axialPoint, sphereNorthPole_coe, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]

private def spatialIsometry (R : ℂ ≃ₗᵢ[ℝ] ℂ) : Hyperboloid E3 ≃ᵢ Hyperboloid E3 :=
  lorentzIsometryEquiv (spatialLorentzEquiv (transverseRotation R)) (by change (0 : ℝ) < 1; norm_num)

private def complexPhase (a : ℂ) (ha : a ≠ 0) : Circle :=
  ⟨a / (‖a‖ : ℂ), by
    simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr ha]⟩

def boundarySimilarity (a : ℂ) (ha : a ≠ 0) : Hyperboloid E3 ≃ᵢ Hyperboloid E3 :=
  (boost (axialPoint ‖a‖ (norm_pos_iff.mpr ha))).trans (spatialIsometry (rotation (complexPhase a ha)))

private theorem lorentzExtension_spatialIsometry (R : ℂ ≃ₗᵢ[ℝ] ℂ) :
    lorentzExtension (spatialIsometry R) = spatialLorentzEquiv (transverseRotation R) := by
  apply (exists_unique_lorentz_extension (spatialIsometry R)).unique (lorentzExtension_apply _)
  intro x
  rfl

private theorem lorentzExtension_boost (x : Hyperboloid E3) :
    lorentzExtension (boost x) = lorentzBoost x := by
  apply (exists_unique_lorentz_extension (boost x)).unique (lorentzExtension_apply _)
  intro y
  exact (lorentzBoost_apply x (y.time, y.space)).trans (boost_coordinates x y).symm

private theorem lorentzExtension_boundarySimilarity_apply (a : ℂ) (ha : a ≠ 0) (v : ℝ × E3) :
    let r := ‖a‖
    let c := (r + r⁻¹) / 2
    let s := (r - r⁻¹) / 2
    let w := (a / (r : ℂ)) * ((v.2 1 : ℂ) + (v.2 2 : ℂ) * Complex.I)
    lorentzExtension (boundarySimilarity a ha) v =
      (c * v.1 + s * v.2 0, WithLp.toLp 2 ![s * v.1 + c * v.2 0, w.re, w.im]) := by
  rw [boundarySimilarity, lorentzExtension_trans, lorentzExtension_boost,
    lorentzExtension_spatialIsometry]
  change spatialLorentzEquiv (transverseRotation (rotation (complexPhase a ha)))
    (lorentzBoost (axialPoint ‖a‖ (norm_pos_iff.mpr ha)) v) = _
  rw [axial_lorentzBoost_apply]
  apply Prod.ext
  · rfl
  · apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · change (rotation (complexPhase a ha) (⟨v.2 1, v.2 2⟩ : ℂ)).re = _
      rw [rotation_apply]
      congr 1
      apply Complex.ext <;> simp [complexPhase]
    · change (rotation (complexPhase a ha) (⟨v.2 1, v.2 2⟩ : ℂ)).im = _
      rw [rotation_apply]
      congr 1
      apply Complex.ext <;> simp [complexPhase]

theorem boundarySimilarity_coordinates (a : ℂ) (ha : a ≠ 0) (x : Hyperboloid E3) :
    let r := ‖a‖
    let c := (r + r⁻¹) / 2
    let s := (r - r⁻¹) / 2
    let w := (a / (r : ℂ)) * ((x.space 1 : ℂ) + (x.space 2 : ℂ) * Complex.I)
    ((boundarySimilarity a ha x).time, (boundarySimilarity a ha x).space) =
      (c * x.time + s * x.space 0, WithLp.toLp 2 ![s * x.time + c * x.space 0, w.re, w.im]) := by
  rw [← lorentzExtension_apply]
  exact lorentzExtension_boundarySimilarity_apply a ha (x.time, x.space)

@[simp] theorem boundaryHomeomorph_boundarySimilarity_northPole (a : ℂ) (ha : a ≠ 0) :
    boundaryHomeomorph (boundarySimilarity a ha) sphereNorthPole = sphereNorthPole := by
  have hr : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  apply Subtype.ext
  rw [boundaryHomeomorph_apply_coe, lorentzExtension_boundarySimilarity_apply]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphereNorthPole_coe, EuclideanSpace.single, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

private theorem northPole_denominator_ne_zero
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    1 - (ξ.val : E3) 0 ≠ 0 := by
  intro hz
  have hcoord : (ξ.val : E3) 0 = 1 := by linarith
  have hi : inner ℝ (sphereNorthPole : E3) (ξ.val : E3) = 1 := by
    simp only [sphereNorthPole_coe, EuclideanSpace.inner_single_left, map_one, one_mul, hcoord]
  have heq := (inner_eq_one_iff_of_norm_eq_one
    (norm_eq_of_mem_sphere sphereNorthPole) (norm_eq_of_mem_sphere ξ.val)).mp hi
  exact ξ.property (Subtype.ext heq.symm)

theorem stereographicComplex_boundarySimilarity (a : ℂ) (ha : a ≠ 0)
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    stereographicComplex
      ⟨boundaryHomeomorph (boundarySimilarity a ha) ξ.val, by
        intro hp
        apply ξ.property
        apply (boundaryHomeomorph (boundarySimilarity a ha)).injective
        rw [boundaryHomeomorph_boundarySimilarity_northPole]
        exact hp⟩ = a * stereographicComplex ξ := by
  let r := ‖a‖
  let c := (r + r⁻¹) / 2
  let s := (r - r⁻¹) / 2
  let T := c + s * (ξ.val : E3) 0
  let w := (a / (r : ℂ)) * (((ξ.val : E3) 1 : ℂ) + ((ξ.val : E3) 2 : ℂ) * Complex.I)
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr ha
  have hT : T ≠ 0 := by
    have hp := lorentzExtension_sphere_time_pos (boundarySimilarity a ha) ξ.val
    rw [lorentzExtension_boundarySimilarity_apply] at hp
    change 0 < c * 1 + s * (ξ.val : E3) 0 at hp
    simpa only [mul_one] using hp.ne'
  have hd := northPole_denominator_ne_zero ξ
  have hcs : c - s = r⁻¹ := by dsimp [c, s]; ring
  have hdiff : T - (s + c * (ξ.val : E3) 0) = r⁻¹ * (1 - (ξ.val : E3) 0) := by
    calc
      _ = (c - s) * (1 - (ξ.val : E3) 0) := by dsimp [T]; ring
      _ = _ := by rw [hcs]
  have hden : 1 - T⁻¹ * (s + c * (ξ.val : E3) 0) = (1 - (ξ.val : E3) 0) / (r * T) := by
    field_simp [hT, hr]
    have hm := congrArg (fun u : ℝ => r * u) hdiff
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul] at hm
    nlinarith only [hm]
  rw [stereographicComplex_apply, stereographicComplex_apply,
    boundaryHomeomorph_apply_coe, lorentzExtension_boundarySimilarity_apply]
  simp only [mul_one, PiLp.smul_apply, smul_eq_mul]
  change (((2 / (1 - T⁻¹ * (s + c * (ξ.val : E3) 0)) : ℝ) : ℂ) *
      (((T⁻¹ * w.re : ℝ) : ℂ) + ((T⁻¹ * w.im : ℝ) : ℂ) * Complex.I)) = _
  rw [hden]
  apply Complex.ext <;>
    simp only [w, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.div_re, Complex.div_im, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  all_goals
    field_simp [hr, hT, hd]
    ring

theorem boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm
    (a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    boundaryHomeomorph (boundarySimilarity a ha) (stereographicComplex.symm z).val =
      (stereographicComplex.symm (a * z)).val := by
  let ξ := stereographicComplex.symm z
  let η : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole} :=
    ⟨boundaryHomeomorph (boundarySimilarity a ha) ξ.val, by
      intro hp
      apply ξ.property
      apply (boundaryHomeomorph (boundarySimilarity a ha)).injective
      rw [boundaryHomeomorph_boundarySimilarity_northPole]
      exact hp⟩
  have hη : stereographicComplex η = a * z := by
    simpa only [ξ, stereographicComplex.apply_symm_apply] using
      stereographicComplex_boundarySimilarity a ha ξ
  have heq : η = stereographicComplex.symm (a * z) :=
    stereographicComplex.injective (hη.trans (stereographicComplex.apply_symm_apply _).symm)
  exact congrArg Subtype.val heq

private theorem spatialIsometry_boundary_northPole (R : ℂ ≃ₗᵢ[ℝ] ℂ) :
    boundaryHomeomorph (spatialIsometry R) sphereNorthPole = sphereNorthPole := by
  apply Subtype.ext
  rw [boundaryHomeomorph_apply_coe, lorentzExtension_spatialIsometry]
  change (1 : ℝ)⁻¹ • transverseRotation R (sphereNorthPole : E3) = _
  rw [inv_one, one_smul]
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · change (R 0).re = 0
    rw [map_zero]
    rfl
  · change (R 0).im = 0
    rw [map_zero]
    rfl

private theorem spatialIsometry_boundary_stereographicComplex_symm
    (R : ℂ ≃ₗᵢ[ℝ] ℂ) (z : ℂ) :
    boundaryHomeomorph (spatialIsometry R) (stereographicComplex.symm z).val =
      (stereographicComplex.symm (R z)).val := by
  apply Subtype.ext
  rw [boundaryHomeomorph_apply_coe, lorentzExtension_spatialIsometry]
  change (1 : ℝ)⁻¹ • transverseRotation R
    ((stereographicComplex.symm z).val : E3) = _
  rw [inv_one, one_smul, stereographicComplex_symm_coe, stereographicComplex_symm_coe,
    R.norm_map]
  have ht : transverse (WithLp.toLp 2
      ![(‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4),
        4 * z.re / (‖z‖ ^ 2 + 4), 4 * z.im / (‖z‖ ^ 2 + 4)] : E3) =
      (4 / (‖z‖ ^ 2 + 4) : ℝ) • z := by
    apply Complex.ext
    · change 4 * z.re / (‖z‖ ^ 2 + 4) =
        (((4 / (‖z‖ ^ 2 + 4) : ℝ) • z).re)
      rw [Complex.real_smul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    · change 4 * z.im / (‖z‖ ^ 2 + 4) =
        (((4 / (‖z‖ ^ 2 + 4) : ℝ) • z).im)
      rw [Complex.real_smul]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      ring
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · change (R (transverse _)).re = _
    rw [ht, R.map_smul]
    change (((4 / (‖z‖ ^ 2 + 4) : ℝ) • R z).re) =
      4 * (R z).re / (‖z‖ ^ 2 + 4)
    rw [Complex.real_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · change (R (transverse _)).im = _
    rw [ht, R.map_smul]
    change (((4 / (‖z‖ ^ 2 + 4) : ℝ) • R z).im) =
      4 * (R z).im / (‖z‖ ^ 2 + 4)
    rw [Complex.real_smul]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring

theorem exists_isometryEquiv_boundary_similarity
    (r : ℝ) (hr : 0 < r) (R : ℂ ≃ₗᵢ[ℝ] ℂ) (b : ℂ) :
    ∃ e : Hyperboloid E3 ≃ᵢ Hyperboloid E3,
      boundaryHomeomorph e sphereNorthPole = sphereNorthPole ∧
      ∀ z : ℂ, boundaryHomeomorph e (stereographicComplex.symm z).val =
        (stereographicComplex.symm (r • R z + b)).val := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let e := (spatialIsometry R).trans
    ((boundarySimilarity (r : ℂ) hrC).trans (boundaryTranslation b))
  refine ⟨e, ?_, ?_⟩
  · simp only [e, boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [spatialIsometry_boundary_northPole, boundaryHomeomorph_boundarySimilarity_northPole,
      boundaryHomeomorph_boundaryTranslation_northPole]
  · intro z
    simp only [e, boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [spatialIsometry_boundary_stereographicComplex_symm,
      boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm,
      boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm]
    rfl

theorem exists_unique_isometryEquiv_boundaryHomeomorph_eq_of_similarity
    (H : Metric.sphere (0 : E3) 1 ≃ₜ Metric.sphere (0 : E3) 1)
    (r : ℝ) (hr : 0 < r) (R : ℂ ≃ₗᵢ[ℝ] ℂ) (b : ℂ)
    (hH : ∀ z : ℂ, H (stereographicComplex.symm z).val =
      (stereographicComplex.symm (r • R z + b)).val) :
    ∃! e : Hyperboloid E3 ≃ᵢ Hyperboloid E3, boundaryHomeomorph e = H := by
  have hHn : H sphereNorthPole = sphereNorthPole := by
    by_contra hn
    let z := stereographicComplex ⟨H sphereNorthPole, hn⟩
    let y := R.symm (r⁻¹ • (z - b))
    have hy : r • R y + b = z := by
      rw [show R y = r⁻¹ • (z - b) from R.apply_symm_apply _]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
    have hz : (stereographicComplex.symm z).val = H sphereNorthPole :=
      congrArg Subtype.val (stereographicComplex.symm_apply_apply ⟨H sphereNorthPole, hn⟩)
    have hh := hH y
    rw [hy, hz] at hh
    exact (stereographicComplex.symm y).property (H.injective hh)
  obtain ⟨e, hen, hez⟩ := exists_isometryEquiv_boundary_similarity r hr R b
  have he : boundaryHomeomorph e = H := by
    apply Homeomorph.ext
    intro ξ
    by_cases hξ : ξ = sphereNorthPole
    · rw [hξ, hen, hHn]
    · let z := stereographicComplex ⟨ξ, hξ⟩
      have hz : (stereographicComplex.symm z).val = ξ :=
        congrArg Subtype.val (stereographicComplex.symm_apply_apply ⟨ξ, hξ⟩)
      rw [← hz, hez, hH]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply eq_of_boundaryHomeomorph_eq (E := E3) ?_ (he'.trans he.symm)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
  norm_num

end DifferentialGeometry.Hyperboloid
