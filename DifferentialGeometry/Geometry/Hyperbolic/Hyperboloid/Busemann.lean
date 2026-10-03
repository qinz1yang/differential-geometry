import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMetric

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem lorentzExtension_null_eq_smul_of_boundary_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) :
    lorentzExtension f (1, (ξ : E)) =
      (lorentzExtension f (1, (ξ : E))).1 • (1, (ξ : E)) := by
  have ha := (lorentzExtension_sphere_time_pos f ξ).ne'
  have h := boundaryHomeomorph_apply_coe f ξ
  rw [hξ] at h
  have hs := congrArg (fun z : E => (lorentzExtension f (1, (ξ : E))).1 • z) h
  apply Prod.ext
  · simp
  · change (lorentzExtension f (1, (ξ : E))).2 = (lorentzExtension f (1, (ξ : E))).1 • (ξ : E)
    simpa only [smul_smul, mul_inv_cancel₀ ha, one_smul] using hs.symm

private theorem abs_log_le_dist_origin_of_null_eigenvector
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    {a : ℝ} (ha : 0 < a) (hA : lorentzExtension f (1, (ξ : E)) = a • (1, (ξ : E))) :
    |Real.log a| ≤ dist (origin : Hyperboloid E) (f origin) := by
  have ht : (lorentzExtension f (1, (ξ : E))).1 = a := by
    have h := congrArg Prod.fst hA
    change (lorentzExtension f (1, (ξ : E))).1 = a * 1 at h
    simpa only [mul_one] using h
  have hAinv : lorentzExtension f.symm (1, (ξ : E)) = a⁻¹ • (1, (ξ : E)) := by
    have hi := congrArg (lorentzExtension f).symm hA
    have hc : (lorentzExtension f).symm (lorentzExtension f (1, (ξ : E))) = (1, (ξ : E)) :=
      (lorentzExtension f).toLinearEquiv.symm_apply_apply _
    rw [hc, map_smul] at hi
    rw [lorentzExtension_symm]
    calc
      (lorentzExtension f).symm (1, (ξ : E)) =
          a⁻¹ • (a • (lorentzExtension f).symm (1, (ξ : E))) := by
        rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
      _ = _ := by rw [← hi]
  have hti : (lorentzExtension f.symm (1, (ξ : E))).1 = a⁻¹ := by
    have h := congrArg Prod.fst hAinv
    change (lorentzExtension f.symm (1, (ξ : E))).1 = a⁻¹ * 1 at h
    simpa only [mul_one] using h
  have hlo := exp_neg_dist_origin_le_boundary_time f ξ
  have hhi := exp_neg_dist_origin_le_boundary_time f.symm ξ
  rw [ht] at hlo
  rw [hti] at hhi
  have hd : dist (origin : Hyperboloid E) (f.symm origin) = dist origin (f origin) := by
    rw [← f.dist_eq, f.apply_symm_apply, dist_comm]
  rw [hd] at hhi
  have hl := (Real.le_log_iff_exp_le ha).mpr hlo
  have hu := (Real.le_log_iff_exp_le (inv_pos.mpr ha)).mpr hhi
  rw [Real.log_inv] at hu
  exact abs_le.mpr ⟨hl, by linarith⟩

theorem abs_log_lorentzExtension_time_le_dist_of_boundary_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) (x : Hyperboloid E) :
    |Real.log ((lorentzExtension f (1, (ξ : E))).1)| ≤ dist x (f x) := by
  let a := (lorentzExtension f (1, (ξ : E))).1
  have ha : 0 < a := lorentzExtension_sphere_time_pos f ξ
  have hA : lorentzExtension f (1, (ξ : E)) = a • (1, (ξ : E)) :=
    lorentzExtension_null_eq_smul_of_boundary_fixed f ξ hξ
  let C := boost x
  let e := C.trans (f.trans C.symm)
  let η := boundaryHomeomorph C.symm ξ
  let k := (lorentzExtension C.symm (1, (ξ : E))).1
  have hk : k ≠ 0 := (lorentzExtension_sphere_time_pos C.symm ξ).ne'
  have hη : (1, (η : E)) = k⁻¹ • lorentzExtension C.symm (1, (ξ : E)) := by
    apply Prod.ext
    · change 1 = k⁻¹ * k
      exact (inv_mul_cancel₀ hk).symm
    · exact boundaryHomeomorph_apply_coe C.symm ξ
  have hcomp (z : ℝ × E) : lorentzExtension e z =
      lorentzExtension C.symm (lorentzExtension f (lorentzExtension C z)) := by
    simp only [e, lorentzExtension_trans]
    rfl
  have hinv : lorentzExtension C (lorentzExtension C.symm (1, (ξ : E))) = (1, (ξ : E)) := by
    rw [lorentzExtension_symm]
    exact (lorentzExtension C).toLinearEquiv.apply_symm_apply _
  have heigen : lorentzExtension e (1, (η : E)) = a • (1, (η : E)) := calc
    _ = k⁻¹ • lorentzExtension e (lorentzExtension C.symm (1, (ξ : E))) := by rw [hη, map_smul]
    _ = k⁻¹ • lorentzExtension C.symm (lorentzExtension f (1, (ξ : E))) := by rw [hcomp, hinv]
    _ = a • (1, (η : E)) := by rw [hA, map_smul, hη, smul_comm]
  have he := abs_log_le_dist_origin_of_null_eigenvector e η ha heigen
  have hd : dist (origin : Hyperboloid E) (e origin) = dist x (f x) := by
    rw [← C.dist_eq]
    change dist (boost x origin) (C (C.symm (f (C origin)))) = dist x (f x)
    rw [C.apply_symm_apply]
    simp only [C, boost_origin]
  rwa [hd] at he

end DifferentialGeometry.Hyperboloid
