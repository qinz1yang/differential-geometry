import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import DifferentialGeometry.Geometry.Lorentz.Isometry

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem lorentzExtension_time_pos_of_norm_le_one (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    {u : E} (hu : ‖u‖ ≤ 1) : 0 < (lorentzExtension f (1, u)).1 := by
  let p : ℝ × E := lorentzExtension f.symm (1, 0)
  have hp0 : 0 < p.1 := lorentzExtension_origin_time_pos f.symm
  have hp : lorentzForm E p p = -1 := by
    change lorentzForm E (lorentzExtension f.symm (1, 0))
      (lorentzExtension f.symm (1, 0)) = -1
    rw [(lorentzExtension f.symm).map_app]
    simp [lorentzForm_apply]
  have hn : ‖p.2‖ < p.1 := by
    apply (sq_lt_sq₀ (norm_nonneg p.2) hp0.le).mp
    rw [lorentzForm_apply, real_inner_self_eq_norm_sq] at hp
    nlinarith only [hp]
  have hi : inner ℝ p.2 u ≤ ‖p.2‖ := calc
    inner ℝ p.2 u ≤ ‖p.2‖ * ‖u‖ := real_inner_le_norm p.2 u
    _ ≤ ‖p.2‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = ‖p.2‖ := mul_one _
  have hpinv : lorentzExtension f p = (1, 0) := by
    dsimp only [p]
    rw [lorentzExtension_symm]
    exact (lorentzExtension f).toLinearEquiv.apply_symm_apply (1, 0)
  have h := (lorentzExtension f).map_app (1, u) p
  rw [hpinv] at h
  simp only [lorentzForm_apply, inner_zero_left, one_mul, mul_one, zero_sub] at h
  linarith only [h, hi, hn]

theorem lorentzExtension_sphere_time_pos (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) : 0 < (lorentzExtension f (1, (ξ : E))).1 :=
  lorentzExtension_time_pos_of_norm_le_one f (le_of_eq (norm_eq_of_mem_sphere ξ))

private theorem boundary_norm (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) :
    ‖(lorentzExtension f (1, (ξ : E))).2‖ = (lorentzExtension f (1, (ξ : E))).1 := by
  have h := (lorentzExtension f).map_app (1, (ξ : E)) (1, (ξ : E))
  simp only [lorentzForm_apply, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere,
    one_pow, mul_one] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (lorentzExtension_sphere_time_pos f ξ).le).mp
  nlinarith only [h]

private def boundaryPoint (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) : Metric.sphere (0 : F) 1 :=
  ⟨(lorentzExtension f (1, (ξ : E))).1⁻¹ • (lorentzExtension f (1, (ξ : E))).2, by
    have ht := lorentzExtension_sphere_time_pos f ξ
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos ht, boundary_norm, inv_mul_cancel₀ ht.ne']⟩

private theorem boundaryPoint_lift (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) :
    (1, (boundaryPoint f ξ : F)) =
      (lorentzExtension f (1, (ξ : E))).1⁻¹ • lorentzExtension f (1, (ξ : E)) := by
  apply Prod.ext
  · change 1 = (lorentzExtension f (1, (ξ : E))).1⁻¹ *
      (lorentzExtension f (1, (ξ : E))).1
    exact (inv_mul_cancel₀ (lorentzExtension_sphere_time_pos f ξ).ne').symm
  · rfl

private theorem boundaryPoint_symm (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) : boundaryPoint f.symm (boundaryPoint f ξ) = ξ := by
  have ha := (lorentzExtension_sphere_time_pos f ξ).ne'
  have hi : (lorentzExtension f).symm (lorentzExtension f (1, (ξ : E))) = (1, (ξ : E)) :=
    (lorentzExtension f).toLinearEquiv.symm_apply_apply _
  have h : lorentzExtension f.symm (1, (boundaryPoint f ξ : F)) =
      (lorentzExtension f (1, (ξ : E))).1⁻¹ • (1, (ξ : E)) := by
    rw [boundaryPoint_lift, lorentzExtension_symm, map_smul, hi]
  apply Subtype.ext
  change (lorentzExtension f.symm (1, (boundaryPoint f ξ : F))).1⁻¹ •
    (lorentzExtension f.symm (1, (boundaryPoint f ξ : F))).2 = (ξ : E)
  rw [h]
  simp [smul_smul, ha]

private theorem continuous_boundaryPoint (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    Continuous (boundaryPoint f) := by
  have h : Continuous (fun ξ : Metric.sphere (0 : E) 1 =>
      lorentzExtension f (1, (ξ : E))) := by
    exact (lorentzIsometryContinuousLinearEquiv (lorentzExtension f)).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  exact ((h.fst.inv₀ fun ξ => (lorentzExtension_sphere_time_pos f ξ).ne').smul h.snd).subtype_mk _

def boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 where
  toFun := boundaryPoint f
  invFun := boundaryPoint f.symm
  left_inv := boundaryPoint_symm f
  right_inv ξ := by
    simpa only [IsometryEquiv.symm_symm] using boundaryPoint_symm f.symm ξ
  continuous_toFun := continuous_boundaryPoint f
  continuous_invFun := continuous_boundaryPoint f.symm

theorem boundaryHomeomorph_apply_coe (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) :
    (boundaryHomeomorph f ξ : F) =
      (lorentzExtension f (1, (ξ : E))).1⁻¹ • (lorentzExtension f (1, (ξ : E))).2 := rfl

theorem lorentzExtension_sphere_eq_smul_boundaryHomeomorph
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (ξ : Metric.sphere (0 : E) 1) :
    lorentzExtension f (1, (ξ : E)) =
      (lorentzExtension f (1, (ξ : E))).1 • (1, (boundaryHomeomorph f ξ : F)) := by
  apply Prod.ext
  · simp
  · change (lorentzExtension f (1, (ξ : E))).2 =
      (lorentzExtension f (1, (ξ : E))).1 • (boundaryHomeomorph f ξ : F)
    rw [boundaryHomeomorph_apply_coe, smul_smul,
      mul_inv_cancel₀ (lorentzExtension_sphere_time_pos f ξ).ne', one_smul]


@[simp] theorem boundaryHomeomorph_symm (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    (boundaryHomeomorph f).symm = boundaryHomeomorph f.symm := by
  apply Homeomorph.ext
  intro ξ
  rfl

@[simp] theorem boundaryHomeomorph_refl :
    boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) =
      Homeomorph.refl (Metric.sphere (0 : E) 1) := by
  apply Homeomorph.ext
  intro ξ
  apply Subtype.ext
  change (lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) (1, (ξ : E))).1⁻¹ •
    (lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) (1, (ξ : E))).2 = (ξ : E)
  rw [lorentzExtension_refl]
  change (1 : ℝ)⁻¹ • (ξ : E) = (ξ : E)
  simp

@[simp] theorem boundaryHomeomorph_trans {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (g : Hyperboloid F ≃ᵢ Hyperboloid G) :
    boundaryHomeomorph (f.trans g) = (boundaryHomeomorph f).trans (boundaryHomeomorph g) := by
  apply Homeomorph.ext
  intro ξ
  have ha := (lorentzExtension_sphere_time_pos f ξ).ne'
  have h : lorentzExtension g (1, (boundaryPoint f ξ : F)) =
      (lorentzExtension f (1, (ξ : E))).1⁻¹ • lorentzExtension (f.trans g) (1, (ξ : E)) := by
    rw [boundaryPoint_lift, map_smul, lorentzExtension_trans]
    rfl
  apply Subtype.ext
  change (lorentzExtension (f.trans g) (1, (ξ : E))).1⁻¹ •
      (lorentzExtension (f.trans g) (1, (ξ : E))).2 =
    (lorentzExtension g (1, (boundaryPoint f ξ : F))).1⁻¹ •
      (lorentzExtension g (1, (boundaryPoint f ξ : F))).2
  rw [h]
  simp [smul_smul, mul_inv_rev, ha]

end DifferentialGeometry.Hyperboloid
