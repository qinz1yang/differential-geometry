import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Klein

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem closedBall_time_pos (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) : 0 < (lorentzExtension f (1, (u : E))).1 :=
  lorentzExtension_time_pos_of_norm_le_one f (by simpa only [Metric.mem_closedBall,
    dist_zero_right] using u.property)

private theorem closedBall_norm_le (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) :
    ‖(lorentzExtension f (1, (u : E))).2‖ ≤ (lorentzExtension f (1, (u : E))).1 := by
  have hu : ‖(u : E)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
  have h := (lorentzExtension f).map_app (1, (u : E)) (1, (u : E))
  simp only [lorentzForm_apply, real_inner_self_eq_norm_sq, mul_one] at h
  apply (sq_le_sq₀ (norm_nonneg _) (closedBall_time_pos f u).le).mp
  nlinarith [norm_nonneg (u : E)]

private def closedBallPoint (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) : Metric.closedBall (0 : F) 1 :=
  ⟨(lorentzExtension f (1, (u : E))).1⁻¹ • (lorentzExtension f (1, (u : E))).2, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (closedBall_time_pos f u))]
    calc
      _ ≤ (lorentzExtension f (1, (u : E))).1⁻¹ * (lorentzExtension f (1, (u : E))).1 :=
        mul_le_mul_of_nonneg_left (closedBall_norm_le f u)
          (inv_nonneg.mpr (closedBall_time_pos f u).le)
      _ = 1 := inv_mul_cancel₀ (closedBall_time_pos f u).ne'⟩

private theorem closedBallPoint_lift (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) :
    (1, (closedBallPoint f u : F)) =
      (lorentzExtension f (1, (u : E))).1⁻¹ • lorentzExtension f (1, (u : E)) := by
  apply Prod.ext
  · change 1 = (lorentzExtension f (1, (u : E))).1⁻¹ * (lorentzExtension f (1, (u : E))).1
    exact (inv_mul_cancel₀ (closedBall_time_pos f u).ne').symm
  · rfl

private theorem closedBallPoint_symm (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) : closedBallPoint f.symm (closedBallPoint f u) = u := by
  have ha := (closedBall_time_pos f u).ne'
  have hi : (lorentzExtension f).symm (lorentzExtension f (1, (u : E))) = (1, (u : E)) :=
    (lorentzExtension f).toLinearEquiv.symm_apply_apply _
  have h : lorentzExtension f.symm (1, (closedBallPoint f u : F)) =
      (lorentzExtension f (1, (u : E))).1⁻¹ • (1, (u : E)) := by
    rw [closedBallPoint_lift, lorentzExtension_symm, map_smul, hi]
  apply Subtype.ext
  change (lorentzExtension f.symm (1, (closedBallPoint f u : F))).1⁻¹ •
    (lorentzExtension f.symm (1, (closedBallPoint f u : F))).2 = (u : E)
  rw [h]
  simp [smul_smul, ha]

private theorem continuous_closedBallPoint (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    Continuous (closedBallPoint f) := by
  have h : Continuous (fun u : Metric.closedBall (0 : E) 1 =>
      lorentzExtension f (1, (u : E))) :=
    (lorentzIsometryContinuousLinearEquiv (lorentzExtension f)).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  exact ((h.fst.inv₀ fun u => (closedBall_time_pos f u).ne').smul h.snd).subtype_mk _

def kleinClosedBallHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : F) 1 where
  toFun := closedBallPoint f
  invFun := closedBallPoint f.symm
  left_inv := closedBallPoint_symm f
  right_inv u := by
    simpa only [IsometryEquiv.symm_symm] using closedBallPoint_symm f.symm u
  continuous_toFun := continuous_closedBallPoint f
  continuous_invFun := continuous_closedBallPoint f.symm

theorem kleinClosedBallHomeomorph_apply_coe (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (u : Metric.closedBall (0 : E) 1) :
    (kleinClosedBallHomeomorph f u : F) =
      (lorentzExtension f (1, (u : E))).1⁻¹ • (lorentzExtension f (1, (u : E))).2 := rfl

theorem kleinClosedBallHomeomorph_apply_kleinHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (x : Hyperboloid E) :
    (kleinClosedBallHomeomorph f
      (Set.inclusion Metric.ball_subset_closedBall (kleinHomeomorph x)) : F) =
        (kleinHomeomorph (f x) : F) := by
  have hl : (1, (kleinHomeomorph x : E)) = x.time⁻¹ • (x.time, x.space) := by
    apply Prod.ext
    · change 1 = x.time⁻¹ * x.time
      exact (inv_mul_cancel₀ x.time_pos.ne').symm
    · exact kleinHomeomorph_apply_coe x
  change (lorentzExtension f (1, (kleinHomeomorph x : E))).1⁻¹ •
    (lorentzExtension f (1, (kleinHomeomorph x : E))).2 = (kleinHomeomorph (f x) : F)
  rw [hl, map_smul, lorentzExtension_apply, kleinHomeomorph_apply_coe]
  simp [smul_smul, mul_inv_rev, x.time_pos.ne']

theorem kleinClosedBallHomeomorph_apply_sphere (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) :
    (kleinClosedBallHomeomorph f (Set.inclusion Metric.sphere_subset_closedBall ξ) : F) =
      (boundaryHomeomorph f ξ : F) := rfl

@[simp] theorem kleinClosedBallHomeomorph_symm (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    (kleinClosedBallHomeomorph f).symm = kleinClosedBallHomeomorph f.symm := by
  apply Homeomorph.ext
  intro u
  rfl

@[simp] theorem kleinClosedBallHomeomorph_refl :
    kleinClosedBallHomeomorph (IsometryEquiv.refl (Hyperboloid E)) =
      Homeomorph.refl (Metric.closedBall (0 : E) 1) := by
  apply Homeomorph.ext
  intro u
  apply Subtype.ext
  change (lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) (1, (u : E))).1⁻¹ •
    (lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) (1, (u : E))).2 = (u : E)
  rw [lorentzExtension_refl]
  change (1 : ℝ)⁻¹ • (u : E) = (u : E)
  simp

@[simp] theorem kleinClosedBallHomeomorph_trans {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (g : Hyperboloid F ≃ᵢ Hyperboloid G) :
    kleinClosedBallHomeomorph (f.trans g) =
      (kleinClosedBallHomeomorph f).trans (kleinClosedBallHomeomorph g) := by
  apply Homeomorph.ext
  intro u
  have ha := (closedBall_time_pos f u).ne'
  have h : lorentzExtension g (1, (closedBallPoint f u : F)) =
      (lorentzExtension f (1, (u : E))).1⁻¹ • lorentzExtension (f.trans g) (1, (u : E)) := by
    rw [closedBallPoint_lift, map_smul, lorentzExtension_trans]
    rfl
  apply Subtype.ext
  change (lorentzExtension (f.trans g) (1, (u : E))).1⁻¹ •
      (lorentzExtension (f.trans g) (1, (u : E))).2 =
    (lorentzExtension g (1, (closedBallPoint f u : F))).1⁻¹ •
      (lorentzExtension g (1, (closedBallPoint f u : F))).2
  rw [h]
  simp [smul_smul, mul_inv_rev, ha]

theorem tendsto_kleinHomeomorph_isometry {α : Type*} {l : Filter α}
    (g : Hyperboloid E ≃ᵢ Hyperboloid F) {x : α → Hyperboloid E}
    {u : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (u : E))) :
    Filter.Tendsto (fun i => (kleinHomeomorph (g (x i)) : F)) l
      (𝓝 (boundaryHomeomorph g u : F)) := by
  let j : Metric.ball (0 : E) 1 → Metric.closedBall (0 : E) 1 :=
    Set.inclusion Metric.ball_subset_closedBall
  let u' : Metric.closedBall (0 : E) 1 := Set.inclusion Metric.sphere_subset_closedBall u
  have hx' : Filter.Tendsto (fun i => j (kleinHomeomorph (x i))) l (𝓝 u') :=
    tendsto_subtype_rng.mpr hx
  have h := (continuous_subtype_val.comp (kleinClosedBallHomeomorph g).continuous).tendsto u'
  have hh := h.comp hx'
  simpa only [Function.comp_def, j, u', kleinClosedBallHomeomorph_apply_kleinHomeomorph,
    kleinClosedBallHomeomorph_apply_sphere] using hh

end DifferentialGeometry.Hyperboloid
