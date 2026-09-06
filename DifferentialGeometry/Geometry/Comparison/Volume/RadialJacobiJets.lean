import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiReparam
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiJets

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential Variation CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]

omit [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] in
theorem radialJacobiField_smul_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (c t : ℝ) :
    radialJacobiField g p (c • x) (c • w) t = radialJacobiField g p x w (c * t) := by
  have h₁ := radialJacobi_scale (I := I) g p (c • x) (c • w) t
  have h₂ := radialJacobi_scale (I := I) g p x w (c * t)
  have hx : t • (c • x) = (c * t) • x := by rw [smul_smul, mul_comm t c]
  have hw : t • (c • w) = (c * t) • w := by rw [smul_smul, mul_comm t c]
  have hmid := congrArg₂ (fun a b : E => (radialJacobiField (I := I) g p a b 1 : E)) hx hw
  exact h₁.trans (hmid.trans h₂.symm)

omit [T2Space (TangentBundle I M)] in
private theorem isJacobiAt_radial_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (c t : ℝ)
    (hJac : IsJacobiAt g (radialCurve g p x) (radialJacobiField g p x w) (c * t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (radialCurve g p x) (c * t)) :
    IsJacobiAt g (radialCurve g p (c • x)) (radialJacobiField g p (c • x) (c • w)) t := by
  have hJac' : IsJacobiAt g (radialCurve g p x) (radialJacobiField g p x w) (c * t + 0) := by
    simpa only [add_zero] using hJac
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) I (radialCurve g p x) (c * t + 0) := by
    simpa only [add_zero] using hγ
  have h := hJac'.comp_affine hγ'
  have hcurve : (fun s => radialCurve g p x (c * s + 0)) = radialCurve g p (c • x) := by
    funext s
    unfold radialCurve
    apply congrArg (fun z : E => expMap (I := I) g p (show TangentSpace I p from z))
    rw [add_zero, smul_smul, mul_comm s c]
  have hfield : (fun s => radialJacobiField g p x w (c * s + 0)) =
      radialJacobiField g p (c • x) (c • w) := by
    funext s
    rw [add_zero]
    exact (radialJacobiField_smul_smul (I := I) g p x w c s).symm
  rw [hcurve, hfield] at h
  exact h

private theorem exists_radialJacobi_symmetric_radius
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ t ∈ Ioo (-1 : ℝ) 1,
      IsJacobiAt g (radialCurve g p x) (radialJacobiField g p x w) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨r₁, hr₁, hpos⟩ := exists_radialJacobi_radius (I := I) g p
  obtain ⟨r₀, hr₀, hzero⟩ := exists_radialJacobi_zero_radius (I := I) g p
  let re := expMapC2Radius (I := I) g p
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  refine ⟨min r₁ (min r₀ re), lt_min hr₁ (lt_min hr₀ hre), ?_⟩
  intro x w hx hw t ht
  have hx₁ : ‖x‖ < r₁ := hx.trans_le (min_le_left _ _)
  have hw₁ : ‖w‖ < r₁ := hw.trans_le (min_le_left _ _)
  have hx₀ : ‖x‖ < r₀ := hx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hw₀ : ‖w‖ < r₀ := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxre : ‖x‖ < re := hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  rcases lt_trichotomy t 0 with hneg | rfl | hpos_t
  · have hxneg : ‖-x‖ < r₁ := by simpa only [norm_neg] using hx₁
    have hwneg : ‖-w‖ < r₁ := by simpa only [norm_neg] using hw₁
    have htime : (-1 : ℝ) * t ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1]
    have hJac := hpos (-x) (-w) hxneg hwneg (-1 * t) htime
    have htAbs : |t| < 1 := abs_lt.mpr ht
    have hnorm : ‖(-1 * t) • (-x)‖ < expMapC2Radius (I := I) g p := by
      calc
        ‖(-1 * t) • (-x)‖ = |t| * ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, norm_neg, neg_one_mul, abs_neg]
        _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg x) htAbs.le
        _ < expMapC2Radius (I := I) g p := hxre
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (radialCurve g p (-x)) (-1 * t) :=
      (radialCurve_contMDiffAt2 (I := I) g p (-x) (-1 * t) hnorm).mdifferentiableAt (by norm_num)
    have h := isJacobiAt_radial_smul (I := I) g p (-x) (-w) (-1) t hJac hγ
    rw [neg_one_smul, neg_neg, neg_one_smul, neg_neg] at h
    exact h
  · exact hzero x w hx₀ hw₀
  · exact hpos x w hx₁ hw₁ t ⟨hpos_t, ht.2⟩

theorem radialJacobiField_eventually_isJacobiAt
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsJacobiAt g (radialCurve g p x) (radialJacobiField g p x w) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨rj, hrj, hJac⟩ := exists_radialJacobi_symmetric_radius (I := I) g p
  let re := expMapC2Radius (I := I) g p
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  let r := min rj re
  have hr : 0 < r := lt_min hrj hre
  obtain ⟨a, ha, hmul⟩ := exists_pos_mul_lt hr (max ‖x‖ ‖w‖)
  have hxsmall : ‖a • x‖ < r := by
    rw [norm_smul_of_nonneg ha.le x, mul_comm]
    exact (mul_le_mul_of_nonneg_right (le_max_left ‖x‖ ‖w‖) ha.le).trans_lt hmul
  have hwsmall : ‖a • w‖ < r := by
    rw [norm_smul_of_nonneg ha.le w, mul_comm]
    exact (mul_le_mul_of_nonneg_right (le_max_right ‖x‖ ‖w‖) ha.le).trans_lt hmul
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha] with t ht
  have htAbs : |t| < a := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have htimeAbs : |a⁻¹ * t| < 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc
      a⁻¹ * |t| < a⁻¹ * a := mul_lt_mul_of_pos_left htAbs (inv_pos.mpr ha)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hJac_t := hJac (a • x) (a • w)
    (hxsmall.trans_le (min_le_left _ _)) (hwsmall.trans_le (min_le_left _ _))
    (a⁻¹ * t) (abs_lt.mp htimeAbs)
  have hnorm : ‖(a⁻¹ * t) • (a • x)‖ < expMapC2Radius (I := I) g p := by
    calc
      ‖(a⁻¹ * t) • (a • x)‖ = |a⁻¹ * t| * ‖a • x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖a • x‖ := mul_le_of_le_one_left (norm_nonneg (a • x)) htimeAbs.le
      _ < r := hxsmall
      _ ≤ expMapC2Radius (I := I) g p := min_le_right _ _
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (radialCurve g p (a • x)) (a⁻¹ * t) :=
    (radialCurve_contMDiffAt2 (I := I) g p (a • x) (a⁻¹ * t) hnorm).mdifferentiableAt (by norm_num)
  have h := isJacobiAt_radial_smul (I := I) g p (a • x) (a • w) a⁻¹ t hJac_t hγ
  have hx : a⁻¹ • (a • x) = x := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have hw : a⁻¹ • (a • w) = w := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [hx, hw] at h
  exact h

omit [T2Space M] in
theorem contMDiffAt_radialJacobiField_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨radialCurve g p x t, radialJacobiField g p x w t⟩ : TangentBundle I M)) 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let F : E → M := fun z => expMap (I := I) g p (show TangentSpace I p from z)
  let b : ℝ → E := fun t => t • x
  have hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ b := contMDiff_id.smul contMDiff_const
  have hF : ContMDiffAt 𝓘(ℝ, E) I ∞ F (b 0) :=
    expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p
      (by simpa only [b, zero_smul, norm_zero] using expMapC2Radius_pos (I := I) g p)
  have hV : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
      (fun t => (⟨b t, t • w⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
    have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun t : ℝ => (b t, t • w)) := hb.prodMk (contMDiff_id.smul contMDiff_const)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, E))).comp hc
  have hD : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun t => ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) E (TangentSpace I)
        (b 0) (b t) (F (b 0)) (F (b t)) (mfderiv 𝓘(ℝ, E) I F (b t))) 0 :=
    (hF.mfderiv_const (by simp)).comp 0 hb.contMDiffAt
  have hJ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (⟨F (b t), mfderiv 𝓘(ℝ, E) I F (b t) (t • w)⟩ : TangentBundle I M)) 0 :=
    ContMDiffAt.clm_apply_of_inCoordinates
      (F₁ := E) (F₂ := E) (E₁ := TangentSpace 𝓘(ℝ, E)) (E₂ := TangentSpace I)
      (b₁ := b) (b₂ := fun t => F (b t))
      (ϕ := fun t => mfderiv 𝓘(ℝ, E) I F (b t)) (v := fun t => t • w)
      hD hV.contMDiffAt (hF.comp 0 hb.contMDiffAt)
  apply hJ.congr_of_eventuallyEq
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) :=
    hb.continuous.continuousAt
      (by simpa only [b, zero_smul] using
        Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
  filter_upwards [hsmall] with t ht
  have hnorm : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    simpa only [b, Metric.mem_ball, dist_zero_right] using ht
  apply congrArg (fun v : TangentSpace I (radialCurve g p x t) =>
    (⟨radialCurve g p x t, v⟩ : TangentBundle I M))
  have h := radialJacobi_at (I := I) g p x w t hnorm
  with_unfolding_all exact h

omit [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] in
theorem covDerivAlong_radialJacobiField_smul_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (c t : ℝ) :
    covDerivAlong g (radialCurve g p (c • x)) (radialJacobiField g p (c • x) (c • w)) t =
      c • covDerivAlong g (radialCurve g p x) (radialJacobiField g p x w) (c * t) := by
  have h := covDeriv_comp_mul (I := I) g (radialCurve g p x) (radialJacobiField g p x w) c t
  have hcurve : (fun s => radialCurve g p x (c * s)) = radialCurve g p (c • x) := by
    funext s
    unfold radialCurve
    apply congrArg (fun z : E => expMap (I := I) g p (show TangentSpace I p from z))
    rw [smul_smul, mul_comm s c]
  have hfield : (fun s => radialJacobiField g p x w (c * s)) =
      radialJacobiField g p (c • x) (c • w) := by
    funext s
    exact (radialJacobiField_smul_smul (I := I) g p x w c s).symm
  rw [hcurve, hfield] at h
  exact h

omit [T2Space M] in
theorem covDerivAlong_radialJacobiField_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    (covDerivAlong g (radialCurve g p x) (radialJacobiField g p x w) 0 : E) = w := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨r, hr, hderiv⟩ := exists_radialJacobi_deriv_radius (I := I) g p
  obtain ⟨a, ha, hmul⟩ := exists_pos_mul_lt hr (max ‖x‖ ‖w‖)
  have hxsmall : ‖a • x‖ < r := by
    rw [norm_smul_of_nonneg ha.le x, mul_comm]
    exact (mul_le_mul_of_nonneg_right (le_max_left ‖x‖ ‖w‖) ha.le).trans_lt hmul
  have hwsmall : ‖a • w‖ < r := by
    rw [norm_smul_of_nonneg ha.le w, mul_comm]
    exact (mul_le_mul_of_nonneg_right (le_max_right ‖x‖ ‖w‖) ha.le).trans_lt hmul
  have h := covDerivAlong_radialJacobiField_smul_smul (I := I) g p (a • x) (a • w) a⁻¹ 0
  have hx : a⁻¹ • (a • x) = x := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have hw : a⁻¹ • (a • w) = w := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [hx, hw, mul_zero] at h
  have hinit : (covDerivAlong g (radialCurve g p (a • x))
      (radialJacobiField g p (a • x) (a • w)) 0 : E) = a • w :=
    hderiv (a • x) (a • w) hxsmall hwsmall
  exact h.trans ((congrArg (fun v : E => a⁻¹ • v) hinit).trans hw)

theorem radialJacobiField_second_covariant_derivative_eq_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    covDerivAlong g (radialCurve g p x)
      (fun t => covDerivAlong g (radialCurve g p x) (radialJacobiField g p x w) t) 0 = 0 :=
  jacobi_second_covariant_derivative_eq_zero g (radialCurve g p x) (radialJacobiField g p x w)
    (radialJacobiField_eventually_isJacobiAt g p x w).self_of_nhds (radialJacobi_zero g p x w)

theorem radialJacobiField_third_covariant_derivative
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    covDerivAlong g (radialCurve g p x)
      (fun t => covDerivAlong g (radialCurve g p x)
        (fun s => covDerivAlong g (radialCurve g p x) (radialJacobiField g p x w) s) t) 0 =
      -DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita g) p w x x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (radialCurve g p x) 0 :=
    radialCurve_contMDiffAt2 (I := I) g p x 0
      (by simpa only [zero_smul, norm_zero] using expMapC2Radius_pos (I := I) g p)
  have h := jacobi_third_covariant_derivative_of_eq_zero g (radialCurve g p x)
    (radialJacobiField g p x w) hγ
    ((contMDiffAt_radialJacobiField_zero g p x w).mdifferentiableAt (by simp))
    (radialJacobiField_eventually_isJacobiAt g p x w) (radialJacobi_zero g p x w)
  have hv : curveVelocity (radialCurve g p x) 0 = (x : E) :=
    radialCurve_launch_velocity (I := I) g p x
  rw [covDerivAlong_radialJacobiField_zero, hv, radialCurve_zero] at h
  exact h

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
